module
public import PurescriptLanguageCstParser.Types
import NonEmpty.CorrectByConstruction.Array

open NonEmpty.CorrectByConstruction.Array
open PurescriptLanguageCstParser.Types
@[expose] public section

namespace PurescriptLanguageCstParser.Traversal

--------------------------------------------------------------------
-- Rewrite type aliases (matching Purescript)
--------------------------------------------------------------------

abbrev Rewrite (e : Type) (f g : Type → Type) :=
  g e → f (g e)

abbrev RewriteWithContext (c e : Type) (f g : Type → Type) :=
  c → g e → f (c × g e)

abbrev MonoidalRewrite (e m : Type) (g : Type → Type) :=
  g e → m

abbrev PureRewrite (e : Type) (g : Type → Type) :=
  g e → g e

abbrev PureRewriteWithContext (c e : Type) (g : Type → Type) :=
  c → g e → c × g e

--------------------------------------------------------------------
-- Visitor record
--------------------------------------------------------------------

structure Visitor (e : Type) (m : Type → Type) where
  onBinder : Binder e → m (Binder e)
  onExpr   : Expr e   → m (Expr e)
  onType   : Type_ e  → m (Type_ e)
  onDecl   : Declaration e → m (Declaration e)

def defaultVisitorM [Applicative m] : Visitor e m :=
  { onBinder := pure, onExpr := pure, onType := pure, onDecl := pure }

def defaultVisitor : Visitor e Id :=
  { onBinder := pure, onExpr := pure, onType := pure, onDecl := pure }

--------------------------------------------------------------------
-- Type traversal
--------------------------------------------------------------------

section TypeTraversal
variable {e : Type} {m : Type → Type} [Monad m]

def traverseType (k : Visitor e m) : Type_ e → m (Type_ e)
  | .Var n                 => pure (.Var n)
  | .Constructor n         => pure (.Constructor n)
  | .Wildcard t            => pure (.Wildcard t)
  | .Hole n                => pure (.Hole n)
  | .String t v    => pure (.String t v)
  | .Int p t v             => pure (.Int p t v)
  | .Row w                 => .Row    <$> w.mapM (fun r => r.mapM k.onType)
  | .Record w              => .Record <$> w.mapM (fun r => r.mapM k.onType)
  | .Forall o bs c body    => .Forall o <$> bs.mapM (fun b => b.mapM k.onType) <*> pure c <*> k.onType body
  | .Kinded t1 sep t2      => .Kinded <$> k.onType t1 <*> pure sep <*> k.onType t2
  | .App t args            => .App    <$> k.onType t  <*> args.mapM k.onType
  | .Op t ops              => .Op     <$> k.onType t  <*> ops.mapM (fun (op, t2) => (op, ·) <$> k.onType t2)
  | .OpName n              => pure (.OpName n)
  | .Arrow t1 tok t2       => .Arrow  <$> k.onType t1 <*> pure tok <*> k.onType t2
  | .ArrowName t           => pure (.ArrowName t)
  | .Constrained t1 tok t2 => .Constrained <$> k.onType t1 <*> pure tok <*> k.onType t2
  | .Parens w              => .Parens <$> w.mapM k.onType
  | .Error err             => pure (.Error err)

end TypeTraversal

--------------------------------------------------------------------
-- Binder traversal
--------------------------------------------------------------------

section BinderTraversal
variable {e : Type} {m : Type → Type} [Monad m]

def traverseBinder (k : Visitor e m) : Binder e → m (Binder e)
  | .Wildcard t         => pure (.Wildcard t)
  | .Var n              => pure (.Var n)
  | .Named n tok b      => .Named n tok <$> k.onBinder b
  | .Constructor n bs   => .Constructor n <$> bs.attach.mapM (fun ⟨b, _h_mem⟩ => k.onBinder b)
  | .Boolean t v        => pure (.Boolean t v)
  | .Char t v           => pure (.Char t v)
  | .String t v => pure (.String t v)
  | .Int p t v          => pure (.Int p t v)
  | .Number p t v       => pure (.Number p t v)
  | .Array items        => .Array  <$> items.mapM k.onBinder
  | .Record fields      => .Record <$> fields.mapM (fun rl => rl.mapM k.onBinder)
  | .Parens w           => .Parens <$> w.mapM k.onBinder
  | .Typed b tok t      => .Typed  <$> k.onBinder b <*> pure tok <*> k.onType t
  | .Op first ops       => .Op     <$> k.onBinder first <*> ops.attach.mapM (fun ⟨(op, b), _h_mem⟩ => (op, ·) <$> k.onBinder b)
  | .Error err          => pure (.Error err)

end BinderTraversal

--------------------------------------------------------------------
-- Mutually recursive: Expr / LetBinding / Where / Guarded / VBF
--------------------------------------------------------------------

section ExprTraversal
variable {e : Type} {m : Type → Type} [Monad m]

mutual

  def traverseExpr (k : Visitor e m) : Expr e → m (Expr e)
    | .Hole n => pure (.Hole n)
    | .Section t => pure (.Section t)
    | .Ident n => pure (.Ident n)
    | .Constructor n => pure (.Constructor n)
    | .Boolean t v => pure (.Boolean t v)
    | .Char t v => pure (.Char t v)
    | .String t v => pure (.String t v)
    | .Int t v => pure (.Int t v)
    | .Number t v => pure (.Number t v)
    | .Array items => .Array <$> items.mapM k.onExpr
    | .Record fields => .Record <$> fields.mapM (fun rl => rl.mapM k.onExpr)
    | .Parens w => .Parens <$> w.mapM k.onExpr
    | .Typed ex tok t => .Typed <$> k.onExpr ex <*> pure tok <*> k.onType t
    | .Infix head tail => .Infix <$> k.onExpr head <*> tail.attach.mapM (fun ⟨(w, ex), _h_mem⟩ => (·, ·) <$> w.mapM k.onExpr <*> k.onExpr ex)
    | .Op head ops => .Op <$> k.onExpr head <*> ops.attach.mapM (fun ⟨(op, ex), _h_mem⟩ => (op, ·) <$> k.onExpr ex)
    | .OpName n => pure (.OpName n)
    | .Negate tok ex => .Negate tok <$> k.onExpr ex
    | .RecordAccessor ra => .RecordAccessor <$> traverseRecordAccessor k ra
    | .RecordUpdate ex upds => .RecordUpdate <$> k.onExpr ex <*> upds.attach.mapM (fun ⟨ru, _h_mem⟩ => traverseRecordUpdate k ru)
    | .App fn args => .App <$> k.onExpr fn <*> args.attach.mapM (fun ⟨arg, _h_mem⟩ => traverseAppSpine k arg)
    | .Lambda l => .Lambda <$> traverseLambda k l
    | .If i => .If <$> traverseIfThenElse k i
    | .Case c => .Case <$> traverseCaseOf k c
    | .Let l => .Let <$> traverseLetIn k l
    | .Do db => .Do <$> traverseDoBlock k db
    | .Ado ab => .Ado <$> traverseAdoBlock k ab
    | .Error err => pure (.Error err)

  def traverseRecordAccessor (k : Visitor e m) (ra : RecordAccessorRecursive e) : m (RecordAccessorRecursive e) :=
    (fun expr => { ra with expr }) <$> k.onExpr ra.expr

  def traverseRecordUpdate (k : Visitor e m) (ru : RecordUpdateRecursive e) : m (RecordUpdateRecursive e) :=
    match ru with
    | .Leaf l tok ex => .Leaf l tok <$> k.onExpr ex
    | .Branch l upds => .Branch l <$> upds.attach.mapM (fun ⟨u, _h_mem⟩ => traverseRecordUpdate k u)
  termination_by sizeOf ru
  decreasing_by
    all_goals simp_wf
    have h := DelimitedNonEmpty.sizeOf_attach_elem upds ⟨u, _h_mem⟩
    dsimp only at h
    omega

  def traverseAppSpine (k : Visitor e m) (s : AppSpineRecursive e) : m (AppSpineRecursive e) :=
    match s with
    | .Type_ tok t => .Type_ tok <$> k.onType t
    | .Term ex     => .Term      <$> k.onExpr ex

  def traverseLambda (k : Visitor e m) (l : LambdaRecursive e) : m (LambdaRecursive e) :=
    (fun binders body => { l with binders, body })
      <$> l.binders.mapM k.onBinder
      <*> k.onExpr l.body

  def traverseIfThenElse (k : Visitor e m) (i : IfThenElseRecursive e) : m (IfThenElseRecursive e) :=
    (fun cond true_ false_ => { i with cond, true_, false_ })
      <$> k.onExpr i.cond
      <*> k.onExpr i.true_
      <*> k.onExpr i.false_

  def traverseCaseOf (k : Visitor e m) (c : CaseOfRecursive e) : m (CaseOfRecursive e) :=
    (fun head branches => { c with head, branches })
      <$> c.head.mapM k.onExpr
      <*> c.branches.attach.mapM (fun ⟨(binders, guarded), _h_mem⟩ =>
            (·, ·) <$> binders.mapM k.onBinder
                   <*> traverseGuarded k guarded)

  def traverseLetIn (k : Visitor e m) (l : LetInRecursive e) : m (LetInRecursive e) :=
    (fun bindings body => { l with bindings, body })
      <$> l.bindings.attach.mapM (fun ⟨lb, _h_mem⟩ => traverseLetBinding k lb)
      <*> k.onExpr l.body

  def traverseLetBinding (k : Visitor e m) (lb : LetBindingRecursive e) : m (LetBindingRecursive e) :=
    match lb with
    | .Signature sig   => .Signature <$> sig.mapM_value k.onType
    | .Name fields     => .Name      <$> traverseValueBindingFields k fields
    | .Pattern b tok w => .Pattern   <$> k.onBinder b <*> pure tok <*> traverseWhere k w
    | .Error err       => pure (.Error err)
  termination_by sizeOf lb
  decreasing_by
    all_goals simp_wf
    all_goals try simp_all
    all_goals try decreasing_trivial

  def traverseWhere (k : Visitor e m) (w : WhereRecursive e) : m (WhereRecursive e) :=
    match w with
    | { expr := expr, bindings := none } => do
        let expr' ← k.onExpr expr
        pure { expr := expr', bindings := none }
    | { expr := expr, bindings := some (tok, lbs) } => do
        let expr' ← k.onExpr expr
        let lbs' ← lbs.attach.mapM (fun ⟨lb, _h_mem⟩ => traverseLetBinding k lb)
        pure { expr := expr', bindings := some (tok, lbs') }
  termination_by sizeOf w
  decreasing_by
    all_goals simp_wf
    have h := NonEmptyArray.sizeOf_lt_of_mem _h_mem
    omega



  def traverseGuarded (k : Visitor e m) (g : GuardedRecursive e) : m (GuardedRecursive e) :=
    match g with
    | .Unconditional tok w => .Unconditional tok <$> traverseWhere k w
    | .Guarded branches    => .Guarded <$> branches.attach.mapM (fun ⟨ge, _h_mem⟩ => traverseGuardedExpr k ge)
  termination_by sizeOf g
  decreasing_by
    all_goals simp_wf
    · omega
    · have := NonEmptyArray.sizeOf_lt_of_mem _h_mem; omega

  def traverseGuardedExpr (k : Visitor e m) (ge : GuardedExprRecursive e) : m (GuardedExprRecursive e) :=
    (fun patterns where_ => { ge with patterns, where_ })
      <$> ge.patterns.mapM (traversePatternGuard k)
      <*> traverseWhere k ge.where_
  termination_by sizeOf ge
  decreasing_by
    all_goals simp_wf

  def traversePatternGuard (k : Visitor e m) (pg : PatternGuardRecursive e) : m (PatternGuardRecursive e) :=
    (fun binder expr => { pg with binder, expr })
      <$> pg.binder.mapM (fun (b, tok) => (·, tok) <$> k.onBinder b)
      <*> k.onExpr pg.expr

  def traverseValueBindingFields (k : Visitor e m) (vbf : ValueBindingFieldsRecursive e) : m (ValueBindingFieldsRecursive e) :=
    (fun binders guarded => { vbf with binders, guarded })
      <$> vbf.binders.mapM k.onBinder
      <*> traverseGuarded k vbf.guarded
  termination_by sizeOf vbf
  decreasing_by
    all_goals simp_wf

  def traverseDoStatement (k : Visitor e m) (s : DoStatementRecursive e) : m (DoStatementRecursive e) :=
    match s with
    | .Let tok lbs   => .Let tok <$> lbs.attach.mapM (fun ⟨lb, _h_mem⟩ => traverseLetBinding k lb)
    | .Discard ex    => .Discard <$> k.onExpr ex
    | .Bind b tok ex => .Bind    <$> k.onBinder b <*> pure tok <*> k.onExpr ex
    | .Error err     => pure (.Error err)

  def traverseDoBlock (k : Visitor e m) (db : DoBlockRecursive e) : m (DoBlockRecursive e) :=
    (fun statements => { db with statements })
      <$> db.statements.attach.mapM (fun ⟨s, _h_mem⟩ => traverseDoStatement k s)

  def traverseAdoBlock (k : Visitor e m) (ab : AdoBlockRecursive e) : m (AdoBlockRecursive e) :=
    (fun statements result => { ab with statements, result })
      <$> ab.statements.attach.mapM (fun ⟨s, _h_mem⟩ => traverseDoStatement k s)
      <*> k.onExpr ab.result
end

end ExprTraversal

--------------------------------------------------------------------
-- Declaration / module traversal
--------------------------------------------------------------------

section DeclTraversal
variable {e : Type} {m : Type → Type} [Monad m]

def traverseInstanceHead (k : Visitor e m) (ih : InstanceHead e) : m (InstanceHead e) :=
  (fun constraints types => { ih with constraints, types })
    <$> ih.constraints.mapM (fun (c, tok) => (·, tok) <$> c.mapM k.onType)
    <*> ih.types.mapM k.onType

def traverseInstanceBinding (k : Visitor e m) : InstanceBinding e → m (InstanceBinding e)
  | .Signature sig  => .Signature <$> sig.mapM_value k.onType
  | .Name fields    => .Name      <$> traverseValueBindingFields k fields

def traverseInstance (k : Visitor e m) (inst : Instance e) : m (Instance e) :=
  (fun head body => { inst with head, body })
    <$> traverseInstanceHead k inst.head
    <*> inst.body.mapM (fun (tok, lbs) =>
          (tok, ·) <$> lbs.mapM (traverseInstanceBinding k))

def traverseClassHead (k : Visitor e m) (ch : ClassHead e) : m (ClassHead e) :=
  (fun typeConstraint parameters => { ch with typeConstraint, parameters })
    <$> ch.typeConstraint.mapM (fun (c, tok) =>
          (·, tok) <$> c.mapM k.onType)
    <*> ch.parameters.mapM (fun b => b.mapM k.onType)

def traverseDataHead (k : Visitor e m) (dh : DataHead e) : m (DataHead e) :=
  (fun parameters => { dh with parameters })
    <$> dh.parameters.mapM (fun b => b.mapM k.onType)

def traverseDataCtor (k : Visitor e m) (dc : DataCtor e) : m (DataCtor e) :=
  (fun parameters => { dc with parameters })
    <$> dc.parameters.mapM k.onType

def traverseForeign (k : Visitor e m) : Foreign e → m (Foreign e)
  | .Value l       => .Value <$> l.mapM_value k.onType
  | .Data tok l    => .Data tok <$> l.mapM_value k.onType
  | .Kind tok n    => pure (.Kind tok n)

def traverseDecl (k : Visitor e m) : Declaration e → m (Declaration e)
  | .Data dh ctors =>
      .Data <$> traverseDataHead k dh
            <*> ctors.mapM (fun (tok, sep) =>
                  (tok, ·) <$> sep.mapM (traverseDataCtor k))
  | .Type_ dh tok t =>
      .Type_ <$> traverseDataHead k dh <*> pure tok <*> k.onType t
  | .Newtype dh tok n t =>
      .Newtype <$> traverseDataHead k dh <*> pure tok <*> pure n <*> k.onType t
  | .Class ch sigs =>
      .Class <$> traverseClassHead k ch
             <*> sigs.mapM (fun (tok, ls) =>
                   (tok, ·) <$> ls.mapM (fun l => l.mapM_value k.onType))
  | .InstanceChain sep =>
      .InstanceChain <$> sep.mapM (traverseInstance k)
  | .Derive tok mbTok ih =>
      .Derive tok mbTok <$> traverseInstanceHead k ih
  | .KindSignature tok l =>
      .KindSignature tok <$> l.mapM_value k.onType
  | .Signature l =>
      .Signature <$> l.mapM_value k.onType
  | .Value fields =>
      .Value <$> traverseValueBindingFields k fields
  | .Foreign tok1 tok2 f =>
      .Foreign tok1 tok2 <$> traverseForeign k f
  | decl => pure decl

def traverseModuleBody (k : Visitor e m) (mb : ModuleBody e) : m (ModuleBody e) :=
  (fun decls => { mb with decls })
    <$> mb.decls.mapM (traverseDecl k)

def traverseModule (k : Visitor e m) (m_ : Module e) : m (Module e) :=
  (fun body => { m_ with body })
    <$> traverseModuleBody k m_.body

end DeclTraversal

--------------------------------------------------------------------
-- Bottom-up and top-down combinators
--------------------------------------------------------------------

section Combinators
variable {e : Type} {m : Type → Type} [Monad m]

partial def bottomUpTraversal (v : Visitor e m) : Visitor e m :=
  { onBinder := fun a => v.onBinder =<< traverseBinder v' a
  , onExpr   := fun a => v.onExpr   =<< traverseExpr   v' a
  , onType   := fun a => v.onType   =<< traverseType   v' a
  , onDecl   := fun a => v.onDecl   =<< traverseDecl   v' a }
  where v' := bottomUpTraversal v

partial def topDownTraversal (v : Visitor e m) : Visitor e m :=
  { onBinder := fun a => v.onBinder a >>= traverseBinder v'
  , onExpr   := fun a => v.onExpr   a >>= traverseExpr   v'
  , onType   := fun a => v.onType   a >>= traverseType   v'
  , onDecl   := fun a => v.onDecl   a >>= traverseDecl   v' }
  where v' := topDownTraversal v

-- Concrete rewriters
def rewriteExprBottomUpM  (v : Visitor e m) : Expr e → m (Expr e) :=
  (bottomUpTraversal v).onExpr

def rewriteExprTopDownM   (v : Visitor e m) : Expr e → m (Expr e) :=
  (topDownTraversal v).onExpr

def rewriteDeclBottomUpM  (v : Visitor e m) : Declaration e → m (Declaration e) :=
  (bottomUpTraversal v).onDecl

def rewriteDeclTopDownM   (v : Visitor e m) : Declaration e → m (Declaration e) :=
  (topDownTraversal v).onDecl

def rewriteModuleBottomUpM (v : Visitor e m) : Module e → m (Module e) :=
  traverseModule (bottomUpTraversal v)

def rewriteModuleTopDownM  (v : Visitor e m) : Module e → m (Module e) :=
  traverseModule (topDownTraversal v)

-- Pure (Identity monad) variants
def rewriteExprBottomUp  (v : Visitor e Id) : Expr e → Expr e :=
  rewriteExprBottomUpM v

def rewriteExprTopDown   (v : Visitor e Id) : Expr e → Expr e :=
  rewriteExprTopDownM v

def rewriteModuleBottomUp (v : Visitor e Id) : Module e → Module e :=
  rewriteModuleBottomUpM v

def rewriteModuleTopDown  (v : Visitor e Id) : Module e → Module e :=
  rewriteModuleTopDownM v

-- Monoidal fold
-- Emulates Haskell's `Const r` fold by accumulating state through `StateM r Unit`.
def foldMapExpr {r : Type} [Add r] [OfNat r 0] (v : Visitor e (StateM r)) : Expr e → r :=
  fun ex => ((rewriteExprTopDownM v ex).run 0).snd

def foldMapModule {r : Type} [Add r] [OfNat r 0] (v : Visitor e (StateM r)) : Module e → r :=
  fun mod => ((rewriteModuleTopDownM v mod).run 0).snd

end Combinators

end PurescriptLanguageCstParser.Traversal
