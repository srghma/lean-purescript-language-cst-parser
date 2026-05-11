module

public import PurescriptLanguageCstParser.Types.PType.Basic
public import PurescriptLanguageCstParser.Types.Module
public import PurescriptLanguageCstParser.Errors
public import PurescriptLanguageCstParser.Range.TokenList
public import NonEmpty.ArrayCorrectByConstruction

namespace PurescriptLanguageCstParser.Range

open PurescriptLanguageCstParser.Types
open PurescriptLanguageCstParser.Range.TokenList
open NonEmpty.ArrayCorrectByConstruction
open PurescriptLanguageCstParser.Errors

class RangeOf (α : Type) where
  rangeOf (a : α) : SourceRange

-- ── Generic Instances (Aligned with PureScript) ─────────────────────────────

instance : RangeOf SourceToken where
  rangeOf t := t.range

instance : RangeOf Empty where
  rangeOf v := nomatch v

instance : RangeOf RecoveredError where
  rangeOf err :=
    let tokens := err.tokens
    match tokens[0]?, tokens.back? with
    | some first, some last =>
        { start := first.range.start, end_ := last.range.end_ }
    | _, _ =>
        { start := err.position, end_ := err.position }

instance : RangeOf (Name a) where
  rangeOf n := n.token.range

instance : RangeOf (QualifiedName a) where
  rangeOf n := n.token.range

instance : RangeOf (Wrapped a) where
  rangeOf w := { start := w.open_.range.start, end_ := w.close.range.end_ }

def rangeOf_Separated_Helper (f : α → SourceRange) (s : Separated α) : SourceRange :=
  match s.tail.back? with
  | some (_, last) => { start := (f s.head).start, end_ := (f last).end_ }
  | none => f s.head

instance [RangeOf a] : RangeOf (Separated a) where
  rangeOf s := rangeOf_Separated_Helper RangeOf.rangeOf s

instance [RangeOf a] [RangeOf b] : RangeOf (Labeled a b) where
  rangeOf l := { start := (RangeOf.rangeOf l.label).start, end_ := (RangeOf.rangeOf l.value).end_ }

instance [RangeOf a] : RangeOf (Prefixed a) where
  rangeOf p :=
    match p.prefix_ with
    | some tok => { start := tok.range.start, end_ := (RangeOf.rangeOf p.value).end_ }
    | none => RangeOf.rangeOf p.value

-- Note: Delimited is just a wrapper around Wrapped, which doesn't need RangeOf a.
instance : RangeOf (Delimited a) where
  rangeOf | .mk w => { start := w.open_.range.start, end_ := w.close.range.end_ }

instance : RangeOf (DelimitedNonEmpty a) where
  rangeOf | .mk w => { start := w.open_.range.start, end_ := w.close.range.end_ }

instance [RangeOf a] : RangeOf (OneOrDelimited a) where
  rangeOf o := match o with
    | .One a => RangeOf.rangeOf a
    | .Many as => RangeOf.rangeOf as

-- ── CST Specific Instances ──────────────────────────────────────────────────

instance : RangeOf DataMembers where
  rangeOf dm := match dm with
    | .All tok => tok.range
    | .Enumerated w => RangeOf.rangeOf w

instance : RangeOf ClassFundep where
  rangeOf cf := match cf with
    | .Determined tok ns =>
        let last_range := (ns.tail.back?.map RangeOf.rangeOf).getD (RangeOf.rangeOf ns.head)
        { start := tok.range.start, end_ := last_range.end_ }
    | .Determines ns1 _ ns2 =>
        let first_range := RangeOf.rangeOf ns1.head
        let last_range := (ns2.tail.back?.map RangeOf.rangeOf).getD (RangeOf.rangeOf ns2.head)
        { start := first_range.start, end_ := last_range.end_ }

instance : RangeOf FixityOp where
  rangeOf fo := match fo with
    | .Value n1 _ n2 => { start := (RangeOf.rangeOf n1).start, end_ := (RangeOf.rangeOf n2).end_ }
    | .Type_ tok1 _ _ n2 => { start := tok1.range.start, end_ := (RangeOf.rangeOf n2).end_ }

instance : RangeOf FixityFields where
  rangeOf fields := { start := fields.keyword.1.range.start, end_ := (RangeOf.rangeOf fields.operator).end_ }

-- ── Recursive CST Implementation ────────────────────────────────────────────

variable [RangeOf e]

mutual
  partial def rangeOf_Type_ (t : Type_ e) : SourceRange := match t with
    | .Var n => RangeOf.rangeOf n
    | .Constructor n => RangeOf.rangeOf n
    | .Wildcard tok => tok.range
    | .Hole n => RangeOf.rangeOf n
    | .String tok _ => tok.range
    | .Int pref tok _ =>
      match pref with
      | none => tok.range
      | some n => { start := n.range.start, end_ := tok.range.end_ }
    | .Row w => RangeOf.rangeOf w
    | .Record w => RangeOf.rangeOf w
    | .Forall tok _ _ ty => { start := tok.range.start, end_ := (rangeOf_Type_ ty).end_ }
    | .Kinded ty1 _ ty2 => { start := (rangeOf_Type_ ty1).start, end_ := (rangeOf_Type_ ty2).end_ }
    | .App ty tys =>
        let last_ty := tys.tail.back?.getD tys.head
        { start := (rangeOf_Type_ ty).start, end_ := (rangeOf_Type_ last_ty).end_ }
    | .Op ty ops =>
        let last_op_ty := (ops.tail.back?.getD ops.head).2
        { start := (rangeOf_Type_ ty).start, end_ := (rangeOf_Type_ last_op_ty).end_ }
    | .OpName n => RangeOf.rangeOf n
    | .Arrow ty1 _ ty2 => { start := (rangeOf_Type_ ty1).start, end_ := (rangeOf_Type_ ty2).end_ }
    | .ArrowName tok => tok.range
    | .Constrained ty1 _ ty2 => { start := (rangeOf_Type_ ty1).start, end_ := (rangeOf_Type_ ty2).end_ }
    | .Parens w => RangeOf.rangeOf w
    | .Error e_inner => RangeOf.rangeOf e_inner

  partial def rangeOf_Export (ex : Export e) : SourceRange := match ex with
    | .Value n => RangeOf.rangeOf n
    | .Op n => RangeOf.rangeOf n
    | .Type_ n dms =>
      match dms with
      | some dms' => { start := (RangeOf.rangeOf n).start, end_ := (RangeOf.rangeOf dms').end_ }
      | none => RangeOf.rangeOf n
    | .TypeOp tok n => { start := tok.range.start, end_ := (RangeOf.rangeOf n).end_ }
    | .Class tok n => { start := tok.range.start, end_ := (RangeOf.rangeOf n).end_ }
    | .Module tok n => { start := tok.range.start, end_ := (RangeOf.rangeOf n).end_ }
    | .Error err => RangeOf.rangeOf err

  partial def rangeOf_Import (im : Import e) : SourceRange := match im with
    | .Value n => RangeOf.rangeOf n
    | .Op n => RangeOf.rangeOf n
    | .Type_ n dms =>
      match dms with
      | some dms' => { start := (RangeOf.rangeOf n).start, end_ := (RangeOf.rangeOf dms').end_ }
      | none => RangeOf.rangeOf n
    | .TypeOp tok n => { start := tok.range.start, end_ := (RangeOf.rangeOf n).end_ }
    | .Class tok n => { start := tok.range.start, end_ := (RangeOf.rangeOf n).end_ }
    | .Error err => RangeOf.rangeOf err

  partial def rangeOf_ImportDecl (id : ImportDecl e) : SourceRange :=
    let end_pos := match id.qualified with
      | some (_, mn) => (RangeOf.rangeOf mn).end_
      | none => match id.importList with
        | some (_, imports) => (RangeOf.rangeOf imports).end_
        | none => (RangeOf.rangeOf id.module_).end_
    { start := id.keyword.range.start, end_ := end_pos }

  partial def rangeOf_ModuleHeader (m : ModuleHeader e) : SourceRange :=
    let end_pos := match m.imports.back? with
      | some imp => (rangeOf_ImportDecl imp).end_
      | none => m.where_.range.end_
    { start := m.keyword.range.start, end_ := end_pos }

  partial def rangeOf_DataCtor (dc : DataCtor e) : SourceRange :=
    let end_pos := match dc.parameters.back? with
      | some p => (rangeOf_Type_ p).end_
      | none => (RangeOf.rangeOf dc.name).end_
    { start := (RangeOf.rangeOf dc.name).start, end_ := end_pos }

  partial def rangeOf_Declaration (decl : Declaration e) : SourceRange := match decl with
    | .Data head optionSeparator =>
      let end_pos := match optionSeparator with
        | some (_, cs) => (rangeOf_Separated_Helper rangeOf_DataCtor cs).end_
        | none => (rangeOf_DataHead_End head)
      { start := head.keyword.range.start, end_ := end_pos }
    | .Type_ head _ ty => { start := head.keyword.range.start, end_ := (rangeOf_Type_ ty).end_ }
    | .Newtype head _ _ ty => { start := head.keyword.range.start, end_ := (rangeOf_Type_ ty).end_ }
    | .Class head optionSeparator =>
      let end_pos := match optionSeparator with
        | some (_, ls) => (rangeOf_Type_ (ls.tail.back?.getD ls.head).value).end_
        | none => (rangeOf_ClassHead_End head)
      { start := head.keyword.range.start, end_ := end_pos }
    | .InstanceChain insts => (rangeOf_Separated_Helper rangeOf_Instance insts)
    | .Derive keyword _ head => { start := keyword.range.start, end_ := (rangeOf_InstanceHead_End head) }
    | .KindSignature keyword lbl => { start := keyword.range.start, end_ := (rangeOf_Type_ lbl.value).end_ }
    | .Signature lbl => { start := (RangeOf.rangeOf lbl.label).start, end_ := (rangeOf_Type_ lbl.value).end_ }
    | .Value fields => rangeOf_ValueBindingFieldsRecursive fields
    | .Fixity fields => RangeOf.rangeOf fields
    | .Foreign keyword _ frn => { start := keyword.range.start, end_ := (rangeOf_Foreign frn).end_ }
    | .Role keyword _ _ roles =>
      let last_range := (roles.tail.back?.map (·.1.range)).getD roles.head.1.range
      { start := keyword.range.start, end_ := last_range.end_ }
    | .Error e_inner => RangeOf.rangeOf e_inner

  partial def rangeOf_ValueBindingFieldsRecursive (fields : ValueBindingFieldsRecursive e) : SourceRange :=
    { start := (RangeOf.rangeOf fields.name).start, end_ := (rangeOf_GuardedRecursive fields.guarded).end_ }

  partial def rangeOf_DataHead_End (h_val : DataHead e) : SourcePos :=
    match h_val.parameters.back? with
    | some (p : TypeVarBinding (Name Ident) (Type_ e)) =>
        match p with
        | .Kinded w => w.close.range.end_
        | .Name n => (RangeOf.rangeOf n).end_
    | none =>
        (RangeOf.rangeOf h_val.name).end_

  partial def rangeOf_ClassHead_End (h_val : ClassHead e) : SourcePos :=
    match h_val.fundependencies with
    | some (_, s) => (RangeOf.rangeOf s).end_
    | none =>
        match h_val.parameters.back? with
        | some (p : TypeVarBinding (Name Ident) (Type_ e)) =>
            match p with
            | .Kinded w => w.close.range.end_
            | .Name n => (RangeOf.rangeOf n).end_
        | none =>
            (RangeOf.rangeOf h_val.name).end_

  partial def rangeOf_InstanceHead_End (h_val : InstanceHead e) : SourcePos :=
    match h_val.types.back? with
    | some ty => (rangeOf_Type_ ty).end_
    | none => (RangeOf.rangeOf h_val.className).end_

  partial def rangeOf_Instance (inst : Instance e) : SourceRange :=
    let end_pos := match inst.body with
      | some (_, bs) => (rangeOf_InstanceBinding (bs.tail.back?.getD bs.head)).end_
      | none => (rangeOf_InstanceHead_End inst.head)
    { start := inst.head.keyword.range.start, end_ := end_pos }

  partial def rangeOf_InstanceBinding (ib : InstanceBinding e) : SourceRange := match ib with
    | .Signature lbl => { start := (RangeOf.rangeOf lbl.label).start, end_ := (rangeOf_Type_ lbl.value).end_ }
    | .Name fields => rangeOf_ValueBindingFieldsRecursive fields

  partial def rangeOf_GuardedRecursive (g : GuardedRecursive e) : SourceRange := match g with
    | .Unconditional tok wh => { start := tok.range.start, end_ := (rangeOf_WhereRecursive wh).end_ }
    | .Guarded gs => { start := (rangeOf_GuardedExprRecursive gs.head).start, end_ := (rangeOf_GuardedExprRecursive (gs.tail.back?.getD gs.head)).end_ }

  partial def rangeOf_GuardedExprRecursive (ge : GuardedExprRecursive e) : SourceRange :=
    { start := ge.bar.range.start, end_ := (rangeOf_WhereRecursive ge.where_).end_ }

  partial def rangeOf_PatternGuardRecursive (pg : PatternGuardRecursive e) : SourceRange :=
    let start_pos := match pg.binder with | some (b, _) => (rangeOf_Binder b).start | none => (rangeOf_Expr pg.expr).start
    { start := start_pos, end_ := (rangeOf_Expr pg.expr).end_ }

  partial def rangeOf_Foreign (f : Foreign e) : SourceRange := match f with
    | .Value lbl => { start := (RangeOf.rangeOf lbl.label).start, end_ := (rangeOf_Type_ lbl.value).end_ }
    | .Data tok lbl => { start := tok.range.start, end_ := (rangeOf_Type_ lbl.value).end_ }
    | .Kind tok n => { start := tok.range.start, end_ := (RangeOf.rangeOf n).end_ }

  partial def rangeOf_Expr (expr : Expr e) : SourceRange := match expr with
    | .Hole n => RangeOf.rangeOf n
    | .Section tok => tok.range
    | .Ident n => RangeOf.rangeOf n
    | .Constructor n => RangeOf.rangeOf n
    | .Boolean tok _ => tok.range
    | .Char tok _ => tok.range
    | .String tok _ => tok.range
    | .Int tok _ => tok.range
    | .Number tok _ => tok.range
    | .Array exprs => RangeOf.rangeOf exprs
    | .Record exprs => RangeOf.rangeOf exprs
    | .Parens w => RangeOf.rangeOf w
    | .Typed e_inner _ ty => { start := (rangeOf_Expr e_inner).start, end_ := (rangeOf_Type_ ty).end_ }
    | .Infix e_inner ops => { start := (rangeOf_Expr e_inner).start, end_ := (rangeOf_Expr (ops.tail.back?.getD ops.head).2).end_ }
    | .Op e_inner ops => { start := (rangeOf_Expr e_inner).start, end_ := (rangeOf_Expr (ops.tail.back?.getD ops.head).2).end_ }
    | .OpName n => RangeOf.rangeOf n
    | .Negate tok e_inner => { start := tok.range.start, end_ := (rangeOf_Expr e_inner).end_ }
    | .RecordAccessor rec => { start := (rangeOf_Expr rec.expr).start, end_ := (RangeOf.rangeOf rec.path).end_ }
    | .RecordUpdate e_inner upds => { start := (rangeOf_Expr e_inner).start, end_ := (RangeOf.rangeOf upds).end_ }
    | .App fn args => { start := (rangeOf_Expr fn).start, end_ := (rangeOf_AppSpineRecursive (args.tail.back?.getD args.head)).end_ }
    | .Lambda rec => { start := rec.symbol.range.start, end_ := (rangeOf_Expr rec.body).end_ }
    | .If rec => { start := rec.keyword.range.start, end_ := (rangeOf_Expr rec.false_).end_ }
    | .Case rec => { start := rec.keyword.range.start, end_ := (rangeOf_GuardedRecursive (rec.branches.tail.back?.getD rec.branches.head).2).end_ }
    | .Let rec => { start := rec.keyword.range.start, end_ := (rangeOf_Expr rec.body).end_ }
    | .Do rec => { start := rec.keyword.range.start, end_ := (rangeOf_NonEmptyArray_DoStatementRecursive rec.statements).end_ }
    | .Ado rec => { start := rec.keyword.range.start, end_ := (rangeOf_Expr rec.result).end_ }
    | .Error e_inner => RangeOf.rangeOf e_inner

  partial def rangeOf_NonEmptyArray_DoStatementRecursive (arr : NonEmptyArray (DoStatementRecursive e)) : SourceRange :=
    { start := (rangeOf_DoStatementRecursive arr.head).start, end_ := (rangeOf_DoStatementRecursive (arr.tail.back?.getD arr.head)).end_ }

  partial def rangeOf_AppSpineRecursive (spine : AppSpineRecursive e) : SourceRange := match spine with
    | .Type_ tok a => { start := tok.range.start, end_ := (rangeOf_Type_ a).end_ }
    | .Term a => rangeOf_Expr a

  partial def rangeOf_LetBindingRecursive (lb : LetBindingRecursive e) : SourceRange := match lb with
    | .Signature lbl => { start := (RangeOf.rangeOf lbl.label).start, end_ := (rangeOf_Type_ lbl.value).end_ }
    | .Name fields => rangeOf_ValueBindingFieldsRecursive fields
    | .Pattern b _ wh => { start := (rangeOf_Binder b).start, end_ := (rangeOf_WhereRecursive wh).end_ }
    | .Error e_inner => RangeOf.rangeOf e_inner

  partial def rangeOf_DoStatementRecursive (ds : DoStatementRecursive e) : SourceRange := match ds with
    | .Let tok bindings => { start := tok.range.start, end_ := (rangeOf_LetBindingRecursive (bindings.tail.back?.getD bindings.head)).end_ }
    | .Discard expr => rangeOf_Expr expr
    | .Bind b _ expr => { start := (rangeOf_Binder b).start, end_ := (rangeOf_Expr expr).end_ }
    | .Error e_inner => RangeOf.rangeOf e_inner

  partial def rangeOf_Binder (b : Binder e) : SourceRange := match b with
    | .Wildcard tok => tok.range
    | .Var n => RangeOf.rangeOf n
    | .Named n _ b_ => { start := (RangeOf.rangeOf n).start, end_ := (rangeOf_Binder b_).end_ }
    | .Constructor n bs =>
        let end_pos := match bs.back? with
          | some last_b => (rangeOf_Binder last_b).end_
          | none => (RangeOf.rangeOf n).end_
        { start := (RangeOf.rangeOf n).start, end_ := end_pos }
    | .Boolean tok _ => tok.range
    | .Char tok _ => tok.range
    | .String tok _ => tok.range
    | .Int pref tok _ =>
      match pref with
      | none => tok.range
      | some n => { start := n.range.start, end_ := tok.range.end_ }
    | .Number pref tok _ =>
      match pref with
      | none => tok.range
      | some n => { start := n.range.start, end_ := tok.range.end_ }
    | .Array bs => RangeOf.rangeOf bs
    | .Record bs => RangeOf.rangeOf bs
    | .Parens b_ => RangeOf.rangeOf b_
    | .Typed b_ _ ty => { start := (rangeOf_Binder b_).start, end_ := (rangeOf_Type_ ty).end_ }
    | .Op b_ ops => { start := (rangeOf_Binder b_).start, end_ := (rangeOf_Binder (ops.tail.back?.getD ops.head).2).end_ }
    | .Error e_inner => RangeOf.rangeOf e_inner

  partial def rangeOf_WhereRecursive (w : WhereRecursive e) : SourceRange :=
    let end_pos := match w.bindings with
      | some (_, bs) => (rangeOf_LetBindingRecursive (bs.tail.back?.getD bs.head)).end_
      | none => (rangeOf_Expr w.expr).end_
    { start := (rangeOf_Expr w.expr).start, end_ := end_pos }

  partial def rangeOf_ModuleBody (b : ModuleBody e) : SourceRange :=
    { start := b.end_, end_ := b.end_ }

  partial def rangeOf_Module (m : Module e) : SourceRange :=
    { start := m.header.keyword.range.start, end_ := m.body.end_ }
end

instance [RangeOf e] : RangeOf (Type_ e) := ⟨rangeOf_Type_⟩
instance [RangeOf name] [RangeOf e] : RangeOf (TypeVarBinding name e) where
  rangeOf := fun x => match x with
    | TypeVarBinding.Kinded w => RangeOf.rangeOf w
    | TypeVarBinding.Name n => RangeOf.rangeOf n
instance [RangeOf e] : RangeOf (Export e) := ⟨rangeOf_Export⟩
instance [RangeOf e] : RangeOf (Import e) := ⟨rangeOf_Import⟩
instance [RangeOf e] : RangeOf (ImportDecl e) := ⟨rangeOf_ImportDecl⟩
instance [RangeOf e] : RangeOf (ModuleHeader e) := ⟨rangeOf_ModuleHeader⟩
instance [RangeOf e] : RangeOf (DataCtor e) := ⟨rangeOf_DataCtor⟩
instance [RangeOf e] : RangeOf (Declaration e) := ⟨rangeOf_Declaration⟩
instance [RangeOf e] : RangeOf (Instance e) := ⟨rangeOf_Instance⟩
instance [RangeOf e] : RangeOf (GuardedRecursive e) := ⟨rangeOf_GuardedRecursive⟩
instance [RangeOf e] : RangeOf (GuardedExprRecursive e) := ⟨rangeOf_GuardedExprRecursive⟩
instance [RangeOf e] : RangeOf (PatternGuardRecursive e) := ⟨rangeOf_PatternGuardRecursive⟩
instance [RangeOf e] : RangeOf (Foreign e) := ⟨rangeOf_Foreign⟩
instance [RangeOf e] : RangeOf (InstanceBinding e) := ⟨rangeOf_InstanceBinding⟩
instance [RangeOf e] : RangeOf (Expr e) := ⟨rangeOf_Expr⟩
instance [RangeOf e] : RangeOf (AppSpineRecursive e) := ⟨rangeOf_AppSpineRecursive⟩
instance [RangeOf e] : RangeOf (DoStatementRecursive e) := ⟨rangeOf_DoStatementRecursive⟩
instance [RangeOf e] : RangeOf (LetBindingRecursive e) := ⟨rangeOf_LetBindingRecursive⟩
instance [RangeOf e] : RangeOf (Binder e) := ⟨rangeOf_Binder⟩
instance [RangeOf e] : RangeOf (WhereRecursive e) := ⟨rangeOf_WhereRecursive⟩
instance [RangeOf e] : RangeOf (ModuleBody e) := ⟨rangeOf_ModuleBody⟩
instance [RangeOf e] : RangeOf (Module e) := ⟨rangeOf_Module⟩
instance [RangeOf e] : RangeOf (ValueBindingFieldsRecursive e) := ⟨rangeOf_ValueBindingFieldsRecursive⟩

end PurescriptLanguageCstParser.Range
