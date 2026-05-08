module

public import PurescriptLanguageCstParser.Types.PType
public import PurescriptLanguageCstParser.Types.Module
public import PurescriptLanguageCstParser.Errors
public import PurescriptLanguageCstParser.Range.TokenList
public import NonEmpty.CorrectByConstruction.Array

namespace PurescriptLanguageCstParser.Range

open PurescriptLanguageCstParser.Types
open PurescriptLanguageCstParser.Range.TokenList
open NonEmpty.CorrectByConstruction.Array
open PurescriptLanguageCstParser.Errors

set_option autoImplicit false

class TokensOf (α : Type) where
  tokensOf (a : α) : TokenList

instance : Inhabited TokenList := ⟨TokenList.mempty⟩

-- ── Generic Instances ───────────────────────────────────────────────────────

instance : TokensOf SourceToken where
  tokensOf t := TokenList.singleton t

instance {α β : Type} [TokensOf α] [TokensOf β] : TokensOf (α × β) where
  tokensOf ab := TokensOf.tokensOf ab.1 ++ TokensOf.tokensOf ab.2

instance {α : Type} [TokensOf α] : TokensOf (Option α) where
  tokensOf o := match o with
    | some a => TokensOf.tokensOf a
    | none => mempty

instance {α : Type} [TokensOf α] : TokensOf (Array α) where
  tokensOf arr := arr.foldl (fun acc a => acc ++ TokensOf.tokensOf a) mempty

instance {α : Type} [TokensOf α] : TokensOf (NonEmptyArray α) where
  tokensOf arr := TokensOf.tokensOf arr.head ++ arr.tail.foldl (fun acc a => acc ++ TokensOf.tokensOf a) mempty

instance : TokensOf Empty where
  tokensOf v := nomatch v

-- ── CST Generic Wrappers ────────────────────────────────────────────────────

instance {a : Type} : TokensOf (Name a) where
  tokensOf n := TokenList.singleton n.token

instance {a : Type} : TokensOf (QualifiedName a) where
  tokensOf n := TokenList.singleton n.token

instance {a : Type} [TokensOf a] : TokensOf (Wrapped a) where
  tokensOf w := wrap w.open_ (TokensOf.tokensOf w.value) w.close

instance {a : Type} [TokensOf a] : TokensOf (Separated a) where
  tokensOf s :=
    TokensOf.tokensOf s.head ++ s.tail.foldl (fun acc (tok, a) => acc ++ cons tok (TokensOf.tokensOf a)) mempty

instance {a b : Type} [TokensOf a] [TokensOf b] : TokensOf (Labeled a b) where
  tokensOf l := TokensOf.tokensOf l.label ++ TokenList.singleton l.separator ++ TokensOf.tokensOf l.value

instance {a : Type} [TokensOf a] : TokensOf (Prefixed a) where
  tokensOf p :=
    match p.prefix_ with
    | some tok => cons tok (TokensOf.tokensOf p.value)
    | none => TokensOf.tokensOf p.value

instance {a : Type} [TokensOf a] : TokensOf (Delimited a) where
  tokensOf | .mk w => TokensOf.tokensOf w

instance {a : Type} [TokensOf a] : TokensOf (DelimitedNonEmpty a) where
  tokensOf | .mk w => TokensOf.tokensOf w

instance {a : Type} [TokensOf a] : TokensOf (OneOrDelimited a) where
  tokensOf o := match o with
    | .One a => TokensOf.tokensOf a
    | .Many as => TokensOf.tokensOf as

instance {a : Type} [TokensOf a] : TokensOf (Row a) where
  tokensOf r :=
    (match r.labels with
     | some s => TokensOf.tokensOf s
     | none => mempty)
    ++ (match r.tail with
      | some (tok, ty) => cons tok (TokensOf.tokensOf ty)
      | none => mempty)

-- ── CST Specific Instances ──────────────────────────────────────────────────

instance : TokensOf RecoveredError where
  tokensOf err := fromArray err.tokens

instance : TokensOf DataMembers where
  tokensOf dm := match dm with
    | .All tok => TokenList.singleton tok
    | .Enumerated w => TokensOf.tokensOf w

instance : TokensOf ClassFundep where
  tokensOf cf := match cf with
    | .Determined tok ns => cons tok (TokensOf.tokensOf ns)
    | .Determines ns1 tok ns2 => TokensOf.tokensOf ns1 ++ TokenList.singleton tok ++ TokensOf.tokensOf ns2

instance : TokensOf FixityOp where
  tokensOf fo := match fo with
    | .Value n tok op => TokensOf.tokensOf n ++ TokenList.singleton tok ++ TokensOf.tokensOf op
    | .Type_ tok1 n tok2 op => cons tok1 (TokensOf.tokensOf n ++ TokenList.singleton tok2 ++ TokensOf.tokensOf op)

instance : TokensOf FixityFields where
  tokensOf fields := cons fields.keyword.1 (cons fields.prec.1 (TokensOf.tokensOf fields.operator))

-- ── Recursive CST Implementation ────────────────────────────────────────────

variable {e : Type} [TokensOf e]

mutual
  partial def tokensOf_Type_ (t : Type_ e) : TokenList := match t with
    | .Var n => TokensOf.tokensOf n
    | .Constructor n => TokensOf.tokensOf n
    | .Wildcard tok => TokenList.singleton tok
    | .Hole n => TokensOf.tokensOf n
    | .String tok _ => TokenList.singleton tok
    | .Int pref tok _ =>
      match pref with
      | none => TokenList.singleton tok
      | some n => TokenList.singleton n ++ TokenList.singleton tok
    | .Row w => tokensOf_WrappedRow w
    | .Record w => tokensOf_WrappedRow w
    | .Forall tok bs c ty => cons tok (tokensOf_TypeF_Forall_Bindings bs ++ TokenList.singleton c ++ tokensOf_Type_ ty)
    | .Kinded ty1 tok ty2 => tokensOf_Type_ ty1 ++ TokenList.singleton tok ++ tokensOf_Type_ ty2
    | .App ty tys => tokensOf_Type_ ty ++ tokensOf_NonEmptyArray_Type_ tys
    | .Op ty ops => tokensOf_Type_ ty ++ tokensOf_TypeF_Op_Ops ops
    | .OpName n => TokensOf.tokensOf n
    | .Arrow ty1 tok ty2 => tokensOf_Type_ ty1 ++ TokenList.singleton tok ++ tokensOf_Type_ ty2
    | .ArrowName tok => TokenList.singleton tok
    | .Constrained ty1 tok ty2 => tokensOf_Type_ ty1 ++ TokenList.singleton tok ++ tokensOf_Type_ ty2
    | .Parens w => tokensOf_Wrapped_Type_ w
    | .Error e_inner => TokensOf.tokensOf e_inner

  partial def tokensOf_WrappedRow (w : Wrapped (Row (Type_ e))) : TokenList :=
    wrap w.open_ (tokensOf_Row w.value) w.close

  partial def tokensOf_Row (r : Row (Type_ e)) : TokenList :=
    tokensOf_Option_Separated_Labeled_Type_ r.labels ++ (match r.tail with
      | some (tok, ty) => cons tok (tokensOf_Type_ ty)
      | none => mempty)

  partial def tokensOf_Option_Separated_Labeled_Type_ (o : Option (Separated (Labeled (Name Label) (Type_ e)))) : TokenList :=
    match o with
    | some s => tokensOf_Separated_Labeled_Type_ s
    | none => mempty

  partial def tokensOf_Separated_Labeled_Type_ (s : Separated (Labeled (Name Label) (Type_ e))) : TokenList :=
    tokensOf_Labeled_Type_ s.head ++ s.tail.foldl (fun acc (tok, l) => acc ++ cons tok (tokensOf_Labeled_Type_ l)) mempty

  partial def tokensOf_Labeled_Type_ (l : Labeled (Name Label) (Type_ e)) : TokenList :=
    TokensOf.tokensOf l.label ++ TokenList.singleton l.separator ++ tokensOf_Type_ l.value

  partial def tokensOf_TypeF_Forall_Bindings (bs : NonEmptyArray (TypeVarBinding (Prefixed (Name Ident)) (Type_ e))) : TokenList :=
    tokensOf_TypeVarBinding_Prefixed_Name_Ident bs.head ++ bs.tail.foldl (fun acc b => acc ++ tokensOf_TypeVarBinding_Prefixed_Name_Ident b) mempty
    where
      tokensOf_TypeVarBinding_Prefixed_Name_Ident (b : TypeVarBinding (Prefixed (Name Ident)) (Type_ e)) : TokenList :=
        match b with
        | .Kinded w => wrap w.open_ (TokensOf.tokensOf w.value.label ++ TokenList.singleton w.value.separator ++ tokensOf_Type_ w.value.value) w.close
        | .Name n => TokensOf.tokensOf n

  partial def tokensOf_Array_Type_ (arr : Array (Type_ e)) : TokenList :=
    arr.foldl (fun acc a => acc ++ tokensOf_Type_ a) mempty

  partial def tokensOf_NonEmptyArray_Type_ (arr : NonEmptyArray (Type_ e)) : TokenList :=
    tokensOf_Type_ arr.head ++ tokensOf_Array_Type_ arr.tail

  partial def tokensOf_TypeF_Op_Ops (ops : NonEmptyArray (QualifiedName Operator × Type_ e)) : TokenList :=
    TokensOf.tokensOf ops.head.1 ++ tokensOf_Type_ ops.head.2 ++ ops.tail.foldl (fun acc (n, t) => acc ++ TokensOf.tokensOf n ++ tokensOf_Type_ t) mempty

  partial def tokensOf_Wrapped_Type_ (w : Wrapped (Type_ e)) : TokenList :=
    wrap w.open_ (tokensOf_Type_ w.value) w.close

  partial def tokensOf_Export (ex : Export e) : TokenList := match ex with
    | .Value n => TokensOf.tokensOf n
    | .Op n => TokensOf.tokensOf n
    | .Type_ n dms => TokensOf.tokensOf n ++ TokensOf.tokensOf dms
    | .TypeOp tok n => cons tok (TokensOf.tokensOf n)
    | .Class tok n => cons tok (TokensOf.tokensOf n)
    | .Module tok n => cons tok (TokensOf.tokensOf n)
    | .Error err => TokensOf.tokensOf err

  partial def tokensOf_Import (im : Import e) : TokenList := match im with
    | .Value n => TokensOf.tokensOf n
    | .Op n => TokensOf.tokensOf n
    | .Type_ n dms => TokensOf.tokensOf n ++ TokensOf.tokensOf dms
    | .TypeOp tok n => cons tok (TokensOf.tokensOf n)
    | .Class tok n => cons tok (TokensOf.tokensOf n)
    | .Error err => TokensOf.tokensOf err

  partial def tokensOf_ImportDecl (id : ImportDecl e) : TokenList :=
    cons id.keyword (
      TokensOf.tokensOf id.module_
        ++ (match id.importList with
           | none => mempty
           | some (hiding_tok, imports) => TokensOf.tokensOf hiding_tok ++ tokensOf_DelimitedNonEmpty_Import imports)
        ++ (match id.qualified with
           | none => mempty
           | some (as_tok, mn) => TokenList.singleton as_tok ++ TokensOf.tokensOf mn)
    )

  partial def tokensOf_DelimitedNonEmpty_Import (dni : DelimitedNonEmpty (Import e)) : TokenList :=
    TokensOf.tokensOf dni.1.open_ ++ tokensOf_Separated_Import dni.1.value ++ TokenList.singleton dni.1.close

  partial def tokensOf_Separated_Import (s : Separated (Import e)) : TokenList :=
    tokensOf_Import s.head ++ s.tail.foldl (fun acc (tok, im) => acc ++ cons tok (tokensOf_Import im)) mempty

  partial def tokensOf_ModuleHeader (m : ModuleHeader e) : TokenList :=
    TokenList.singleton m.keyword
      ++ TokensOf.tokensOf m.name
      ++ tokensOf_Option_DelimitedNonEmpty_Export m.exports
      ++ TokenList.singleton m.where_
      ++ tokensOf_Array_ImportDecl m.imports

  partial def tokensOf_Option_DelimitedNonEmpty_Export (o : Option (DelimitedNonEmpty (Export e))) : TokenList :=
    match o with
    | some dni => wrap dni.1.open_ (tokensOf_Separated_Export dni.1.value) dni.1.close
    | none => mempty

  partial def tokensOf_Separated_Export (s : Separated (Export e)) : TokenList :=
    tokensOf_Export s.head ++ s.tail.foldl (fun acc (tok, ex) => acc ++ cons tok (tokensOf_Export ex)) mempty

  partial def tokensOf_Array_ImportDecl (arr : Array (ImportDecl e)) : TokenList :=
    arr.foldl (fun acc id => acc ++ tokensOf_ImportDecl id) mempty

  partial def tokensOf_DataCtor (dc : DataCtor e) : TokenList :=
    TokensOf.tokensOf dc.name ++ tokensOf_Array_Type_ dc.parameters

  partial def tokensOf_Declaration (decl : Declaration e) : TokenList := match decl with
    | .Data head optionSeparator =>
      tokensOf_DataHead head ++ match optionSeparator with
        | some (tok, cs) => cons tok (tokensOf_Separated_DataCtor cs)
        | none => mempty
    | .Type_ head tok ty => tokensOf_DataHead head ++ TokenList.singleton tok ++ tokensOf_Type_ ty
    | .Newtype head tok n ty => tokensOf_DataHead head ++ TokenList.singleton tok ++ TokensOf.tokensOf n ++ tokensOf_Type_ ty
    | .Class head optionSeparator =>
      tokensOf_ClassHead head ++ match optionSeparator with
        | some (tok, ls) => cons tok (tokensOf_NonEmptyArray_Labeled_NameIdent_Type_ ls)
        | none => mempty
    | .InstanceChain insts => tokensOf_Separated_Instance insts
    | .Derive keyword tok head => cons keyword (TokensOf.tokensOf tok ++ tokensOf_InstanceHead head)
    | .KindSignature keyword lbl => cons keyword (TokensOf.tokensOf lbl.label ++ TokenList.singleton lbl.separator ++ tokensOf_Type_ lbl.value)
    | .Signature lbl => TokensOf.tokensOf lbl.label ++ TokenList.singleton lbl.separator ++ tokensOf_Type_ lbl.value
    | .Value fields => tokensOf_ValueBindingFieldsRecursive fields
    | .Fixity fields => TokensOf.tokensOf fields
    | .Foreign keyword imp frn => cons keyword (cons imp (tokensOf_Foreign frn))
    | .Role keyword rl n roles =>
      cons keyword (
        TokenList.singleton rl
          ++ TokensOf.tokensOf n
          ++ roles.foldl (fun acc (tok, _) => acc ++ TokenList.singleton tok) mempty
      )
    | .Error e_inner => TokensOf.tokensOf e_inner

  partial def tokensOf_NonEmptyArray_Labeled_NameIdent_Type_ (arr : NonEmptyArray (Labeled (Name Ident) (Type_ e))) : TokenList :=
    tokensOf_Labeled_Type_Ident arr.head ++ arr.tail.foldl (fun acc l => acc ++ tokensOf_Labeled_Type_Ident l) mempty
    where
      tokensOf_Labeled_Type_Ident (l : Labeled (Name Ident) (Type_ e)) : TokenList :=
        TokensOf.tokensOf l.label ++ TokenList.singleton l.separator ++ tokensOf_Type_ l.value

  partial def tokensOf_Separated_DataCtor (s : Separated (DataCtor e)) : TokenList :=
    tokensOf_DataCtor s.head ++ s.tail.foldl (fun acc (tok, dc) => acc ++ cons tok (tokensOf_DataCtor dc)) mempty

  partial def tokensOf_Separated_InstanceBinding (s : Separated (InstanceBinding e)) : TokenList :=
    tokensOf_InstanceBinding s.head ++ s.tail.foldl (fun acc (tok, ib) => acc ++ cons tok (tokensOf_InstanceBinding ib)) mempty

  partial def tokensOf_Separated_Instance (s : Separated (Instance e)) : TokenList :=
    tokensOf_Instance s.head ++ s.tail.foldl (fun acc (tok, inst) => acc ++ cons tok (tokensOf_Instance inst)) mempty

  partial def tokensOf_ValueBindingFieldsRecursive (fields : ValueBindingFieldsRecursive e) : TokenList :=
    TokensOf.tokensOf fields.name ++ tokensOf_Array_Binder fields.binders ++ tokensOf_GuardedRecursive fields.guarded

  partial def tokensOf_Array_Binder (arr : Array (Binder e)) : TokenList :=
    arr.foldl (fun acc b => acc ++ tokensOf_Binder b) mempty

  partial def tokensOf_DataHead (h : DataHead e) : TokenList :=
    TokenList.singleton h.keyword ++ TokensOf.tokensOf h.name ++ tokensOf_Array_TypeVarBinding_Name_Ident h.parameters

  partial def tokensOf_Array_TypeVarBinding_Name_Ident (arr : Array (TypeVarBinding (Name Ident) (Type_ e))) : TokenList :=
    arr.foldl (fun acc b => acc ++ (match b with
      | .Kinded w => wrap w.open_ (TokensOf.tokensOf w.value.label ++ TokenList.singleton w.value.separator ++ tokensOf_Type_ w.value.value) w.close
      | .Name n => TokensOf.tokensOf n)) mempty

  partial def tokensOf_ClassHead (h : ClassHead e) : TokenList :=
    TokenList.singleton h.keyword
      ++ tokensOf_Option_OneOrDelimited_Type_ h.typeConstraint
      ++ TokensOf.tokensOf h.name
      ++ tokensOf_Array_TypeVarBinding_Name_Ident h.parameters
      ++ tokensOf_Option_SourceToken_Separated_ClassFundep h.fundependencies

  partial def tokensOf_Option_OneOrDelimited_Type_ (o : Option (OneOrDelimited (Type_ e) × SourceToken)) : TokenList :=
    match o with
    | some (od, tok) => (match od with | .One ty => tokensOf_Type_ ty | .Many tys => wrap tys.1.open_ (tokensOf_Separated_Type_ tys.1.value) tys.1.close) ++ TokenList.singleton tok
    | none => mempty

  partial def tokensOf_Separated_Type_ (s : Separated (Type_ e)) : TokenList :=
    tokensOf_Type_ s.head ++ s.tail.foldl (fun acc (tok, ty) => acc ++ cons tok (tokensOf_Type_ ty)) mempty

  partial def tokensOf_Option_SourceToken_Separated_ClassFundep (o : Option (SourceToken × Separated ClassFundep)) : TokenList :=
    match o with
    | some (tok, s) => cons tok (TokensOf.tokensOf s)
    | none => mempty

  partial def tokensOf_InstanceHead (h : InstanceHead e) : TokenList :=
    TokenList.singleton h.keyword
      ++ tokensOf_Option_Name_Ident_SourceToken h.name
      ++ tokensOf_Option_OneOrDelimited_Type_ h.constraints
      ++ TokensOf.tokensOf h.className
      ++ tokensOf_Array_Type_ h.types

  partial def tokensOf_Option_Name_Ident_SourceToken (o : Option (Name Ident × SourceToken)) : TokenList :=
    match o with
    | some (n, tok) => TokensOf.tokensOf n ++ TokenList.singleton tok
    | none => mempty

  partial def tokensOf_Instance (inst : Instance e) : TokenList :=
    tokensOf_InstanceHead inst.head ++ match inst.body with
      | some (tok, bs) => cons tok (tokensOf_NonEmptyArray_InstanceBinding bs)
      | none => mempty

  partial def tokensOf_NonEmptyArray_InstanceBinding (arr : NonEmptyArray (InstanceBinding e)) : TokenList :=
    tokensOf_InstanceBinding arr.head ++ arr.tail.foldl (fun acc ib => acc ++ tokensOf_InstanceBinding ib) mempty

  partial def tokensOf_Array_InstanceBinding (arr : Array (InstanceBinding e)) : TokenList :=
    arr.foldl (fun acc ib => acc ++ tokensOf_InstanceBinding ib) mempty

  partial def tokensOf_InstanceBinding (ib : InstanceBinding e) : TokenList := match ib with
    | .Signature lbl => TokensOf.tokensOf lbl.label ++ TokenList.singleton lbl.separator ++ tokensOf_Type_ lbl.value
    | .Name fields => tokensOf_ValueBindingFieldsRecursive fields

  partial def tokensOf_GuardedRecursive (g : GuardedRecursive e) : TokenList := match g with
    | .Unconditional tok wh => cons tok (tokensOf_WhereRecursive wh)
    | .Guarded gs => tokensOf_NonEmptyArray_GuardedExprRecursive gs

  partial def tokensOf_NonEmptyArray_GuardedExprRecursive (arr : NonEmptyArray (GuardedExprRecursive e)) : TokenList :=
    tokensOf_GuardedExprRecursive arr.head ++ arr.tail.foldl (fun acc ge => acc ++ tokensOf_GuardedExprRecursive ge) mempty

  partial def tokensOf_GuardedExprRecursive (ge : GuardedExprRecursive e) : TokenList :=
    cons ge.bar (tokensOf_Separated_PatternGuardRecursive ge.patterns ++ TokenList.singleton ge.separator ++ tokensOf_WhereRecursive ge.where_)

  partial def tokensOf_Separated_PatternGuardRecursive (s : Separated (PatternGuardRecursive e)) : TokenList :=
    tokensOf_PatternGuardRecursive s.head ++ s.tail.foldl (fun acc (tok, pg) => acc ++ cons tok (tokensOf_PatternGuardRecursive pg)) mempty

  partial def tokensOf_PatternGuardRecursive (pg : PatternGuardRecursive e) : TokenList :=
    (match pg.binder with | some (b, tok) => tokensOf_Binder b ++ TokenList.singleton tok | none => mempty)
      ++ tokensOf_Expr pg.expr

  partial def tokensOf_Foreign (f : Foreign e) : TokenList := match f with
    | .Value lbl => TokensOf.tokensOf lbl.label ++ TokenList.singleton lbl.separator ++ tokensOf_Type_ lbl.value
    | .Data tok lbl => cons tok (TokensOf.tokensOf lbl.label ++ TokenList.singleton lbl.separator ++ tokensOf_Type_ lbl.value)
    | .Kind tok n => cons tok (TokensOf.tokensOf n)

  partial def tokensOf_Expr (expr : Expr e) : TokenList := match expr with
    | .Hole n => TokensOf.tokensOf n
    | .Section tok => TokenList.singleton tok
    | .Ident n => TokensOf.tokensOf n
    | .Constructor n => TokensOf.tokensOf n
    | .Boolean tok _ => TokenList.singleton tok
    | .Char tok _ => TokenList.singleton tok
    | .String tok _ => TokenList.singleton tok
    | .Int tok _ => TokenList.singleton tok
    | .Number tok _ => TokenList.singleton tok
    | .Array exprs => tokensOf_Delimited_Expr exprs
    | .Record exprs => tokensOf_Delimited_RecordLabeled_Expr exprs
    | .Parens w => tokensOf_Wrapped_Expr w
    | .Typed e_inner tok ty => tokensOf_Expr e_inner ++ cons tok (tokensOf_Type_ ty)
    | .Infix e_inner ops => tokensOf_Expr e_inner ++ tokensOf_NonEmptyArray_WrappedExpr_Expr ops
    | .Op e_inner ops => tokensOf_Expr e_inner ++ tokensOf_NonEmptyArray_QualOp_Expr ops
    | .OpName n => TokensOf.tokensOf n
    | .Negate tok e_inner => cons tok (tokensOf_Expr e_inner)
    | .RecordAccessor rec => tokensOf_Expr rec.expr ++ cons rec.dot (TokensOf.tokensOf rec.path)
    | .RecordUpdate e_inner upds => tokensOf_Expr e_inner ++ tokensOf_DelimitedNonEmpty_RecordUpdateRecursive upds
    | .App fn args => tokensOf_Expr fn ++ tokensOf_NonEmptyArray_AppSpineRecursive args
    | .Lambda rec => cons rec.symbol (tokensOf_NonEmptyArray_Binder rec.binders ++ TokenList.singleton rec.arrow ++ tokensOf_Expr rec.body)
    | .If rec =>
      cons rec.keyword (
        tokensOf_Expr rec.cond
          ++ TokenList.singleton rec.then_
          ++ tokensOf_Expr rec.true_
          ++ TokenList.singleton rec.else_
          ++ tokensOf_Expr rec.false_
      )
    | .Case rec => cons rec.keyword (tokensOf_Separated_Expr rec.head ++ TokenList.singleton rec.«of» ++ tokensOf_NonEmptyArray_SeparatedBinder_GuardedRecursive rec.branches)
    | .Let rec => cons rec.keyword (tokensOf_NonEmptyArray_LetBindingRecursive rec.bindings ++ TokenList.singleton rec.in_ ++ tokensOf_Expr rec.body)
    | .Do rec => cons rec.keyword (tokensOf_NonEmptyArray_DoStatementRecursive rec.statements)
    | .Ado rec => cons rec.keyword (tokensOf_Array_DoStatementRecursive rec.statements ++ TokenList.singleton rec.in_ ++ tokensOf_Expr rec.result)
    | .Error e_inner => TokensOf.tokensOf e_inner

  partial def tokensOf_Delimited_Expr (d : Delimited (Expr e)) : TokenList :=
    wrap d.1.open_ (tokensOf_Option_Separated_Expr d.1.value) d.1.close

  partial def tokensOf_Option_Separated_Expr (o : Option (Separated (Expr e))) : TokenList :=
    match o with | some s => tokensOf_Separated_Expr s | none => mempty

  partial def tokensOf_Separated_Expr (s : Separated (Expr e)) : TokenList :=
    tokensOf_Expr s.head ++ s.tail.foldl (fun acc (tok, e_inner) => acc ++ cons tok (tokensOf_Expr e_inner)) mempty

  partial def tokensOf_Delimited_RecordLabeled_Expr (d : Delimited (RecordLabeled (Expr e))) : TokenList :=
    wrap d.1.open_ (tokensOf_Option_Separated_RecordLabeled_Expr d.1.value) d.1.close

  partial def tokensOf_Option_Separated_RecordLabeled_Expr (o : Option (Separated (RecordLabeled (Expr e)))) : TokenList :=
    match o with | some s => tokensOf_Separated_RecordLabeled_Expr s | none => mempty

  partial def tokensOf_Separated_RecordLabeled_Expr (s : Separated (RecordLabeled (Expr e))) : TokenList :=
    tokensOf_RecordLabeled_Expr s.head ++ s.tail.foldl (fun acc (tok, rl) => acc ++ cons tok (tokensOf_RecordLabeled_Expr rl)) mempty

  partial def tokensOf_RecordLabeled_Expr (rl : RecordLabeled (Expr e)) : TokenList := match rl with
    | .Pun n => TokensOf.tokensOf n
    | .Field n tok a => TokensOf.tokensOf n ++ cons tok (tokensOf_Expr a)

  partial def tokensOf_Wrapped_Expr (w : Wrapped (Expr e)) : TokenList :=
    wrap w.open_ (tokensOf_Expr w.value) w.close

  partial def tokensOf_NonEmptyArray_WrappedExpr_Expr (arr : NonEmptyArray (Wrapped (Expr e) × Expr e)) : TokenList :=
    (tokensOf_Wrapped_Expr arr.head.1 ++ tokensOf_Expr arr.head.2) ++ arr.tail.foldl (fun acc (w, e_inner) => acc ++ tokensOf_Wrapped_Expr w ++ tokensOf_Expr e_inner) mempty

  partial def tokensOf_NonEmptyArray_QualOp_Expr (arr : NonEmptyArray (QualifiedName Operator × Expr e)) : TokenList :=
    (TokensOf.tokensOf arr.head.1 ++ tokensOf_Expr arr.head.2) ++ arr.tail.foldl (fun acc (n, e_inner) => acc ++ TokensOf.tokensOf n ++ tokensOf_Expr e_inner) mempty

  partial def tokensOf_DelimitedNonEmpty_RecordUpdateRecursive (dni : DelimitedNonEmpty (RecordUpdateRecursive e)) : TokenList :=
    wrap dni.1.open_ (tokensOf_Separated_RecordUpdateRecursive dni.1.value) dni.1.close

  partial def tokensOf_Separated_RecordUpdateRecursive (s : Separated (RecordUpdateRecursive e)) : TokenList :=
    tokensOf_RecordUpdateRecursive s.head ++ s.tail.foldl (fun acc (tok, ru) => acc ++ cons tok (tokensOf_RecordUpdateRecursive ru)) mempty

  partial def tokensOf_RecordUpdateRecursive (ru : RecordUpdateRecursive e) : TokenList := match ru with
    | .Leaf n tok e_inner => TokensOf.tokensOf n ++ TokenList.singleton tok ++ tokensOf_Expr e_inner
    | .Branch n us => TokensOf.tokensOf n ++ tokensOf_DelimitedNonEmpty_RecordUpdateRecursive us

  partial def tokensOf_NonEmptyArray_AppSpineRecursive (arr : NonEmptyArray (AppSpineRecursive e)) : TokenList :=
    tokensOf_AppSpineRecursive arr.head ++ arr.tail.foldl (fun acc a => acc ++ tokensOf_AppSpineRecursive a) mempty

  partial def tokensOf_AppSpineRecursive (spine : AppSpineRecursive e) : TokenList := match spine with
    | .Type_ tok a => cons tok (tokensOf_Type_ a)
    | .Term a => tokensOf_Expr a

  partial def tokensOf_NonEmptyArray_Binder (arr : NonEmptyArray (Binder e)) : TokenList :=
    tokensOf_Binder arr.head ++ arr.tail.foldl (fun acc b => acc ++ tokensOf_Binder b) mempty

  partial def tokensOf_NonEmptyArray_SeparatedBinder_GuardedRecursive (arr : NonEmptyArray (Separated (Binder e) × GuardedRecursive e)) : TokenList :=
    (tokensOf_Separated_Binder arr.head.1 ++ tokensOf_GuardedRecursive arr.head.2) ++ arr.tail.foldl (fun acc (s, g) => acc ++ tokensOf_Separated_Binder s ++ tokensOf_GuardedRecursive g) mempty

  partial def tokensOf_Separated_Binder (s : Separated (Binder e)) : TokenList :=
    tokensOf_Binder s.head ++ s.tail.foldl (fun acc (tok, b) => acc ++ cons tok (tokensOf_Binder b)) mempty

  partial def tokensOf_NonEmptyArray_LetBindingRecursive (arr : NonEmptyArray (LetBindingRecursive e)) : TokenList :=
    tokensOf_LetBindingRecursive arr.head ++ arr.tail.foldl (fun acc lb => acc ++ tokensOf_LetBindingRecursive lb) mempty

  partial def tokensOf_LetBindingRecursive (lb : LetBindingRecursive e) : TokenList := match lb with
    | .Signature lbl => TokensOf.tokensOf lbl.label ++ TokenList.singleton lbl.separator ++ tokensOf_Type_ lbl.value
    | .Name fields => tokensOf_ValueBindingFieldsRecursive fields
    | .Pattern b tok wh => tokensOf_Binder b ++ cons tok (tokensOf_WhereRecursive wh)
    | .Error e_inner => TokensOf.tokensOf e_inner

  partial def tokensOf_NonEmptyArray_DoStatementRecursive (arr : NonEmptyArray (DoStatementRecursive e)) : TokenList :=
    tokensOf_DoStatementRecursive arr.head ++ arr.tail.foldl (fun acc ds => acc ++ tokensOf_DoStatementRecursive ds) mempty

  partial def tokensOf_Array_DoStatementRecursive (arr : Array (DoStatementRecursive e)) : TokenList :=
    arr.foldl (fun acc ds => acc ++ tokensOf_DoStatementRecursive ds) mempty

  partial def tokensOf_DoStatementRecursive (ds : DoStatementRecursive e) : TokenList := match ds with
    | .Let tok bindings => cons tok (tokensOf_NonEmptyArray_LetBindingRecursive bindings)
    | .Discard expr => tokensOf_Expr expr
    | .Bind b tok expr => tokensOf_Binder b ++ cons tok (tokensOf_Expr expr)
    | .Error e_inner => TokensOf.tokensOf e_inner

  partial def tokensOf_Binder (b : Binder e) : TokenList := match b with
    | .Wildcard tok => TokenList.singleton tok
    | .Var n => TokensOf.tokensOf n
    | .Named n tok b_ => TokensOf.tokensOf n ++ cons tok (tokensOf_Binder b_)
    | .Constructor n bs => TokensOf.tokensOf n ++ tokensOf_Array_Binder bs
    | .Boolean tok _ => TokenList.singleton tok
    | .Char tok _ => TokenList.singleton tok
    | .String tok _ => TokenList.singleton tok
    | .Int pref tok _ =>
      match pref with
      | none => TokenList.singleton tok
      | some n => TokenList.singleton n ++ TokenList.singleton tok
    | .Number pref tok _ =>
      match pref with
      | none => TokenList.singleton tok
      | some n => TokenList.singleton n ++ TokenList.singleton tok
    | .Array bs => tokensOf_Delimited_Binder bs
    | .Record bs => tokensOf_Delimited_RecordLabeled_Binder bs
    | .Parens b_ => tokensOf_Wrapped_Binder b_
    | .Typed b_ tok ty => tokensOf_Binder b_ ++ cons tok (tokensOf_Type_ ty)
    | .Op b_ ops => tokensOf_Binder b_ ++ tokensOf_NonEmptyArray_QualOp_Binder ops
    | .Error e_inner => TokensOf.tokensOf e_inner

  partial def tokensOf_Delimited_Binder (d : Delimited (Binder e)) : TokenList :=
    wrap d.1.open_ (tokensOf_Option_Separated_Binder d.1.value) d.1.close

  partial def tokensOf_Option_Separated_Binder (o : Option (Separated (Binder e))) : TokenList :=
    match o with | some s => tokensOf_Separated_Binder s | none => mempty

  partial def tokensOf_Delimited_RecordLabeled_Binder (d : Delimited (RecordLabeled (Binder e))) : TokenList :=
    wrap d.1.open_ (tokensOf_Option_Separated_RecordLabeled_Binder d.1.value) d.1.close

  partial def tokensOf_Option_Separated_RecordLabeled_Binder (o : Option (Separated (RecordLabeled (Binder e)))) : TokenList :=
    match o with | some s => tokensOf_Separated_RecordLabeled_Binder s | none => mempty

  partial def tokensOf_Separated_RecordLabeled_Binder (s : Separated (RecordLabeled (Binder e))) : TokenList :=
    tokensOf_RecordLabeled_Binder s.head ++ s.tail.foldl (fun acc (tok, rl) => acc ++ cons tok (tokensOf_RecordLabeled_Binder rl)) mempty

  partial def tokensOf_RecordLabeled_Binder (rl : RecordLabeled (Binder e)) : TokenList := match rl with
    | .Pun n => TokensOf.tokensOf n
    | .Field n tok a => TokensOf.tokensOf n ++ cons tok (tokensOf_Binder a)

  partial def tokensOf_Wrapped_Binder (w : Wrapped (Binder e)) : TokenList :=
    wrap w.open_ (tokensOf_Binder w.value) w.close

  partial def tokensOf_NonEmptyArray_QualOp_Binder (arr : NonEmptyArray (QualifiedName Operator × Binder e)) : TokenList :=
    (TokensOf.tokensOf arr.head.1 ++ tokensOf_Binder arr.head.2) ++ arr.tail.foldl (fun acc (n, b) => acc ++ TokensOf.tokensOf n ++ tokensOf_Binder b) mempty

  partial def tokensOf_WhereRecursive (w : WhereRecursive e) : TokenList :=
    tokensOf_Expr w.expr ++ match w.bindings with
      | some (tok, bs) => cons tok (tokensOf_NonEmptyArray_LetBindingRecursive bs)
      | none => mempty

  partial def tokensOf_ModuleBody (b : ModuleBody e) : TokenList := tokensOf_Array_Declaration b.decls

  partial def tokensOf_Array_Declaration (arr : Array (Declaration e)) : TokenList :=
    arr.foldl (fun acc decl => acc ++ tokensOf_Declaration decl) mempty

  partial def tokensOf_Module (m : Module e) : TokenList := tokensOf_ModuleHeader m.header ++ tokensOf_ModuleBody m.body
end

instance {e : Type} [TokensOf e] : TokensOf (Type_ e) := ⟨tokensOf_Type_⟩
instance {name e : Type} [TokensOf name] [TokensOf e] : TokensOf (TypeVarBinding name e) where
  tokensOf := fun x => match x with
    | .Kinded w => TokensOf.tokensOf w
    | .Name n => TokensOf.tokensOf n
instance {e : Type} [TokensOf e] : TokensOf (Export e) := ⟨tokensOf_Export⟩
instance {e : Type} [TokensOf e] : TokensOf (Import e) := ⟨tokensOf_Import⟩
instance {e : Type} [TokensOf e] : TokensOf (ImportDecl e) := ⟨tokensOf_ImportDecl⟩
instance {e : Type} [TokensOf e] : TokensOf (ModuleHeader e) := ⟨tokensOf_ModuleHeader⟩
instance {e : Type} [TokensOf e] : TokensOf (DataCtor e) := ⟨tokensOf_DataCtor⟩
instance {e : Type} [TokensOf e] : TokensOf (Declaration e) := ⟨tokensOf_Declaration⟩
instance {e : Type} [TokensOf e] : TokensOf (Instance e) := ⟨tokensOf_Instance⟩
instance {e : Type} [TokensOf e] : TokensOf (GuardedRecursive e) := ⟨tokensOf_GuardedRecursive⟩
instance {e : Type} [TokensOf e] : TokensOf (GuardedExprRecursive e) := ⟨tokensOf_GuardedExprRecursive⟩
instance {e : Type} [TokensOf e] : TokensOf (PatternGuardRecursive e) := ⟨tokensOf_PatternGuardRecursive⟩
instance {e : Type} [TokensOf e] : TokensOf (Foreign e) := ⟨tokensOf_Foreign⟩
instance {e : Type} [TokensOf e] : TokensOf (InstanceBinding e) := ⟨tokensOf_InstanceBinding⟩
instance {e : Type} [TokensOf e] : TokensOf (Expr e) := ⟨tokensOf_Expr⟩
instance {e : Type} [TokensOf e] : TokensOf (AppSpineRecursive e) := ⟨tokensOf_AppSpineRecursive⟩
instance {e : Type} [TokensOf e] : TokensOf (RecordUpdateRecursive e) := ⟨tokensOf_RecordUpdateRecursive⟩
instance {e : Type} [TokensOf e] : TokensOf (DoStatementRecursive e) := ⟨tokensOf_DoStatementRecursive⟩
instance {e : Type} [TokensOf e] : TokensOf (LetBindingRecursive e) := ⟨tokensOf_LetBindingRecursive⟩
instance {e : Type} [TokensOf e] : TokensOf (Binder e) := ⟨tokensOf_Binder⟩
instance {e : Type} [TokensOf e] : TokensOf (WhereRecursive e) := ⟨tokensOf_WhereRecursive⟩
instance {e : Type} [TokensOf e] : TokensOf (ModuleBody e) := ⟨tokensOf_ModuleBody⟩
instance {e : Type} [TokensOf e] : TokensOf (Module e) := ⟨tokensOf_Module⟩
instance {e : Type} [TokensOf e] : TokensOf (DataHead e) := ⟨tokensOf_DataHead⟩
instance {e : Type} [TokensOf e] : TokensOf (ClassHead e) := ⟨tokensOf_ClassHead⟩
instance {e : Type} [TokensOf e] : TokensOf (InstanceHead e) := ⟨tokensOf_InstanceHead⟩
instance {e : Type} [TokensOf e] : TokensOf (ValueBindingFieldsRecursive e) := ⟨tokensOf_ValueBindingFieldsRecursive⟩

end PurescriptLanguageCstParser.Range
