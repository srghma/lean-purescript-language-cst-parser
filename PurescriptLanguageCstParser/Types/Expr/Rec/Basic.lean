module

public import PurescriptLanguageCstParser.Types.PType
public import PurescriptLanguageCstParser.Types.Expr.Leafs
meta import PurescriptLanguageCstParser.GenerateFixed

@[expose] public section

namespace PurescriptLanguageCstParser.Types

-- https://github.com/leanprover/lean4/issues/13465#issuecomment-4349653768
/--
info: generate_fixed_mutual expansion:
mutual
  structure PatternGuardRecursive (e : Type) where
    binder : Option (Binder e × SourceToken)
    expr : Expr e
    deriving Repr, BEq
  inductive LetBindingRecursive (e : Type) : Type where
    | Signature (labeled : Labeled (Name Ident) (Type_ e)) : LetBindingRecursive e
    | Name (fields : ValueBindingFieldsRecursive e) : LetBindingRecursive e
    | Pattern (binder : Binder e) (token : SourceToken) (where_ : WhereRecursive e) : LetBindingRecursive e
    | Error (data : e) : LetBindingRecursive e
    deriving Repr, BEq
  structure WhereRecursive (e : Type) where
    expr : Expr e
    bindings : Option (SourceToken × NonEmpty.ArrayCorrectByConstruction.NonEmptyArray (LetBindingRecursive e))
    deriving Repr, BEq
  inductive GuardedRecursive (e : Type) : Type where
    | Unconditional (token : SourceToken) (where_ : WhereRecursive e) : GuardedRecursive e
    |
    Guarded (branches : NonEmpty.ArrayCorrectByConstruction.NonEmptyArray (GuardedExprRecursive e)) : GuardedRecursive e
    deriving Repr, BEq
  structure GuardedExprRecursive (e : Type) where
    bar : SourceToken
    patterns : Separated (PatternGuardRecursive e)
    separator : SourceToken
    where_ : WhereRecursive e
    deriving Repr, BEq
  structure ValueBindingFieldsRecursive (e : Type) where
    name : Name Ident
    binders : Array (Binder e)
    guarded : GuardedRecursive e
    deriving Repr, BEq
  inductive DoStatementRecursive (e : Type) : Type where
    |
    Let (token : SourceToken) (bindings : NonEmpty.ArrayCorrectByConstruction.NonEmptyArray (LetBindingRecursive e)) :
      DoStatementRecursive e
    | Discard (expr : Expr e) : DoStatementRecursive e
    | Bind (binder : Binder e) (token : SourceToken) (expr : Expr e) : DoStatementRecursive e
    | Error (data : e) : DoStatementRecursive e
    deriving Repr, BEq
  structure DoBlockRecursive (e : Type) where
    keyword : SourceToken
    statements : NonEmpty.ArrayCorrectByConstruction.NonEmptyArray (DoStatementRecursive e)
    deriving Repr, BEq
  structure AdoBlockRecursive (e : Type) where
    keyword : SourceToken
    statements : Array (DoStatementRecursive e)
    in_ : SourceToken
    result : Expr e
    deriving Repr, BEq
  structure RecordAccessorRecursive (e : Type) where
    expr : Expr e
    dot : SourceToken
    path : Separated (Name Label)
    deriving Repr, BEq
  inductive RecordUpdateRecursive (e : Type) : Type where
    | Leaf (label : Name Label) (token : SourceToken) (expr : Expr e) : RecordUpdateRecursive e
    | Branch (label : Name Label) (updates : DelimitedNonEmpty (RecordUpdateRecursive e)) : RecordUpdateRecursive e
    deriving Repr, BEq
  inductive AppSpineRecursive (e : Type) : Type where
    | Type_ (token : SourceToken) (type_ : Type_ e) : AppSpineRecursive e
    | Term (expr : Expr e) : AppSpineRecursive e
    deriving Repr, BEq
  structure LambdaRecursive (e : Type) where
    symbol : SourceToken
    binders : NonEmpty.ArrayCorrectByConstruction.NonEmptyArray (Binder e)
    arrow : SourceToken
    body : Expr e
    deriving Repr, BEq
  structure IfThenElseRecursive (e : Type) where
    keyword : SourceToken
    cond : Expr e
    then_ : SourceToken
    true_ : Expr e
    else_ : SourceToken
    false_ : Expr e
    deriving Repr, BEq
  structure CaseOfRecursive (e : Type) where
    keyword : SourceToken
    head : Separated (Expr e)
    of : SourceToken
    branches : NonEmpty.ArrayCorrectByConstruction.NonEmptyArray (Separated (Binder e) × GuardedRecursive e)
    deriving Repr, BEq
  structure LetInRecursive (e : Type) where
    keyword : SourceToken
    bindings : NonEmpty.ArrayCorrectByConstruction.NonEmptyArray (LetBindingRecursive e)
    in_ : SourceToken
    body : Expr e
    deriving Repr, BEq
  inductive Expr (e : Type) : Type where
    | Hole (name : Name Ident) : Expr e
    | Section (token : SourceToken) : Expr e
    | Ident (name : QualifiedName Ident) : Expr e
    | Constructor (name : QualifiedName Proper) : Expr e
    | Boolean (token : SourceToken) (val : Bool) : Expr e
    | Char (token : SourceToken) (val : Char) : Expr e
    | String (token : SourceToken) (val : String) : Expr e
    | Int (token : SourceToken) (val : IntValue) : Expr e
    | Number (token : SourceToken) (val : Float) : Expr e
    | Array (items : Delimited (Expr e)) : Expr e
    | Record (fields : Delimited (RecordLabeled (Expr e))) : Expr e
    | Parens (wrapped : Wrapped (Expr e)) : Expr e
    | Typed (expr : Expr e) (token : SourceToken) (type_ : Type_ e) : Expr e
    |
    Infix (head : Expr e) (tail : NonEmpty.ArrayCorrectByConstruction.NonEmptyArray (Wrapped (Expr e) × Expr e)) :
      Expr e
    |
    Op (head : Expr e) (ops : NonEmpty.ArrayCorrectByConstruction.NonEmptyArray (QualifiedName Operator × Expr e)) :
      Expr e
    | OpName (name : QualifiedName Operator) : Expr e
    | Negate (token : SourceToken) (expr : Expr e) : Expr e
    | RecordAccessor (data : RecordAccessorRecursive e) : Expr e
    | RecordUpdate (expr : Expr e) (updates : DelimitedNonEmpty (RecordUpdateRecursive e)) : Expr e
    | App (fn : Expr e) (args : NonEmpty.ArrayCorrectByConstruction.NonEmptyArray (AppSpineRecursive e)) : Expr e
    | Lambda (data : LambdaRecursive e) : Expr e
    | If (data : IfThenElseRecursive e) : Expr e
    | Case (data : CaseOfRecursive e) : Expr e
    | Let (data : LetInRecursive e) : Expr e
    | Do (data : DoBlockRecursive e) : Expr e
    | Ado (data : AdoBlockRecursive e) : Expr e
    | Error (data : e) : Expr e
    deriving Repr, BEq
end-/
#guard_msgs in
set_option linter.unusedVariables false in
generate_fixed_mutual?
  generate_fixed PatternGuardRecursive (e : Type) from PatternGuardF
    fill expr_e with (Expr e)
    deriving Repr, BEq

  generate_fixed LetBindingRecursive (e : Type) from LetBindingF
    fill valueBindingFields_e with (ValueBindingFieldsRecursive e)
    fill where_e with (WhereRecursive e)
    deriving Repr, BEq

  generate_fixed WhereRecursive (e : Type) from WhereF
    fill expr_e with (Expr e)
    fill letBinding_e with (LetBindingRecursive e)
    deriving Repr, BEq

  generate_fixed GuardedRecursive (e : Type) from GuardedF
    fill where_e with (WhereRecursive e)
    fill guardedExpr_e with (GuardedExprRecursive e)
    deriving Repr, BEq

  generate_fixed GuardedExprRecursive (e : Type) from GuardedExprF
    fill patternGuard_e with (PatternGuardRecursive e)
    fill where_e with (WhereRecursive e)
    deriving Repr, BEq

  generate_fixed ValueBindingFieldsRecursive (e : Type) from ValueBindingFieldsF
    fill guardedExpr_e with (GuardedRecursive e)
    deriving Repr, BEq

  generate_fixed DoStatementRecursive (e : Type) from DoStatementF
    fill expr_e with (Expr e)
    fill letBindingRecursive_e with (LetBindingRecursive e)
    deriving Repr, BEq

  generate_fixed DoBlockRecursive (e : Type) from DoBlockF
    fill doStatement_e with (DoStatementRecursive e)
    deriving Repr, BEq

  generate_fixed AdoBlockRecursive (e : Type) from AdoBlockF
    fill expr_e with (Expr e)
    fill doStatement_e with (DoStatementRecursive e)
    deriving Repr, BEq

  generate_fixed RecordAccessorRecursive (e : Type) from RecordAccessorF
    fill expr_e with (Expr e)
    deriving Repr, BEq

  generate_fixed RecordUpdateRecursive (e : Type) from RecordUpdateF
    fill expr_e with (Expr e)
    fill self with (RecordUpdateRecursive e)
    deriving Repr, BEq

  generate_fixed AppSpineRecursive (e : Type) from AppSpineF
    fill expr_e with (Expr e)
    deriving Repr, BEq

  generate_fixed LambdaRecursive (e : Type) from LambdaF
    fill expr_e with (Expr e)
    deriving Repr, BEq

  generate_fixed IfThenElseRecursive (e : Type) from IfThenElseF
    fill expr_e with (Expr e)
    deriving Repr, BEq

  generate_fixed CaseOfRecursive (e : Type) from CaseOfF
    fill expr_e with (Expr e)
    fill guardedRecursive_e with (GuardedRecursive e)
    deriving Repr, BEq

  generate_fixed LetInRecursive (e : Type) from LetInF
    fill expr_e with (Expr e)
    fill letBindingRecursive_e with (LetBindingRecursive e)
    deriving Repr, BEq

  generate_fixed Expr (e : Type) from ExprF
    fill expr_e with (Expr e)
    fill doBlock with (DoBlockRecursive e)
    fill adoBlock with (AdoBlockRecursive e)
    fill guardedRecursive_e with (GuardedRecursive e)
    fill letBindingRecursive_e with (LetBindingRecursive e)
    fill recordAccessor_e with (RecordAccessorRecursive e)
    fill recordUpdate_e with (RecordUpdateRecursive e)
    fill appSpine_e with (AppSpineRecursive e)
    fill lambda_e with (LambdaRecursive e)
    fill ifThenElse_e with (IfThenElseRecursive e)
    fill caseOf_e with (CaseOfRecursive e)
    fill letIn_e with (LetInRecursive e)
    deriving Repr, BEq
end_generate_fixed_mutual


end PurescriptLanguageCstParser.Types
