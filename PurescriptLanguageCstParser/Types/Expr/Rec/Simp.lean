module

import NonEmpty.ArrayCorrectByConstruction
-- import NonEmpty.String
-- import Aesop
import PurescriptLanguageCstParser.Types.PType.Basic
public import PurescriptLanguageCstParser.Types.Expr.Leafs
public import PurescriptLanguageCstParser.Types.Expr.Rec.Basic
@[expose] public section
namespace PurescriptLanguageCstParser.Types

open NonEmpty.ArrayCorrectByConstruction
-- open NonEmpty.String
-- open PurescriptLanguageCstParser.Types

-- ╔══════════════════════════════════════════════════════════════════╗
-- ║  sizeOf theorems                                                 ║
-- ╚══════════════════════════════════════════════════════════════════╝

@[simp] theorem PatternGuardRecursive.sizeOf_expr_lt {e : Type} (data : PatternGuardRecursive e) : sizeOf data.expr < sizeOf data := by
  cases data; decreasing_trivial

@[simp] theorem LetBindingRecursive.sizeOf_Signature_labeled_lt {e : Type} (labeled : Labeled (PurescriptLanguageCstParser.Types.Name Ident) (Type_ e)) : sizeOf labeled < sizeOf (LetBindingRecursive.Signature (e := e) labeled) := by
  simp only [Signature.sizeOf_spec, Nat.lt_add_left_iff_pos, Nat.lt_add_one];

@[simp] theorem LetBindingRecursive.sizeOf_Name_fields_lt {e : Type} (fields : ValueBindingFieldsRecursive e) : sizeOf fields < sizeOf (LetBindingRecursive.Name (e := e) fields) := by
  decreasing_trivial

@[simp] theorem LetBindingRecursive.sizeOf_Pattern_binder_lt {e : Type} (binder : Binder e) (token : SourceToken) (where_ : WhereRecursive e) : sizeOf binder < sizeOf (LetBindingRecursive.Pattern (e := e) binder token where_) := by
  decreasing_trivial

@[simp] theorem LetBindingRecursive.sizeOf_Pattern_where_lt {e : Type} (binder : Binder e) (token : SourceToken) (where_ : WhereRecursive e) : sizeOf where_ < sizeOf (LetBindingRecursive.Pattern (e := e) binder token where_) := by
  decreasing_trivial

@[simp] theorem WhereRecursive.sizeOf_expr_lt {e : Type} (data : WhereRecursive e) : sizeOf data.expr < sizeOf data := by
  cases data; decreasing_trivial

@[simp] theorem WhereRecursive.sizeOf_bindings_lt {e : Type} (data : WhereRecursive e) : sizeOf data.bindings < sizeOf data := by
  cases data; decreasing_trivial

@[simp] theorem GuardedRecursive.sizeOf_Unconditional_where_lt {e : Type} (token : SourceToken) (where_ : WhereRecursive e) : sizeOf where_ < sizeOf (GuardedRecursive.Unconditional (e := e) token where_) := by
  decreasing_trivial

@[simp] theorem GuardedRecursive.sizeOf_Guarded_branches_lt {e : Type} (branches : NonEmptyArray (GuardedExprRecursive e)) : sizeOf branches < sizeOf (GuardedRecursive.Guarded (e := e) branches) := by
  decreasing_trivial

@[simp] theorem GuardedExprRecursive.sizeOf_patterns_lt {e : Type} (data : GuardedExprRecursive e) : sizeOf data.patterns < sizeOf data := by
  cases data; decreasing_trivial

@[simp] theorem GuardedExprRecursive.sizeOf_where_lt {e : Type} (data : GuardedExprRecursive e) : sizeOf data.where_ < sizeOf data := by
  cases data; decreasing_trivial

@[simp] theorem ValueBindingFieldsRecursive.sizeOf_guarded_lt {e : Type} (data : ValueBindingFieldsRecursive e) : sizeOf data.guarded < sizeOf data := by
  cases data; decreasing_trivial

@[simp] theorem DoStatementRecursive.sizeOf_Let_bindings_lt {e : Type} (token : SourceToken) (bindings : NonEmptyArray (LetBindingRecursive e)) : sizeOf bindings < sizeOf (DoStatementRecursive.Let (e := e) token bindings) := by
  decreasing_trivial

@[simp] theorem DoStatementRecursive.sizeOf_Discard_expr_lt {e : Type} (expr : Expr e) : sizeOf expr < sizeOf (DoStatementRecursive.Discard (e := e) expr) := by
  decreasing_trivial

@[simp] theorem DoStatementRecursive.sizeOf_Bind_expr_lt {e : Type} (binder : Binder e) (token : SourceToken) (expr : Expr e) : sizeOf expr < sizeOf (DoStatementRecursive.Bind (e := e) binder token expr) := by
  decreasing_trivial

@[simp] theorem DoBlockRecursive.sizeOf_statements_lt {e : Type} (data : DoBlockRecursive e) : sizeOf data.statements < sizeOf data := by
  cases data; decreasing_trivial

@[simp] theorem AdoBlockRecursive.sizeOf_statements_lt {e : Type} (data : AdoBlockRecursive e) : sizeOf data.statements < sizeOf data := by
  cases data; decreasing_trivial

@[simp] theorem AdoBlockRecursive.sizeOf_result_lt {e : Type} (data : AdoBlockRecursive e) : sizeOf data.result < sizeOf data := by
  cases data; decreasing_trivial

@[simp] theorem RecordAccessorRecursive.sizeOf_expr_lt {e : Type} (data : RecordAccessorRecursive e) : sizeOf data.expr < sizeOf data := by
  cases data; decreasing_trivial

@[simp] theorem RecordUpdateRecursive.sizeOf_Leaf_expr_lt {e : Type} (label : Name Label) (token : SourceToken) (expr : Expr e) : sizeOf expr < sizeOf (RecordUpdateRecursive.Leaf (e := e) label token expr) := by
  decreasing_trivial

@[simp] theorem RecordUpdateRecursive.sizeOf_Branch_updates_lt {e : Type} (label : Name Label) (updates : DelimitedNonEmpty (RecordUpdateRecursive e)) : sizeOf updates < sizeOf (RecordUpdateRecursive.Branch (e := e) label updates) := by
  decreasing_trivial

@[simp] theorem AppSpineRecursive.sizeOf_Term_expr_lt {e : Type} (expr : Expr e) : sizeOf expr < sizeOf (AppSpineRecursive.Term (e := e) expr) := by
  decreasing_trivial

@[simp] theorem LambdaRecursive.sizeOf_body_lt {e : Type} (data : LambdaRecursive e) : sizeOf data.body < sizeOf data := by
  cases data; decreasing_trivial

@[simp] theorem IfThenElseRecursive.sizeOf_cond_lt {e : Type} (data : IfThenElseRecursive e) : sizeOf data.cond < sizeOf data := by
  cases data; decreasing_trivial

@[simp] theorem IfThenElseRecursive.sizeOf_true_lt {e : Type} (data : IfThenElseRecursive e) : sizeOf data.true_ < sizeOf data := by
  cases data; decreasing_trivial

@[simp] theorem IfThenElseRecursive.sizeOf_false_lt {e : Type} (data : IfThenElseRecursive e) : sizeOf data.false_ < sizeOf data := by
  cases data; decreasing_trivial

@[simp] theorem CaseOfRecursive.sizeOf_head_lt {e : Type} (data : CaseOfRecursive e) : sizeOf data.head < sizeOf data := by
  cases data; decreasing_trivial

@[simp] theorem CaseOfRecursive.sizeOf_branches_lt {e : Type} (data : CaseOfRecursive e) : sizeOf data.branches < sizeOf data := by
  cases data; decreasing_trivial

@[simp] theorem LetInRecursive.sizeOf_bindings_lt {e : Type} (data : LetInRecursive e) : sizeOf data.bindings < sizeOf data := by
  cases data; decreasing_trivial

@[simp] theorem LetInRecursive.sizeOf_body_lt {e : Type} (data : LetInRecursive e) : sizeOf data.body < sizeOf data := by
  cases data; decreasing_trivial

@[simp] theorem Expr.sizeOf_Array_items_lt {e : Type} (items : Delimited (Expr e)) : sizeOf items < sizeOf (Expr.Array (e := e) items) := by
  cases items; decreasing_trivial

@[simp] theorem Expr.sizeOf_Record_fields_lt {e : Type} (fields : Delimited (RecordLabeled (Expr e))) : sizeOf fields < sizeOf (Expr.Record (e := e) fields) := by
  cases fields; decreasing_trivial

@[simp] theorem Expr.sizeOf_Parens_wrapped_lt {e : Type} (wrapped : Wrapped (Expr e)) : sizeOf wrapped < sizeOf (Expr.Parens (e := e) wrapped) := by
  cases wrapped; decreasing_trivial

@[simp] theorem Expr.sizeOf_Typed_expr_lt {e : Type} (expr : Expr e) (token : SourceToken) (type_ : Type_ e) : sizeOf expr < sizeOf (Expr.Typed (e := e) expr token type_) := by
  decreasing_trivial

@[simp] theorem Expr.sizeOf_Infix_head_lt {e : Type} (head : Expr e) (tail : NonEmptyArray (Wrapped (Expr e) × Expr e)) : sizeOf head < sizeOf (Expr.Infix (e := e) head tail) := by
  decreasing_trivial

@[simp] theorem Expr.sizeOf_Infix_tail_lt {e : Type} (head : Expr e) (tail : NonEmptyArray (Wrapped (Expr e) × Expr e)) : sizeOf tail < sizeOf (Expr.Infix (e := e) head tail) := by
  decreasing_trivial

@[simp] theorem Expr.sizeOf_Op_head_lt {e : Type} (head : Expr e) (ops : NonEmptyArray (QualifiedName Operator × Expr e)) : sizeOf head < sizeOf (Expr.Op (e := e) head ops) := by
  decreasing_trivial

@[simp] theorem Expr.sizeOf_Op_ops_lt {e : Type} (head : Expr e) (ops : NonEmptyArray (QualifiedName Operator × Expr e)) : sizeOf ops < sizeOf (Expr.Op (e := e) head ops) := by
  decreasing_trivial

@[simp] theorem Expr.sizeOf_Negate_expr_lt {e : Type} (token : SourceToken) (expr : Expr e) : sizeOf expr < sizeOf (Expr.Negate (e := e) token expr) := by
  decreasing_trivial

@[simp] theorem Expr.sizeOf_RecordAccessor_data_lt {e : Type} (data : RecordAccessorRecursive e) : sizeOf data < sizeOf (Expr.RecordAccessor (e := e) data) := by
  decreasing_trivial

@[simp] theorem Expr.sizeOf_RecordUpdate_expr_lt {e : Type} (expr : Expr e) (updates : DelimitedNonEmpty (RecordUpdateRecursive e)) : sizeOf expr < sizeOf (Expr.RecordUpdate (e := e) expr updates) := by
  decreasing_trivial

@[simp] theorem Expr.sizeOf_RecordUpdate_updates_lt {e : Type} (expr : Expr e) (updates : DelimitedNonEmpty (RecordUpdateRecursive e)) : sizeOf updates < sizeOf (Expr.RecordUpdate (e := e) expr updates) := by
  decreasing_trivial

@[simp] theorem Expr.sizeOf_App_fn_lt {e : Type} (fn : Expr e) (args : NonEmptyArray (AppSpineRecursive e)) : sizeOf fn < sizeOf (Expr.App (e := e) fn args) := by
  decreasing_trivial

@[simp] theorem Expr.sizeOf_App_args_lt {e : Type} (fn : Expr e) (args : NonEmptyArray (AppSpineRecursive e)) : sizeOf args < sizeOf (Expr.App (e := e) fn args) := by
  decreasing_trivial

@[simp] theorem Expr.sizeOf_Lambda_data_lt {e : Type} (data : LambdaRecursive e) : sizeOf data < sizeOf (Expr.Lambda (e := e) data) := by
  decreasing_trivial

@[simp] theorem Expr.sizeOf_If_data_lt {e : Type} (data : IfThenElseRecursive e) : sizeOf data < sizeOf (Expr.If (e := e) data) := by
  decreasing_trivial

@[simp] theorem Expr.sizeOf_Case_data_lt {e : Type} (data : CaseOfRecursive e) : sizeOf data < sizeOf (Expr.Case (e := e) data) := by
  decreasing_trivial

@[simp] theorem Expr.sizeOf_Let_data_lt {e : Type} (data : LetInRecursive e) : sizeOf data < sizeOf (Expr.Let (e := e) data) := by
  decreasing_trivial

@[simp] theorem Expr.sizeOf_Do_data_lt {e : Type} (data : DoBlockRecursive e) : sizeOf data < sizeOf (Expr.Do (e := e) data) := by
  decreasing_trivial

@[simp] theorem Expr.sizeOf_Ado_data_lt {e : Type} (data : AdoBlockRecursive e) : sizeOf data < sizeOf (Expr.Ado (e := e) data) := by
  decreasing_trivial
