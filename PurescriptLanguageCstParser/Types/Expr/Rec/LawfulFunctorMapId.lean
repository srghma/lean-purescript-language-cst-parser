module

import NonEmpty.CorrectByConstruction.Array
import NonEmpty.String
import Aesop
import PurescriptLanguageCstParser.Types.PType
public import PurescriptLanguageCstParser.Types.Expr.Leafs
public import PurescriptLanguageCstParser.Types.Expr.Rec.Basic
public import PurescriptLanguageCstParser.Types.Expr.Rec.Simp
public import PurescriptLanguageCstParser.Types.Expr.Rec.Functor
@[expose] public section
namespace PurescriptLanguageCstParser.Types

open NonEmpty.CorrectByConstruction.Array
open NonEmpty.String
open PurescriptLanguageCstParser.Types

-- ╔══════════════════════════════════════════════════════════════════╗
-- ║  id_map theorems                                                 ║
-- ╚══════════════════════════════════════════════════════════════════╝
set_option linter.unreachableTactic false in
set_option linter.unusedSimpArgs false in
mutual
  theorem Expr.map_id {e : Type} (expr : Expr e) : Expr.map id expr = expr := by
    match expr with
    | .Hole _ | .Section _ | .Ident _ | .Constructor _ | .Boolean _ _ | .Char _ _ | .String _ _ | .Int _ _ | .Number _ _ | .OpName _ =>
        unfold Expr.map; rfl
    | .Error d =>
        unfold Expr.map; dsimp;
    | .Parens w =>
        unfold Expr.map; congr; cases w; congr; exact Expr.map_id _
    | .Typed e' t ty =>
        unfold Expr.map; congr; exact Expr.map_id e'; exact Type_.map_id _
    | .Negate t e' =>
        unfold Expr.map; congr; exact Expr.map_id e'
    | .Array items =>
        unfold Expr.map; congr; exact Expr.mapDelimited_id items
    | .Record fields =>
        unfold Expr.map; congr; exact Expr.mapDelimitedRL_id fields
    | .Infix head tail =>
        unfold Expr.map; congr
        · exact Expr.map_id head
        · have h : (fun x : { x // x ∈ tail } =>
                match x with
                | ⟨(w, e_1), _hmem⟩ =>
                    ({ open_ := w.open_, value := Expr.map id w.value, close := w.close }, Expr.map id e_1)) =
              fun x => x.val := by
            funext ⟨⟨w, e'⟩, hmem⟩
            simp only [Expr.map_id]
          rw [h, NonEmptyArray.attach_map_val]
    | .Op head ops =>
        unfold Expr.map; congr
        · exact Expr.map_id head
        · have h : (fun x : { x // x ∈ ops } =>
                match x with
                | ⟨(n, e_1), _hmem⟩ => (n, Expr.map id e_1)) =
              fun x => x.val := by
            funext ⟨⟨n, e'⟩, hmem⟩
            simp only [Expr.map_id]
          rw [h, NonEmptyArray.attach_map_val]
    | .RecordAccessor d =>
        unfold Expr.map; congr; exact RecordAccessorRecursive.map_id d
    | .RecordUpdate e' upd =>
        unfold Expr.map; congr
        · exact Expr.map_id e'
        · have h : (fun x : { x // x ∈ upd } =>
                RecordUpdateRecursive.map id x.val) =
              fun x => x.val := by
            funext ⟨u, hmem⟩
            exact RecordUpdateRecursive.map_id u
          rw [h, DelimitedNonEmpty.attach_map_val]
    | .App fn args =>
        unfold Expr.map; congr
        · exact Expr.map_id fn
        · have h : (fun x : { x // x ∈ args } =>
                AppSpineRecursive.map id x.val) =
              fun x => x.val := by
            funext ⟨s, hmem⟩
            exact AppSpineRecursive.map_id s
          rw [h, NonEmptyArray.attach_map_val]
    | .Lambda d =>
        unfold Expr.map; congr; exact LambdaRecursive.map_id d
    | .If d =>
        unfold Expr.map; congr; exact IfThenElseRecursive.map_id d
    | .Case d =>
        unfold Expr.map; congr; exact CaseOfRecursive.map_id d
    | .Let d =>
        unfold Expr.map; congr; exact LetInRecursive.map_id d
    | .Do d =>
        unfold Expr.map; congr; exact DoBlockRecursive.map_id d
    | .Ado d =>
        unfold Expr.map; congr; exact AdoBlockRecursive.map_id d
  termination_by sizeOf expr
  decreasing_by
    all_goals simp_wf
    all_goals try decreasing_trivial
    · sorry
    ·
      simp_all
      sorry
    · sorry
    ·
      simp_all
      sorry

  theorem Expr.mapDelimited_id {e : Type} (d : Delimited (Expr e)) : Expr.mapDelimited id d = d := by
    cases d with | mk w =>
    cases w with | mk o v c =>
    cases v with
    | none => simp_all only [Expr.mapDelimited.eq_1]
    | some s =>
        unfold Expr.mapDelimited
        simp_all only [Expr.mapSep.eq_1, Delimited.mk.injEq, Wrapped.mk.injEq, Option.some.injEq, and_true, true_and]
        sorry
  termination_by sizeOf d
  decreasing_by simp_all

  theorem Expr.mapSep_id {e : Type} (s : Separated (Expr e)) : Expr.mapSep id s = s := by
    cases s; rename_i head tail
    simp only [Expr.mapSep, Separated.mk.injEq]
    refine ⟨Expr.map_id head, ?_⟩
    have h : (fun x : { x // x ∈ tail } => (x.val.1, Expr.map id x.val.2)) = fun x => id x.val := by
      funext ⟨⟨tok, e'⟩, hmem⟩
      have ih_e := Expr.map_id e'
      simp only [ih_e, id_eq]
    rw [h, Array.attach_map_val]
    exact Array.map_id _
  termination_by sizeOf s
  decreasing_by
    all_goals simp_wf
    all_goals try decreasing_trivial
    · sorry

  theorem Expr.mapDelimitedRL_id {e : Type} (d : Delimited (RecordLabeled (Expr e))) : Expr.mapDelimitedRL id d = d := by
    cases d; rename_i w
    cases w with | mk open_ value close =>
    cases value with
    | none => simp only [Expr.mapDelimitedRL]
    | some s =>
      simp only [Expr.mapDelimitedRL]
      have h := Expr.mapSepRL_id s
      simp only [h]
  termination_by sizeOf d
  decreasing_by
    all_goals simp_wf
    all_goals try decreasing_trivial


  theorem Expr.mapSepRL_id {e : Type} (s : Separated (RecordLabeled (Expr e))) : Expr.mapSepRL id s = s := by
    cases s; rename_i head tail
    simp only [Expr.mapSepRL, Separated.mk.injEq]
    refine ⟨Expr.mapRL_id head, ?_⟩
    have h : (fun x : { x // x ∈ tail } => (x.val.1, Expr.mapRL id x.val.2)) = fun x => id x.val := by
      funext ⟨⟨tok, rl⟩, hmem⟩
      have ih_rl := Expr.mapRL_id rl
      simp only [ih_rl, id_eq]
    rw [h, Array.attach_map_val]
    exact Array.map_id _
  termination_by sizeOf s
  decreasing_by
    all_goals simp_wf
    all_goals try decreasing_trivial
    · sorry


  theorem Expr.mapRL_id {e : Type} (rl : RecordLabeled (Expr e)) : Expr.mapRL id rl = rl := by
    match rl with
    | .Pun n => unfold Expr.mapRL; rfl
    | .Field l sep e' =>
        unfold Expr.mapRL; congr; exact Expr.map_id e'
  termination_by sizeOf rl
  decreasing_by
    all_goals simp_wf
    all_goals try decreasing_trivial


  theorem RecordAccessorRecursive.map_id {e : Type} (d : RecordAccessorRecursive e) : RecordAccessorRecursive.map id d = d := by
    cases d; unfold RecordAccessorRecursive.map; congr; exact Expr.map_id _
  termination_by sizeOf d
  decreasing_by
    all_goals simp_wf
    all_goals try decreasing_trivial

  theorem RecordUpdateRecursive.map_id {e : Type} (u : RecordUpdateRecursive e) : RecordUpdateRecursive.map id u = u := by
    match u with
    | .Leaf l t e' =>
        unfold RecordUpdateRecursive.map; congr; exact Expr.map_id e'
    | .Branch l updates =>
        unfold RecordUpdateRecursive.map; congr
        -- have h : RecordUpdateRecursive.map id = id := funext RecordUpdateRecursive.map_id
        -- simp? [h, DelimitedNonEmpty.id_map]
        simp_all only [DelimitedNonEmpty.map, DelimitedNonEmpty.attach, DelimitedNonEmpty.attachWith, Separated.map]
        sorry
  termination_by sizeOf u
  decreasing_by
    all_goals simp_wf
    all_goals try decreasing_trivial

  theorem AppSpineRecursive.map_id {e : Type} (s : AppSpineRecursive e) : AppSpineRecursive.map id s = s := by
    match s with
    | .Type_ t ty => unfold AppSpineRecursive.map; congr; exact Type_.map_id _
    | .Term e' => unfold AppSpineRecursive.map; congr; exact Expr.map_id e'
  termination_by sizeOf s
  decreasing_by
    all_goals simp_wf
    all_goals try decreasing_trivial

  theorem LambdaRecursive.map_id {e : Type} (d : LambdaRecursive e) : LambdaRecursive.map id d = d := by
    have hb : Binder.map id = (id : Binder e → Binder e) := funext Binder.map_id
    cases d; unfold LambdaRecursive.map; congr
    · simp only [NonEmptyArray.map, Binder.map_id, hb, Array.map_id_fun, id_eq]
    · exact Expr.map_id _
  termination_by sizeOf d
  decreasing_by
    all_goals simp_wf
    all_goals try decreasing_trivial

  theorem IfThenElseRecursive.map_id {e : Type} (d : IfThenElseRecursive e) : IfThenElseRecursive.map id d = d := by
    cases d; unfold IfThenElseRecursive.map; congr
    · exact Expr.map_id _
    · exact Expr.map_id _
    · exact Expr.map_id _
  termination_by sizeOf d
  decreasing_by
    all_goals simp_wf
    all_goals try decreasing_trivial

  theorem CaseOfRecursive.map_id {e : Type} (data : CaseOfRecursive e) : CaseOfRecursive.map id data = data := by
    cases data
    rename_i keyword head of_ branches
    simp only [CaseOfRecursive.map, CaseOfRecursive.mk.injEq, true_and]
    refine ⟨Expr.mapSep_id head, ?_⟩
    have h : (fun x : { x // x ∈ branches } =>
          (x.val.1.map (Binder.map id), GuardedRecursive.map id x.val.2)) = fun x => x.val := by
      funext ⟨⟨b, g⟩, _⟩
      have hb : Binder.map id = (id : Binder e → Binder e) := funext Binder.map_id
      simp only [hb, Separated.map_id_fun, GuardedRecursive.map_id, id_eq]
    rw [h, NonEmptyArray.attach_map_val]
  termination_by sizeOf data
  decreasing_by
    all_goals simp_wf
    all_goals simp_all only
    all_goals try decreasing_trivial
    · cases data
      sorry

  theorem GuardedRecursive.map_id {e : Type} (g : GuardedRecursive e) : GuardedRecursive.map id g = g := by
    cases g
    · simp only [GuardedRecursive.map, GuardedRecursive.Unconditional.injEq, true_and]
      exact WhereRecursive.map_id _
    · rename_i patterns
      simp only [GuardedRecursive.map, GuardedRecursive.Guarded.injEq]
      have h : (fun b : { x // x ∈ patterns } => GuardedExprRecursive.map id b.val) =
          fun b => b.val := by
        funext ⟨b, _⟩
        exact GuardedExprRecursive.map_id b
      rw [h, NonEmptyArray.attach_map_val]
  termination_by sizeOf g
  decreasing_by
    all_goals simp_wf
    all_goals try decreasing_trivial
    · sorry

  theorem GuardedExprRecursive.map_id {e : Type} (d : GuardedExprRecursive e) : GuardedExprRecursive.map id d = d := by
    cases d with | mk bar patterns separator where_ =>
    unfold GuardedExprRecursive.map; congr
    · -- have h : PatternGuardRecursive.map id = id := funext PatternGuardRecursive.map_id
      -- simp? [h, Separated.id_map]
      simp_all only [Separated.map, PatternGuardRecursive.map.eq_1, Binder.map_id, Option.attach_map_subtype_val]
      sorry
    · exact WhereRecursive.map_id where_
  termination_by sizeOf d
  decreasing_by
    all_goals simp_wf
    all_goals try decreasing_trivial

  theorem PatternGuardRecursive.map_id {e : Type} (d : PatternGuardRecursive e) : PatternGuardRecursive.map id d = d := by
    cases d with | mk binder expr =>
    unfold PatternGuardRecursive.map; congr
    · have h : (fun x : { x // x ∈ binder } =>
              match x with
              | ⟨(b, t), _ht⟩ => (Binder.map id b, t)) =
            fun x => x.val := by
        funext ⟨⟨b, t⟩, _⟩
        simp only [Binder.map_id]
      -- rw [h]
      -- exact Option.attach_map_val binder
      simp_all only [Binder.map_id, Option.attach_map_subtype_val]
    · exact Expr.map_id expr
  termination_by sizeOf d
  decreasing_by
    all_goals simp_wf
    all_goals try decreasing_trivial
    · sorry

  theorem LetInRecursive.map_id {e : Type} (d : LetInRecursive e) : LetInRecursive.map id d = d := by
    cases d with | mk kw bindings in_ body =>
    unfold LetInRecursive.map; congr
    · -- have h : LetBindingRecursive.map id = id := funext LetBindingRecursive.map_id
      -- simp? [h, NonEmptyArray.map_id]
      simp_all only [NonEmptyArray.map, Array.map_subtype]
      sorry
    · exact Expr.map_id body
  termination_by sizeOf d
  decreasing_by
    all_goals simp_wf
    all_goals try decreasing_trivial

  theorem LetBindingRecursive.map_id {e : Type} (b : LetBindingRecursive e) : LetBindingRecursive.map id b = b := by
    match b with
    | .Signature l => unfold LetBindingRecursive.map; congr; sorry -- exact Type_.id_map _
    | .Name fields => unfold LetBindingRecursive.map; congr; exact ValueBindingFieldsRecursive.map_id fields
    | .Pattern b' t w => unfold LetBindingRecursive.map; congr; exact Binder.map_id b'; exact WhereRecursive.map_id w
    | .Error d => unfold LetBindingRecursive.map; rfl
  termination_by sizeOf b
  decreasing_by
    all_goals simp_wf
    all_goals try decreasing_trivial
    · sorry

  theorem ValueBindingFieldsRecursive.map_id {e : Type} (d : ValueBindingFieldsRecursive e) : ValueBindingFieldsRecursive.map id d = d := by
    cases d with | mk name binders guarded =>
    unfold ValueBindingFieldsRecursive.map; congr
    · -- have h : Binder.map id = id := funext Binder.map_id
      -- simp? [h, Array.map_id]
      grind =>
        instantiate only [= Array.size_map]
        instantiate only [= Array.size_attach]
        sorry
    · exact GuardedRecursive.map_id guarded
  termination_by sizeOf d
  decreasing_by
    all_goals simp_wf
    all_goals try decreasing_trivial
    · sorry

  theorem WhereRecursive.map_id {e : Type} (d : WhereRecursive e) : WhereRecursive.map id d = d := by
    cases d with | mk expr bindings =>
    unfold WhereRecursive.map; congr
    · exact Expr.map_id expr
    · cases bindings with
      | none => rfl
      | some p =>
          cases p with | mk t bs =>
          congr
          -- have h : LetBindingRecursive.map id = id := funext LetBindingRecursive.map_id
          -- simp? [h, NonEmptyArray.map_id]
          simp_all only [NonEmptyArray.map, Array.map_subtype, Option.attach_some, Option.map_some, Option.some.injEq,
            Prod.mk.injEq, true_and]
          sorry
  termination_by sizeOf d
  decreasing_by
    all_goals simp_wf
    all_goals try decreasing_trivial

  theorem DoBlockRecursive.map_id {e : Type} (d : DoBlockRecursive e) : DoBlockRecursive.map id d = d := by
    cases d; unfold DoBlockRecursive.map; congr
    -- have h : DoStatementRecursive.map id = id := funext DoStatementRecursive.map_id
    -- simp? [h, NonEmptyArray.map_id]
    simp_all only [NonEmptyArray.map, Array.map_subtype]
    sorry
  termination_by sizeOf d
  decreasing_by
    all_goals simp_wf
    all_goals try decreasing_trivial
    · sorry

  theorem AdoBlockRecursive.map_id {e : Type} (data : AdoBlockRecursive e) : AdoBlockRecursive.map id data = data := by
    cases data
    rename_i keyword statements in_ result
    simp only [AdoBlockRecursive.map]
    have h : (fun s : { x // x ∈ statements } => DoStatementRecursive.map id s.val) = fun s => s.val := by
      funext ⟨s, _⟩
      exact DoStatementRecursive.map_id s
    rw [h]
    have :=
      congrArg
        (fun sts => ({ keyword := keyword, statements := sts, in_ := in_, result := Expr.map id result } :
          AdoBlockRecursive e))
        (Array.attach_map_val statements (f := fun st => DoStatementRecursive.map id st))
    simp only [Array.map_subtype, Array.unattach_attach, Array.map_id_fun', id_eq, Expr.map_id]
    termination_by sizeOf data
  decreasing_by
    all_goals simp_wf
    all_goals try decreasing_trivial
    · sorry

  theorem DoStatementRecursive.map_id {e : Type} (s : DoStatementRecursive e) : DoStatementRecursive.map id s = s := by
    match s with
    | .Let t bs =>
        unfold DoStatementRecursive.map; congr
        -- have h : LetBindingRecursive.map id = id := funext LetBindingRecursive.map_id
        -- simp? [h, NonEmptyArray.map_id]
        simp_all only [NonEmptyArray.map, Array.map_subtype]
        sorry
    | .Discard e' => unfold DoStatementRecursive.map; congr; exact Expr.map_id e'
    | .Bind b t e' => unfold DoStatementRecursive.map; congr; exact Binder.map_id b; exact Expr.map_id e'
    | .Error d => unfold DoStatementRecursive.map; rfl
  termination_by sizeOf s
  decreasing_by
    all_goals simp_wf
    all_goals try decreasing_trivial
end

end PurescriptLanguageCstParser.Types
