module

import NonEmpty.ArrayCorrectByConstruction
import NonEmpty.String
import Aesop
public import PurescriptLanguageCstParser.Types.PType
public import PurescriptLanguageCstParser.Types.Expr.Leafs
public import PurescriptLanguageCstParser.Types.Expr.Rec.Basic
meta import PurescriptLanguageCstParser.GenerateFixed

@[expose] public section

namespace PurescriptLanguageCstParser.Types

open NonEmpty.ArrayCorrectByConstruction
open NonEmpty.String
open PurescriptLanguageCstParser.Types

-- ╔══════════════════════════════════════════════════════════════════╗
-- ║  Map definitions                                                 ║
-- ╚══════════════════════════════════════════════════════════════════╝

mutual

  -- ── Expr ───────────────────────────────────────────────────────────
  @[simp] def Expr.map {e1 e2 : Type} (f : e1 → e2) : Expr e1 → Expr e2
    | .Hole n             => .Hole n
    | .Section t          => .Section t
    | .Ident n            => .Ident n
    | .Constructor n      => .Constructor n
    | .Boolean t v        => .Boolean t v
    | .Char t v           => .Char t v
    | .String t v => .String t v
    | .Int t v            => .Int t v
    | .Number t v         => .Number t v
    | .OpName n           => .OpName n
    | .Error d            => .Error (f d)
    | .Parens w           => .Parens { w with value := Expr.map f w.value }
    | .Typed e t ty       => .Typed (Expr.map f e) t (Type_.map f ty)
    | .Negate t e         => .Negate t (Expr.map f e)
    | .Array items        => .Array (Expr.mapDelimited f items)
    | .Record fields      => .Record (Expr.mapDelimitedRL f fields)
    | .Infix head tail    =>
        .Infix (Expr.map f head)
          (tail.attach.map (fun ⟨⟨w, e⟩, _hmem⟩ =>
            ({ w with value := Expr.map f w.value }, Expr.map f e)))
    | .Op head ops        =>
        .Op (Expr.map f head)
          (ops.attach.map (fun ⟨⟨n, e⟩, _hmem⟩ => (n, Expr.map f e)))
    | .RecordAccessor d   => .RecordAccessor (RecordAccessorRecursive.map f d)
    | .RecordUpdate e upd =>
        .RecordUpdate (Expr.map f e)
          (upd.attach.map (fun ⟨u, _hmem⟩ => RecordUpdateRecursive.map f u))
    | .App fn args        =>
        .App (Expr.map f fn)
          (args.attach.map (fun ⟨s, _hmem⟩ => AppSpineRecursive.map f s))
    | .Lambda d           => .Lambda  (LambdaRecursive.map f d)
    | .If d               => .If      (IfThenElseRecursive.map f d)
    | .Case d             => .Case    (CaseOfRecursive.map f d)
    | .Let d              => .Let     (LetInRecursive.map f d)
    | .Do d               => .Do      (DoBlockRecursive.map f d)
    | .Ado d              => .Ado     (AdoBlockRecursive.map f d)
  termination_by t => sizeOf t
  decreasing_by
    all_goals simp_wf
    all_goals try decreasing_trivial;
    -- Parens
    · have := Wrapped.sizeOf_value w; decreasing_trivial
    -- Typed
    · have := NonEmptyArray.sizeOf_lt_of_mem _hmem
      have := Wrapped.sizeOf_value w
      simp only [Prod.mk.sizeOf_spec] at *; omega
    -- Negate
    · have := NonEmptyArray.sizeOf_lt_of_mem _hmem
      simp only [Prod.mk.sizeOf_spec] at *; omega
    -- Array
    · have := NonEmptyArray.sizeOf_lt_of_mem _hmem
      simp only [Prod.mk.sizeOf_spec] at *; omega
    -- Record
    · have := DelimitedNonEmpty.sizeOf_attach_elem upd ⟨u, _hmem⟩
      simp only at *; omega
    -- Infix head
    · have := NonEmptyArray.sizeOf_lt_of_mem _hmem
      simp only at *; omega

  -- ── Delimited (Expr e) ─────────────────────────────────────────────
  @[simp] def Expr.mapDelimited {e1 e2} (f : e1 → e2) : Delimited (Expr e1) → Delimited (Expr e2)
    | .mk ⟨o, none,   c⟩ => .mk ⟨o, none, c⟩
    | .mk ⟨o, some s, c⟩ => .mk ⟨o, some (Expr.mapSep f s), c⟩
  termination_by d => sizeOf d
  decreasing_by
    simp only [Delimited.mk.sizeOf_spec, Wrapped.mk.sizeOf_spec,
               Option.some.sizeOf_spec] at *; omega

  -- ── Separated (Expr e) ─────────────────────────────────────────────
  @[simp] def Expr.mapSep {e1 e2} (f : e1 → e2) (s : Separated (Expr e1)) : Separated (Expr e2) :=
    { head := Expr.map f s.head
      tail := s.tail.attach.map (fun ⟨⟨tok, e⟩, _hmem⟩ => (tok, Expr.map f e)) }
  termination_by sizeOf s
  decreasing_by
    · exact Separated.sizeOf_head s
    · simp_wf
      obtain ⟨i, hi, h⟩ := Array.mem_iff_getElem.mp _hmem
      have : e = s.tail[i].2 := by simp only [h]
      rw [this]; exact s.sizeOf_tail_get i hi

  -- ── Delimited (RecordLabeled (Expr e)) ─────────────────────────────
  @[simp] def Expr.mapDelimitedRL {e1 e2} (f : e1 → e2)
      : Delimited (RecordLabeled (Expr e1)) → Delimited (RecordLabeled (Expr e2))
    | .mk ⟨o, none,   c⟩ => .mk ⟨o, none, c⟩
    | .mk ⟨o, some s, c⟩ => .mk ⟨o, some (Expr.mapSepRL f s), c⟩
  termination_by d => sizeOf d
  decreasing_by
    simp only [Delimited.mk.sizeOf_spec, Wrapped.mk.sizeOf_spec,
               Option.some.sizeOf_spec] at *; omega

  -- ── Separated (RecordLabeled (Expr e)) ─────────────────────────────
  @[simp] def Expr.mapSepRL {e1 e2} (f : e1 → e2)
      (s : Separated (RecordLabeled (Expr e1))) : Separated (RecordLabeled (Expr e2)) :=
    { head := Expr.mapRL f s.head
      tail := s.tail.attach.map (fun ⟨⟨tok, rl⟩, _hmem⟩ => (tok, Expr.mapRL f rl)) }
  termination_by sizeOf s
  decreasing_by
    · exact Separated.sizeOf_head s
    · simp_wf
      obtain ⟨i, hi, h⟩ := Array.mem_iff_getElem.mp _hmem
      have : rl = s.tail[i].2 := by simp only [h]
      rw [this]; exact s.sizeOf_tail_get i hi

  -- ── RecordLabeled (Expr e) ─────────────────────────────────────────
  @[simp] def Expr.mapRL {e1 e2} (f : e1 → e2) : RecordLabeled (Expr e1) → RecordLabeled (Expr e2)
    | .Pun n           => .Pun n
    | .Field l sep e'  => .Field l sep (Expr.map f e')
  termination_by rl => sizeOf rl
  decreasing_by
    simp_wf
    omega

  -- ── RecordAccessorRecursive ────────────────────────────────────────
  @[simp] def RecordAccessorRecursive.map {e1 e2 : Type} (f : e1 → e2)
      (data : RecordAccessorRecursive e1) : RecordAccessorRecursive e2 :=
    { expr := Expr.map f data.expr, dot := data.dot, path := data.path }
  termination_by sizeOf data
  decreasing_by
    simp_wf
    cases data; simp_wf
    omega

  -- ── RecordUpdateRecursive ──────────────────────────────────────────
  @[simp] def RecordUpdateRecursive.map {e1 e2 : Type} (f : e1 → e2)
      (u : RecordUpdateRecursive e1) : RecordUpdateRecursive e2 :=
    match u with
    | .Leaf l t e' => .Leaf l t (Expr.map f e')
    | .Branch l updates => .Branch l (updates.attach.map fun ⟨u', _hu'⟩ => RecordUpdateRecursive.map f u')
  termination_by sizeOf u
  decreasing_by
    all_goals simp_wf
    · omega
    · have : sizeOf u' < sizeOf updates := DelimitedNonEmpty.sizeOf_attach_elem updates ⟨u', _hu'⟩
      omega

  -- ── AppSpineRecursive ──────────────────────────────────────────────
  @[simp] def AppSpineRecursive.map {e1 e2 : Type} (f : e1 → e2)
      (s : AppSpineRecursive e1) : AppSpineRecursive e2 :=
    match s with
    | .Type_ t ty => .Type_ t (Type_.map f ty)
    | .Term e' => .Term (Expr.map f e')
  termination_by sizeOf s
  decreasing_by
    all_goals simp_wf

  -- ── LambdaRecursive ────────────────────────────────────────────────
  @[simp] def LambdaRecursive.map {e1 e2 : Type} (f : e1 → e2)
      (data : LambdaRecursive e1) : LambdaRecursive e2 :=
    { symbol := data.symbol, binders := data.binders.map (Binder.map f), arrow := data.arrow, body := Expr.map f data.body }
  termination_by sizeOf data
  decreasing_by
    simp_wf
    cases data; simp_wf
    omega

  -- ── IfThenElseRecursive ────────────────────────────────────────────
  @[simp] def IfThenElseRecursive.map {e1 e2 : Type} (f : e1 → e2)
      (data : IfThenElseRecursive e1) : IfThenElseRecursive e2 :=
    { keyword := data.keyword, cond := Expr.map f data.cond, then_ := data.then_, true_ := Expr.map f data.true_, else_ := data.else_, false_ := Expr.map f data.false_ }
  termination_by sizeOf data
  decreasing_by
    all_goals simp_wf
    all_goals cases data; simp_wf
    all_goals omega

  -- ── CaseOfRecursive ────────────────────────────────────────────────
  @[simp] def CaseOfRecursive.map {e1 e2 : Type} (f : e1 → e2)
      (data : CaseOfRecursive e1) : CaseOfRecursive e2 :=
    { keyword := data.keyword
      head := Expr.mapSep f data.head
      of := data.of
      branches := data.branches.attach.map (fun x => (x.val.1.map (Binder.map f), GuardedRecursive.map f x.val.2)) }
  termination_by sizeOf data
  decreasing_by
    all_goals simp_wf
    · cases data; simp_wf
      omega
    · cases data; simp_wf
      rename_i keyword head of_ branches
      have : sizeOf x.val < sizeOf branches := NonEmptyArray.sizeOf_lt_of_mem x.property
      have : sizeOf x.val.2 < sizeOf x.val := by
        cases x.val; simp_wf; omega
      omega

  -- ── GuardedRecursive ───────────────────────────────────────────────
  @[simp] def GuardedRecursive.map {e1 e2 : Type} (f : e1 → e2)
      (g : GuardedRecursive e1) : GuardedRecursive e2 :=
    match g with
    | .Unconditional t w => .Unconditional t (WhereRecursive.map f w)
    | .Guarded branches => .Guarded (branches.attach.map (fun ⟨b, _hb⟩ => GuardedExprRecursive.map f b))
  termination_by sizeOf g
  decreasing_by
    all_goals simp_wf
    · omega
    · have : sizeOf b < sizeOf branches := NonEmptyArray.sizeOf_lt_of_mem _hb
      omega

  -- ── GuardedExprRecursive ───────────────────────────────────────────
  @[simp] def GuardedExprRecursive.map {e1 e2 : Type} (f : e1 → e2)
      (data : GuardedExprRecursive e1) : GuardedExprRecursive e2 :=
    { bar := data.bar
      patterns := data.patterns.attach.map (fun ⟨p, _hp⟩ => PatternGuardRecursive.map f p)
      separator := data.separator
      where_ := WhereRecursive.map f data.where_ }
  termination_by sizeOf data
  decreasing_by
    all_goals simp_wf
    · cases data; simp_wf
      rename_i bar patterns separator where_
      have : sizeOf p < sizeOf patterns := Separated.sizeOf_attach_elem patterns ⟨p, _hp⟩
      omega
    · cases data; simp_wf
      omega

  -- ── PatternGuardRecursive ──────────────────────────────────────────
  @[simp] def PatternGuardRecursive.map {e1 e2 : Type} (f : e1 → e2)
      (data : PatternGuardRecursive e1) : PatternGuardRecursive e2 :=
    {
      binder := data.binder.attach.map (fun ⟨(b, t), _ht⟩ => (b.map f, t)),
      expr := Expr.map f data.expr
    }
  termination_by sizeOf data
  decreasing_by
    simp_wf
    cases data; simp_wf
    omega

  -- ── LetInRecursive ─────────────────────────────────────────────────
  @[simp] def LetInRecursive.map {e1 e2 : Type} (f : e1 → e2)
      (data : LetInRecursive e1) : LetInRecursive e2 :=
    { keyword := data.keyword
      bindings := data.bindings.attach.map (fun ⟨b, _hb⟩ => LetBindingRecursive.map f b)
      in_ := data.in_
      body := Expr.map f data.body }
  termination_by sizeOf data
  decreasing_by
    all_goals simp_wf
    · cases data; simp_wf
      rename_i keyword bindings in_ body
      have : sizeOf b < sizeOf bindings := NonEmptyArray.sizeOf_lt_of_mem _hb
      omega
    · cases data; simp_wf
      omega

  -- ── LetBindingRecursive ────────────────────────────────────────────
  @[simp] def LetBindingRecursive.map {e1 e2 : Type} (f : e1 → e2)
      (b : LetBindingRecursive e1) : LetBindingRecursive e2 :=
    match b with
    | .Signature l => .Signature (Labeled.map_value (Type_.map f) l)
    | .Name fields => .Name (ValueBindingFieldsRecursive.map f fields)
    | .Pattern b t w => .Pattern (Binder.map f b) t (WhereRecursive.map f w)
    | .Error d => .Error (f d)
  termination_by sizeOf b
  decreasing_by
    · simp_all only [LetBindingRecursive.Name.sizeOf_spec, Nat.lt_add_left_iff_pos, Nat.lt_add_one]
    · simp_all only [LetBindingRecursive.Pattern.sizeOf_spec, Nat.lt_add_left_iff_pos]
      omega

  -- ── ValueBindingFieldsRecursive ────────────────────────────────────
  @[simp] def ValueBindingFieldsRecursive.map {e1 e2 : Type} (f : e1 → e2)
      (data : ValueBindingFieldsRecursive e1) : ValueBindingFieldsRecursive e2 :=
    {
      name := data.name
      binders := data.binders.attach.map (fun ⟨b, _hb⟩ => Binder.map f b)
      guarded := GuardedRecursive.map f data.guarded
    }
  termination_by sizeOf data
  decreasing_by
    simp_wf
    cases data
    simp_all only [ValueBindingFieldsRecursive.mk.sizeOf_spec, Nat.lt_add_left_iff_pos]
    omega

  -- ── WhereRecursive ─────────────────────────────────────────────────
  @[simp] def WhereRecursive.map {e1 e2 : Type} (f : e1 → e2)
      (data : WhereRecursive e1) : WhereRecursive e2 :=
    { expr := Expr.map f data.expr
      bindings := data.bindings.attach.map (fun ⟨(t, bs), _hbs⟩ => (t, bs.attach.map (fun ⟨b, _hb⟩ => LetBindingRecursive.map f b))) }
  termination_by sizeOf data
  decreasing_by
    all_goals simp_wf
    cases data with
    | mk expr bindings =>
      cases bindings with
      | none =>
          simp only [WhereRecursive.mk.sizeOf_spec, Option.none.sizeOf_spec]
          omega
      | some p =>
          cases p with
          | mk t bs =>
            -- now `data` is definitionally `mk expr (some (t, bs))`
            simp only [WhereRecursive.mk.sizeOf_spec, Option.some.sizeOf_spec, Prod.mk.sizeOf_spec]
            -- goal should now be arithmetic and solvable by omega
            omega
    cases data with
    | mk expr bindings =>
      subst _hbs
      simp_all only [WhereRecursive.mk.sizeOf_spec, Option.some.sizeOf_spec, Prod.mk.sizeOf_spec]
      have : sizeOf b < sizeOf bs := by simp_all only [NonEmptyArray.sizeOf_lt_of_mem]
      omega

  -- ── DoBlockRecursive ───────────────────────────────────────────────
  @[simp] def DoBlockRecursive.map {e1 e2 : Type} (f : e1 → e2)
      (data : DoBlockRecursive e1) : DoBlockRecursive e2 :=
    { keyword := data.keyword
      statements := data.statements.attach.map (fun ⟨s, _hs⟩ => DoStatementRecursive.map f s) }
  termination_by sizeOf data
  decreasing_by
    simp_wf
    cases data with | mk keyword statements =>
      simp_wf
      have : sizeOf s < sizeOf statements := NonEmptyArray.sizeOf_lt_of_mem _hs
      omega

-- ── AdoBlockRecursive ──────────────────────────────────────────────
  @[simp] def AdoBlockRecursive.map {e1 e2 : Type} (f : e1 → e2)
      (data : AdoBlockRecursive e1) : AdoBlockRecursive e2 :=
    { keyword := data.keyword
      statements := data.statements.attach.map (fun ⟨s, _hs⟩ => DoStatementRecursive.map f s)
      in_ := data.in_
      result := Expr.map f data.result }
  termination_by sizeOf data
  decreasing_by
    all_goals simp_wf
    · cases data with | mk keyword statements in_ result =>
      simp_wf
      have : sizeOf s < sizeOf statements := Array.sizeOf_lt_of_mem _hs
      omega
    · cases data with | mk keyword statements in_ result =>
      simp_wf
      omega

  -- ── DoStatementRecursive ───────────────────────────────────────────
  @[simp] def DoStatementRecursive.map {e1 e2 : Type} (f : e1 → e2)
      (s : DoStatementRecursive e1) : DoStatementRecursive e2 :=
    match s with
    | .Let t bs => .Let t (bs.attach.map (fun ⟨b, _hb⟩ => LetBindingRecursive.map f b))
    | .Discard e' => .Discard (Expr.map f e')
    | .Bind b t e' => .Bind (Binder.map f b) t (Expr.map f e')
    | .Error d => .Error (f d)
  termination_by sizeOf s
  decreasing_by
    all_goals simp_wf
    · have : sizeOf b < sizeOf bs := NonEmptyArray.sizeOf_lt_of_mem _hb
      omega
    · omega
end

instance : Functor Expr where map := Expr.map
-- instance : LawfulFunctor Expr where
--   map_const := rfl
--   id_map := Expr.map_id
--   comp_map := Expr.map_comp

instance : Functor RecordAccessorRecursive where map := RecordAccessorRecursive.map
-- instance : LawfulFunctor RecordAccessorRecursive where
--   map_const := rfl
--   id_map := RecordAccessorRecursive.map_id
--   comp_map := RecordAccessorRecursive.map_comp

instance : Functor RecordUpdateRecursive where map := RecordUpdateRecursive.map
-- instance : LawfulFunctor RecordUpdateRecursive where
--   map_const := rfl
--   id_map := RecordUpdateRecursive.map_id
--   comp_map := RecordUpdateRecursive.map_comp

instance : Functor AppSpineRecursive where map := AppSpineRecursive.map
-- instance : LawfulFunctor AppSpineRecursive where
--   map_const := rfl
--   id_map := AppSpineRecursive.map_id
--   comp_map := AppSpineRecursive.map_comp

instance : Functor LambdaRecursive where map := LambdaRecursive.map
-- instance : LawfulFunctor LambdaRecursive where
--   map_const := rfl
--   id_map := LambdaRecursive.map_id
--   comp_map := LambdaRecursive.map_comp

instance : Functor IfThenElseRecursive where map := IfThenElseRecursive.map
-- instance : LawfulFunctor IfThenElseRecursive where
--   map_const := rfl
--   id_map := IfThenElseRecursive.map_id
--   comp_map := IfThenElseRecursive.map_comp

instance : Functor CaseOfRecursive where map := CaseOfRecursive.map
-- instance : LawfulFunctor CaseOfRecursive where
--   map_const := rfl
--   id_map := CaseOfRecursive.map_id
--   comp_map := CaseOfRecursive.map_comp

instance : Functor GuardedRecursive where map := GuardedRecursive.map
-- instance : LawfulFunctor GuardedRecursive where
--   map_const := rfl
--   id_map := GuardedRecursive.map_id
--   comp_map := GuardedRecursive.map_comp

instance : Functor GuardedExprRecursive where map := GuardedExprRecursive.map
-- instance : LawfulFunctor GuardedExprRecursive where
--   map_const := rfl
--   id_map := GuardedExprRecursive.map_id
--   comp_map := GuardedExprRecursive.map_comp

instance : Functor PatternGuardRecursive where map := PatternGuardRecursive.map
-- instance : LawfulFunctor PatternGuardRecursive where
--   map_const := rfl
--   id_map := PatternGuardRecursive.map_id
--   comp_map := PatternGuardRecursive.map_comp

instance : Functor LetInRecursive where map := LetInRecursive.map
-- instance : LawfulFunctor LetInRecursive where
--   map_const := rfl
--   id_map := LetInRecursive.map_id
--   comp_map := LetInRecursive.map_comp

instance : Functor LetBindingRecursive where map := LetBindingRecursive.map
-- instance : LawfulFunctor LetBindingRecursive where
--   map_const := rfl
--   id_map := LetBindingRecursive.map_id
--   comp_map := LetBindingRecursive.map_comp

instance : Functor ValueBindingFieldsRecursive where map := ValueBindingFieldsRecursive.map
-- instance : LawfulFunctor ValueBindingFieldsRecursive where
--   map_const := rfl
--   id_map := ValueBindingFieldsRecursive.map_id
--   comp_map := ValueBindingFieldsRecursive.map_comp

instance : Functor WhereRecursive where map := WhereRecursive.map
-- instance : LawfulFunctor WhereRecursive where
--   map_const := rfl
--   id_map := WhereRecursive.map_id
--   comp_map := WhereRecursive.map_comp

instance : Functor DoBlockRecursive where map := DoBlockRecursive.map
-- instance : LawfulFunctor DoBlockRecursive where
--   map_const := rfl
--   id_map := DoBlockRecursive.map_id
--   comp_map := DoBlockRecursive.map_comp

instance : Functor AdoBlockRecursive where map := AdoBlockRecursive.map
-- instance : LawfulFunctor AdoBlockRecursive where
--   map_const := rfl
--   id_map := AdoBlockRecursive.map_id
--   comp_map := AdoBlockRecursive.map_comp

instance : Functor DoStatementRecursive where map := DoStatementRecursive.map
-- instance : LawfulFunctor DoStatementRecursive where
--   map_const := rfl
--   id_map := DoStatementRecursive.map_id
--   comp_map := DoStatementRecursive.map_comp
