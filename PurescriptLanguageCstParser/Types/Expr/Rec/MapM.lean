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

mutual

  -- ── Expr ───────────────────────────────────────────────────────────
  @[simp] def Expr.mapM {e1 e2 : Type} {m : Type → Type} [Monad m] (f : e1 → m e2) : Expr e1 → m (Expr e2)
    | .Hole n             => pure (.Hole n)
    | .Section t          => pure (.Section t)
    | .Ident n            => pure (.Ident n)
    | .Constructor n      => pure (.Constructor n)
    | .Boolean t v        => pure (.Boolean t v)
    | .Char t v           => pure (.Char t v)
    | .String t v => pure (.String t v)
    | .Int t v            => pure (.Int t v)
    | .Number t v         => pure (.Number t v)
    | .OpName n           => pure (.OpName n)
    | .Error d            => .Error <$> f d
    | .Parens w           => .Parens <$> (Wrapped.mk w.open_ <$> (Expr.mapM f) w.value <*> pure w.close)
    -- | .Parens w           => .Parens <$> w.mapM (Expr.mapM f)
    | .Typed e t ty       => .Typed <$> Expr.mapM f e <*> pure t <*> Type_.mapM f ty
    | .Negate t e         => .Negate t <$> Expr.mapM f e
    | .Array items        => .Array <$> Expr.mapMDelimited f items
    | .Record fields      => .Record <$> Expr.mapMDelimitedRL f fields
    | .Infix head tail    => do
        let head' ← Expr.mapM f head
        let tail' ← tail.attach.mapM (fun ⟨⟨w, e⟩, _hmem⟩ => do
          let w' ← Wrapped.mk w.open_ <$> Expr.mapM f w.value <*> pure w.close
          let e' ← Expr.mapM f e
          pure (w', e'))
        pure (.Infix head' tail')
    | .Op head ops        => do
        let head' ← Expr.mapM f head
        let ops' ← ops.attach.mapM (fun ⟨⟨n, e⟩, _hmem⟩ => do
          let e' ← Expr.mapM f e
          pure (n, e'))
        pure (.Op head' ops')
    | .RecordAccessor d   => .RecordAccessor <$> RecordAccessorRecursive.mapM f d
    | .RecordUpdate e upd => do
        let e' ← Expr.mapM f e
        let upd' ← upd.attach.mapM (fun ⟨u, _hmem⟩ => RecordUpdateRecursive.mapM f u)
        pure (.RecordUpdate e' upd')
    | .App fn args        => do
        let fn' ← Expr.mapM f fn
        let args' ← args.attach.mapM (fun ⟨s, _hmem⟩ => AppSpineRecursive.mapM f s)
        pure (.App fn' args')
    | .Lambda d           => .Lambda  <$> LambdaRecursive.mapM f d
    | .If d               => .If      <$> IfThenElseRecursive.mapM f d
    | .Case d             => .Case    <$> CaseOfRecursive.mapM f d
    | .Let d              => .Let     <$> LetInRecursive.mapM f d
    | .Do d               => .Do      <$> DoBlockRecursive.mapM f d
    | .Ado d              => .Ado     <$> AdoBlockRecursive.mapM f d
  termination_by t => sizeOf t
  decreasing_by
    all_goals simp_wf
    all_goals try decreasing_trivial
    -- Parens
    ·
      -- simp_all? [Wrapped.sizeOf_mem]
      have := Wrapped.sizeOf_value w;
      omega
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
  @[simp] def Expr.mapMDelimited {e1 e2} {m} [Monad m] (f : e1 → m e2) : Delimited (Expr e1) → m (Delimited (Expr e2))
    | .mk ⟨o, none,   c⟩ => pure (.mk ⟨o, none, c⟩)
    | .mk ⟨o, some s, c⟩ => do
        let s' ← Expr.mapMSep f s
        pure (.mk ⟨o, some s', c⟩)
  termination_by d => sizeOf d
  decreasing_by
    simp only [Delimited.mk.sizeOf_spec, Wrapped.mk.sizeOf_spec,
               Option.some.sizeOf_spec] at *; omega

  -- ── Separated (Expr e) ─────────────────────────────────────────────
  @[simp] def Expr.mapMSep {e1 e2} {m} [Monad m] (f : e1 → m e2) (s : Separated (Expr e1)) : m (Separated (Expr e2)) := do
    let head ← Expr.mapM f s.head
    let tail ← s.tail.attach.mapM (fun ⟨⟨tok, e⟩, _hmem⟩ => do
      let e' ← Expr.mapM f e
      pure (tok, e'))
    pure { head := head, tail := tail }
  termination_by sizeOf s
  decreasing_by
    · exact Separated.sizeOf_head s
    · simp_wf
      obtain ⟨i, hi, h⟩ := Array.mem_iff_getElem.mp _hmem
      have : e = s.tail[i].2 := by simp only [h]
      rw [this]; exact s.sizeOf_tail_get i hi

  -- ── Delimited (RecordLabeled (Expr e)) ─────────────────────────────
  @[simp] def Expr.mapMDelimitedRL {e1 e2} {m} [Monad m] (f : e1 → m e2)
      : Delimited (RecordLabeled (Expr e1)) → m (Delimited (RecordLabeled (Expr e2)))
    | .mk ⟨o, none,   c⟩ => pure (.mk ⟨o, none, c⟩)
    | .mk ⟨o, some s, c⟩ => do
        let s' ← Expr.mapMSepRL f s
        pure (.mk ⟨o, some s', c⟩)
  termination_by d => sizeOf d
  decreasing_by
    simp only [Delimited.mk.sizeOf_spec, Wrapped.mk.sizeOf_spec,
               Option.some.sizeOf_spec] at *; omega

  -- ── Separated (RecordLabeled (Expr e)) ─────────────────────────────
  @[simp] def Expr.mapMSepRL {e1 e2} {m} [Monad m] (f : e1 → m e2)
      (s : Separated (RecordLabeled (Expr e1))) : m (Separated (RecordLabeled (Expr e2))) := do
    let head ← Expr.mapMRL f s.head
    let tail ← s.tail.attach.mapM (fun ⟨⟨tok, rl⟩, _hmem⟩ => do
      let rl' ← Expr.mapMRL f rl
      pure (tok, rl'))
    pure { head := head, tail := tail }
  termination_by sizeOf s
  decreasing_by
    · exact Separated.sizeOf_head s
    · simp_wf
      obtain ⟨i, hi, h⟩ := Array.mem_iff_getElem.mp _hmem
      have : rl = s.tail[i].2 := by simp only [h]
      rw [this]; exact s.sizeOf_tail_get i hi

  -- ── RecordLabeled (Expr e) ─────────────────────────────────────────
  @[simp] def Expr.mapMRL {e1 e2} {m} [Monad m] (f : e1 → m e2) : RecordLabeled (Expr e1) → m (RecordLabeled (Expr e2))
    | .Pun n           => pure (.Pun n)
    | .Field l sep e'  => .Field l sep <$> Expr.mapM f e'
  termination_by rl => sizeOf rl
  decreasing_by
    simp_wf
    omega

  -- ── RecordAccessorRecursive ────────────────────────────────────────
  @[simp] def RecordAccessorRecursive.mapM {e1 e2 : Type} {m} [Monad m] (f : e1 → m e2)
      (data : RecordAccessorRecursive e1) : m (RecordAccessorRecursive e2) := do
    let expr ← Expr.mapM f data.expr
    pure { expr := expr, dot := data.dot, path := data.path }
  termination_by sizeOf data
  decreasing_by
    simp_wf
    cases data; simp_wf
    omega

  -- ── RecordUpdateRecursive ──────────────────────────────────────────
  @[simp] def RecordUpdateRecursive.mapM {e1 e2 : Type} {m} [Monad m] (f : e1 → m e2)
      (u : RecordUpdateRecursive e1) : m (RecordUpdateRecursive e2) :=
    match u with
    | .Leaf l t e' => .Leaf l t <$> Expr.mapM f e'
    | .Branch l updates => .Branch l <$> updates.attach.mapM fun ⟨u', _hu'⟩ => RecordUpdateRecursive.mapM f u'
  termination_by sizeOf u
  decreasing_by
    all_goals simp_wf
    · omega
    · have : sizeOf u' < sizeOf updates := DelimitedNonEmpty.sizeOf_attach_elem updates ⟨u', _hu'⟩
      omega

  -- ── AppSpineRecursive ──────────────────────────────────────────────
  @[simp] def AppSpineRecursive.mapM {e1 e2 : Type} {m} [Monad m] (f : e1 → m e2)
      (s : AppSpineRecursive e1) : m (AppSpineRecursive e2) :=
    match s with
    | .Type_ t ty => .Type_ t <$> Type_.mapM f ty
    | .Term e' => .Term <$> Expr.mapM f e'
  termination_by sizeOf s
  decreasing_by
    all_goals simp_wf

  -- ── LambdaRecursive ────────────────────────────────────────────────
  @[simp] def LambdaRecursive.mapM {e1 e2 : Type} {m} [Monad m] (f : e1 → m e2)
      (data : LambdaRecursive e1) : m (LambdaRecursive e2) := do
    let binders ← data.binders.mapM (Binder.mapM f)
    let body ← Expr.mapM f data.body
    pure { symbol := data.symbol, binders := binders, arrow := data.arrow, body := body }
  termination_by sizeOf data
  decreasing_by
    simp_wf
    cases data; simp_wf
    omega

  -- ── IfThenElseRecursive ────────────────────────────────────────────
  @[simp] def IfThenElseRecursive.mapM {e1 e2 : Type} {m} [Monad m] (f : e1 → m e2)
      (data : IfThenElseRecursive e1) : m (IfThenElseRecursive e2) := do
    let cond ← Expr.mapM f data.cond
    let true_ ← Expr.mapM f data.true_
    let false_ ← Expr.mapM f data.false_
    pure { keyword := data.keyword, cond := cond, then_ := data.then_, true_ := true_, else_ := data.else_, false_ := false_ }
  termination_by sizeOf data
  decreasing_by
    all_goals simp_wf
    all_goals cases data; simp_wf
    all_goals omega

  -- ── CaseOfRecursive ────────────────────────────────────────────────
  @[simp] def CaseOfRecursive.mapM {e1 e2 : Type} {m} [Monad m] (f : e1 → m e2)
      (data : CaseOfRecursive e1) : m (CaseOfRecursive e2) := do
    let head ← Expr.mapMSep f data.head
    let branches ← data.branches.attach.mapM (fun x => do
      let b ← x.val.1.mapM (Binder.mapM f)
      let g ← GuardedRecursive.mapM f x.val.2
      pure (b, g))
    pure { keyword := data.keyword, head := head, of := data.of, branches := branches }
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
  @[simp] def GuardedRecursive.mapM {e1 e2 : Type} {m} [Monad m] (f : e1 → m e2)
      (g : GuardedRecursive e1) : m (GuardedRecursive e2) :=
    match g with
    | .Unconditional t w => .Unconditional t <$> WhereRecursive.mapM f w
    | .Guarded branches => .Guarded <$> branches.attach.mapM (fun ⟨b, _hb⟩ => GuardedExprRecursive.mapM f b)
  termination_by sizeOf g
  decreasing_by
    all_goals simp_wf
    · omega
    · have : sizeOf b < sizeOf branches := NonEmptyArray.sizeOf_lt_of_mem _hb
      omega

  -- ── GuardedExprRecursive ───────────────────────────────────────────
  @[simp] def GuardedExprRecursive.mapM {e1 e2 : Type} {m} [Monad m] (f : e1 → m e2)
      (data : GuardedExprRecursive e1) : m (GuardedExprRecursive e2) := do
    let patterns ← data.patterns.attach.mapM (fun ⟨p, _hp⟩ => PatternGuardRecursive.mapM f p)
    let where_ ← WhereRecursive.mapM f data.where_
    pure { bar := data.bar, patterns := patterns, separator := data.separator, where_ := where_ }
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
  @[simp] def PatternGuardRecursive.mapM {e1 e2 : Type} {m} [Monad m] (f : e1 → m e2)
      (data : PatternGuardRecursive e1) : m (PatternGuardRecursive e2) := do
    let binder ← data.binder.mapM (fun (b, t) => do
      let b' ← Binder.mapM f b
      pure (b', t))
    let expr ← Expr.mapM f data.expr
    pure { binder := binder, expr := expr }
  termination_by sizeOf data
  decreasing_by
    simp_wf
    cases data; simp_wf
    omega

  -- ── LetInRecursive ─────────────────────────────────────────────────
  @[simp] def LetInRecursive.mapM {e1 e2 : Type} {m} [Monad m] (f : e1 → m e2)
      (data : LetInRecursive e1) : m (LetInRecursive e2) := do
    let bindings ← data.bindings.attach.mapM (fun ⟨b, _hb⟩ => LetBindingRecursive.mapM f b)
    let body ← Expr.mapM f data.body
    pure { keyword := data.keyword, bindings := bindings, in_ := data.in_, body := body }
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
  @[simp] def LetBindingRecursive.mapM {e1 e2 : Type} {m} [Monad m] (f : e1 → m e2)
      (b : LetBindingRecursive e1) : m (LetBindingRecursive e2) :=
    match b with
    | .Signature l => .Signature <$> Labeled.mapM_value (Type_.mapM f) l
    | .Name fields => .Name <$> ValueBindingFieldsRecursive.mapM f fields
    | .Pattern b t w => .Pattern <$> Binder.mapM f b <*> pure t <*> WhereRecursive.mapM f w
    | .Error d => .Error <$> f d
  termination_by sizeOf b
  decreasing_by
    · simp_all only [LetBindingRecursive.Name.sizeOf_spec, Nat.lt_add_left_iff_pos, Nat.lt_add_one]
    · simp_all only [LetBindingRecursive.Pattern.sizeOf_spec, Nat.lt_add_left_iff_pos]
      omega

  -- ── ValueBindingFieldsRecursive ────────────────────────────────────
  @[simp] def ValueBindingFieldsRecursive.mapM {e1 e2 : Type} {m} [Monad m] (f : e1 → m e2)
      (data : ValueBindingFieldsRecursive e1) : m (ValueBindingFieldsRecursive e2) := do
    let binders ← data.binders.mapM (Binder.mapM f)
    let guarded ← GuardedRecursive.mapM f data.guarded
    pure { name := data.name, binders := binders, guarded := guarded }
  termination_by sizeOf data
  decreasing_by
    simp_wf
    cases data
    simp_all only [ValueBindingFieldsRecursive.mk.sizeOf_spec, Nat.lt_add_left_iff_pos]
    omega

  -- ── WhereRecursive ─────────────────────────────────────────────────
  @[simp] def WhereRecursive.mapM {e1 e2 : Type} {m} [Monad m] (f : e1 → m e2)
      (data : WhereRecursive e1) : m (WhereRecursive e2) := do
    let expr ← Expr.mapM f data.expr
    let bindings ← data.bindings.attach.mapM (fun ⟨(t, bs), _hbs⟩ => do
      let bs' ← bs.attach.mapM (fun ⟨b, _hb⟩ => LetBindingRecursive.mapM f b)
      pure (t, bs'))
    pure { expr := expr, bindings := bindings }
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
            simp only [WhereRecursive.mk.sizeOf_spec, Option.some.sizeOf_spec, Prod.mk.sizeOf_spec]
            omega
    cases data with
    | mk expr bindings =>
      subst _hbs
      simp_all only [WhereRecursive.mk.sizeOf_spec, Option.some.sizeOf_spec, Prod.mk.sizeOf_spec]
      have : sizeOf b < sizeOf bs := by simp_all only [NonEmptyArray.sizeOf_lt_of_mem]
      omega

  -- ── DoBlockRecursive ───────────────────────────────────────────────
  @[simp] def DoBlockRecursive.mapM {e1 e2 : Type} {m} [Monad m] (f : e1 → m e2)
      (data : DoBlockRecursive e1) : m (DoBlockRecursive e2) := do
    let statements ← data.statements.attach.mapM (fun ⟨s, _hs⟩ => DoStatementRecursive.mapM f s)
    pure { keyword := data.keyword, statements := statements }
  termination_by sizeOf data
  decreasing_by
    simp_wf
    cases data with | mk keyword statements =>
      simp_wf
      have : sizeOf s < sizeOf statements := NonEmptyArray.sizeOf_lt_of_mem _hs
      omega

-- ── AdoBlockRecursive ──────────────────────────────────────────────
  @[simp] def AdoBlockRecursive.mapM {e1 e2 : Type} {m} [Monad m] (f : e1 → m e2)
      (data : AdoBlockRecursive e1) : m (AdoBlockRecursive e2) := do
    let statements ← data.statements.attach.mapM (fun ⟨s, _hs⟩ => DoStatementRecursive.mapM f s)
    let result ← Expr.mapM f data.result
    pure { keyword := data.keyword, statements := statements, in_ := data.in_, result := result }
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
  @[simp] def DoStatementRecursive.mapM {e1 e2 : Type} {m} [Monad m] (f : e1 → m e2)
      (s : DoStatementRecursive e1) : m (DoStatementRecursive e2) :=
    match s with
    | .Let t bs => .Let t <$> bs.attach.mapM (fun ⟨b, _hb⟩ => LetBindingRecursive.mapM f b)
    | .Discard e' => .Discard <$> Expr.mapM f e'
    | .Bind b t e' => .Bind <$> Binder.mapM f b <*> pure t <*> Expr.mapM f e'
    | .Error d => .Error <$> f d
  termination_by sizeOf s
  decreasing_by
    all_goals simp_wf
    · have : sizeOf b < sizeOf bs := NonEmptyArray.sizeOf_lt_of_mem _hb
      omega
    · omega
end
