module

public import Init.Data.Float.Model.Float
public import Batteries
public import Std.Tactic.BVDecide
public import Std.Tactic.BVDecide.Reflect

open Float.Model
open UnpackedFloat

@[expose] public section

structure HashableFloat where
  ofFloat ::
  toFloat : Float
  notNaN : toFloat ≠ Float.nan
  notNegZero : toFloat ≠ (-0 : Float)

instance : Repr HashableFloat where
  reprPrec f := reprPrec f.toFloat

theorem float_toBits_inj (a b : Float) : a.toBits = b.toBits → a = b := by
  intro h
  cases a; rename_i ma
  cases b; rename_i mb
  dsimp [Float.toBits] at h
  cases ma; rename_i ba vala
  cases mb; rename_i bb valb
  dsimp at h
  subst h
  have h_val : vala = valb := by rfl
  subst h_val
  rfl

instance : BEq HashableFloat where
  beq a b := a.toFloat.toBits == b.toFloat.toBits

instance : ReflBEq HashableFloat where
  rfl {a} := by
    dsimp [BEq.beq]
    simp

instance : LawfulBEq HashableFloat where
  eq_of_beq {a b} h := by
    dsimp [BEq.beq] at h
    rw [decide_eq_true_iff] at h
    have h_float : a.toFloat = b.toFloat := float_toBits_inj a.toFloat b.toFloat h
    cases a; cases b
    dsimp at h_float
    subst h_float
    rfl

instance : Coe HashableFloat Float where
  coe f := f.toFloat

instance : Inhabited HashableFloat where
  default := {
    toFloat := Float.ofModel default
    notNaN := fun h => by
      have h_eq : (Float.ofModel default).toBits = Float.nan.toBits := by rw [h]
      have h_eq' : 0 = Float.nan.toBits := h_eq
      have h_ne : 0 ≠ Float.nan.toBits := by decide
      exact h_ne h_eq'
    notNegZero := fun h => by
      have h_eq : (Float.ofModel default).toBits = (-0 : Float).toBits := by rw [h]
      have h_eq' : 0 = (Float.neg (Float.ofModel default)).toBits := h_eq
      have h_ne : 0 ≠ (Float.neg (Float.ofModel default)).toBits := by decide
      exact h_ne h_eq'
  }

namespace HashableFloat

noncomputable def ofFloat? (f : Float) : Option HashableFloat :=
  if h_nan : f = Float.nan then
    none
  else if h_neg : f = (-0 : Float) then
    none
  else
    some (HashableFloat.ofFloat f h_nan h_neg)

noncomputable def ofFloat! (f : Float) : HashableFloat :=
  match ofFloat? f with
  | some hf => hf
  | none => panic! s!"Invalid HashableFloat: {f} is either NaN or -0.0"

noncomputable def normalize (f : Float) : HashableFloat :=
  if h_nan : f = Float.nan then
    default
  else if h_neg : f = (-0 : Float) then
    default
  else
    ⟨f, h_nan, h_neg⟩

instance : Ord HashableFloat where
  compare a b := compare a.toFloat.toBits b.toFloat.toBits

instance : LT HashableFloat where
  lt a b := a.toFloat.toBits < b.toFloat.toBits

instance : LE HashableFloat where
  le a b := a.toFloat.toBits ≤ b.toFloat.toBits

theorem compare_eq_iff_eq (a b : HashableFloat) : compare a b = Ordering.eq ↔ a = b := by
  dsimp [compare, Ord.compare, compareOfLessAndEq]
  constructor
  · intro h
    split at h
    · contradiction
    · split at h
      · rename_i h_eq
        have h_float : a.toFloat = b.toFloat := float_toBits_inj a.toFloat b.toFloat h_eq
        cases a; cases b
        dsimp at h_float
        subst h_float
        rfl
      · contradiction
  · intro h
    subst h
    dsimp [compare, Ord.compare, compareOfLessAndEq]
    split
    · have h_contra : ¬ (a.toFloat.toBits < a.toFloat.toBits) := by bv_decide
      contradiction
    · split
      · rfl
      · rename_i h_eq
        have h_refl : a.toFloat.toBits = a.toFloat.toBits := rfl
        contradiction

theorem compare_lt_iff_lt (a b : HashableFloat) : compare a b = Ordering.lt ↔ a < b := by
  dsimp [compare, Ord.compare, compareOfLessAndEq, LT.lt]
  constructor
  · intro h
    split at h <;> rename_i h_lt
    · exact h_lt
    · split at h <;> contradiction
  · intro h
    split
    · rfl
    · contradiction

theorem compare_gt_iff_gt (a b : HashableFloat) : compare a b = Ordering.gt ↔ b < a := by
  dsimp [compare, Ord.compare, compareOfLessAndEq, LT.lt]
  constructor
  · intro h
    split at h <;> rename_i h_lt
    · contradiction
    · split at h <;> rename_i h_eq
      · contradiction
      · have h_lt_ba : (b.toFloat.toBits < a.toFloat.toBits) = true := by bv_decide
        exact h_lt_ba
  · intro h
    split <;> rename_i h_lt_ab
    · have h_asymm : ¬ (a.toFloat.toBits < b.toFloat.toBits ∧ b.toFloat.toBits < a.toFloat.toBits) := by bv_decide
      have h_and : a.toFloat.toBits < b.toFloat.toBits ∧ b.toFloat.toBits < a.toFloat.toBits := ⟨h_lt_ab, h⟩
      contradiction
    · split <;> rename_i h_eq
      · have h_refl : ¬ (b.toFloat.toBits < b.toFloat.toBits) := by bv_decide
        rw [← h_eq] at h
        contradiction
      · rfl

noncomputable def Sum (a b : HashableFloat) : HashableFloat :=
  normalize (a.toFloat + b.toFloat)

noncomputable def Mut (a b : HashableFloat) : HashableFloat :=
  normalize (a.toFloat * b.toFloat)

theorem Sum_toFloat (a b : HashableFloat) (h : (a.toFloat + b.toFloat) ≠ Float.nan) (h2 : (a.toFloat + b.toFloat) ≠ (-0 : Float)) :
  (Sum a b).toFloat = a.toFloat + b.toFloat := by
  by_cases h_nan : a.toFloat + b.toFloat = Float.nan
  · contradiction
  · by_cases h_neg : a.toFloat + b.toFloat = (-0 : Float)
    · contradiction
    · dsimp [normalize]
      rw [if_neg h_nan, if_neg h_neg]
      rfl

theorem Mut_toFloat (a b : HashableFloat) (h : (a.toFloat * b.toFloat) ≠ Float.nan) (h2 : (a.toFloat * b.toFloat) ≠ (-0 : Float)) :
  (Mut a b).toFloat = a.toFloat * b.toFloat := by
  by_cases h_nan : a.toFloat * b.toFloat = Float.nan
  · contradiction
  · by_cases h_neg : a.toFloat * b.toFloat = (-0 : Float)
    · contradiction
    · dsimp [normalize]
      rw [if_neg h_nan, if_neg h_neg]
      rfl

end HashableFloat
