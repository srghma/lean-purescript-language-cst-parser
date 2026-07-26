module

public import Batteries.Data.Float.Lemmas

@[expose] public section

structure HashableFloat where
  ofFloat ::
  toFloat : Float
  notNaN : toFloat ≠ Float.nan
  notNegZero : toFloat ≠ (-0 : Float)

instance : Repr HashableFloat where
  reprPrec f := reprPrec f.toFloat

instance : BEq HashableFloat where
  beq a b := a.toFloat == b.toFloat

instance : Hashable HashableFloat where
  hash f := hash f.toFloat.toBits

instance : LawfulHashable HashableFloat where
  hash_eq a b h := by
    dsimp [BEq.beq, hash] at h ⊢
    have h_eq : a.toFloat == b.toFloat := h
    rw [Float.beq_iff_ne_nan_and_eq] at h_eq
    have h_or := h_eq.2.2
    rcases h_or with h_val | ⟨_, h_neg⟩ | ⟨h_neg, _⟩
    · rw [h_val]
    · have h_contra := b.notNegZero
      contradiction
    · have h_contra := a.notNegZero
      contradiction

instance : ReflBEq HashableFloat where
  rfl {a} := by
    have h : (a.toFloat == a.toFloat) = true := by
      rw [Float.beq_iff_ne_nan_and_eq]
      exact ⟨a.notNaN, a.notNaN, Or.inl rfl⟩
    exact h

instance : LawfulBEq HashableFloat where
  eq_of_beq {a b} h := by
    have h' : (a.toFloat == b.toFloat) = true := h
    rw [Float.beq_iff_ne_nan_and_eq] at h'
    have h_or := h'.2.2
    rcases h_or with h_val | ⟨_, h_neg⟩ | ⟨h_neg, _⟩
    · cases a; cases b
      dsimp at h_val
      subst h_val
      rfl
    · have h_contra := b.notNegZero
      contradiction
    · have h_contra := a.notNegZero
      contradiction

instance : Coe HashableFloat Float where
  coe f := f.toFloat

-- Custom Ord instance for HashableFloat
instance : Ord HashableFloat where
  compare a b :=
    if a.toFloat < b.toFloat then Ordering.lt
    else if a.toFloat == b.toFloat then Ordering.eq
    else Ordering.gt

instance : LT HashableFloat where
  lt a b := a.toFloat < b.toFloat

instance : LE HashableFloat where
  le a b := a.toFloat ≤ b.toFloat

instance : Inhabited HashableFloat where
  default := {
    toFloat := default -- it is 0
    notNaN := fun h => by
      have hBits : (0.0 : Float).toBits = Float.nan.toBits := by rw [h]
      revert hBits; decide
    notNegZero := fun h => by
      have hBits : (0.0 : Float).toBits = (-0.0 : Float).toBits := by rw [h]
      revert hBits; decide
  }

namespace HashableFloat

def ofFloat? (f : Float) : Option HashableFloat :=
  if h_nan : f = Float.nan then
    none
  else if h_neg : f = (-0 : Float) then
    none
  else
    some (HashableFloat.ofFloat f h_nan h_neg)

def ofFloat! (f : Float) : HashableFloat :=
  match ofFloat? f with
  | some hf => hf
  | none => panic! s!"Invalid HashableFloat: {f} is either NaN or -0.0"

def normalize (f : Float) : HashableFloat :=
  if h_nan : f = Float.nan then
    default -- returns the 0.0 from the Inhabited instance
  else if h_neg : f = (-0 : Float) then
    default
  else
    ⟨f, h_nan, h_neg⟩

-- ==========================================
-- PROOFS OF CORRECTNESS FOR `Ord` -- TODO: is there some class in mathlib to prove ord correctness instead of these custom theorems?
-- ==========================================

-- TODO: what other classes can prove other correctnesses?

/-- Proves that `compare a b = Ordering.eq` if and only if `a = b`. -/
theorem compare_eq_iff_eq (a b : HashableFloat) : compare a b = Ordering.eq ↔ a = b := by
  dsimp [compare]
  split_ifs with h_lt h_eq
  · simp
  · have h : (a.toFloat == b.toFloat) = true := h_eq
    rw [Float.beq_iff_ne_nan_and_eq] at h
    rcases h.2.2 with h_val | ⟨_, h_neg⟩ | ⟨h_neg, _⟩
    · cases a; cases b; dsimp at h_val; subst h_val; simp
    · have h_contra := b.notNegZero; contradiction
    · have h_contra := a.notNegZero; contradiction
  · simp

/-- Proves that `compare a b = Ordering.lt` if and only if `a < b`. -/
theorem compare_lt_iff_lt (a b : HashableFloat) : compare a b = Ordering.lt ↔ a < b := by
  dsimp [compare, LT.lt]
  split_ifs with h_lt
  · simp [h_lt]
  · simp [h_lt]

-- TODO: Prove that `compare a b = Ordering.gt` if and only if `a > b`.


-- TODO: add also Sum, Mut, prove their correctness too

end HashableFloat
