module

public import Batteries.Data.Float.Lemmas

@[expose] public section

structure HashableFloat where
  val : Float
  noNaN : val ≠ Float.nan
  noNegZero : val ≠ (-0 : Float)

instance : Hashable Float := ⟨λ f => hash f.toBits⟩

instance : Repr HashableFloat where
  reprPrec f d := reprPrec f.val d

instance : BEq HashableFloat where
  beq a b := a.val == b.val

instance : Hashable HashableFloat where
  hash f := hash f.val.toBits

instance : LawfulHashable HashableFloat where
  hash_eq a b h := by
    dsimp [BEq.beq, hash] at h ⊢
    have h_eq : a.val == b.val := h
    rw [Float.beq_iff_ne_nan_and_eq] at h_eq
    have h_or := h_eq.2.2
    rcases h_or with h_val | ⟨_, h_neg⟩ | ⟨h_neg, _⟩
    · rw [h_val]
    · have h_contra := b.noNegZero
      contradiction
    · have h_contra := a.noNegZero
      contradiction

instance : ReflBEq HashableFloat where
  rfl {a} := by
    have h : (a.val == a.val) = true := by
      rw [Float.beq_iff_ne_nan_and_eq]
      exact ⟨a.noNaN, a.noNaN, Or.inl rfl⟩
    exact h

instance : LawfulBEq HashableFloat where
  eq_of_beq {a b} h := by
    have h' : (a.val == b.val) = true := h
    rw [Float.beq_iff_ne_nan_and_eq] at h'
    have h_or := h'.2.2
    rcases h_or with h_val | ⟨_, h_neg⟩ | ⟨h_neg, _⟩
    · cases a; cases b
      dsimp at h_val
      subst h_val
      rfl
    · have h_contra := b.noNegZero
      contradiction
    · have h_contra := a.noNegZero
      contradiction
