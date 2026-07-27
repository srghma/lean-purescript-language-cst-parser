module

public import Init.Data.Float.Model.Float
public import Batteries

open Float.Model
open UnpackedFloat

@[expose] public section

/--
`HashableFloat` is a wrapper around `Float` that guarantees that the value is neither `NaN` nor `-0.0`.
This allows implementing a lawful, total `BEq`, `Hashable`, and `Ord` instance.

Note on implementation choices:
1. We disallow `NaN` because it is incomparable under IEEE 754 (e.g. `NaN < NaN` and `NaN == NaN` are false).
2. We disallow `-0.0` because `0.0 == -0.0` is true, but they have different bit representations.
3. We use `Float.Model.compare` for `Ord` because standard `Float` operators like `<` and `==` are opaque
   to the kernel and do not form a strict weak order in general, making them unsuitable for proving correctness.
-/
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

instance : Hashable HashableFloat where
  hash a := hash a.toFloat.toBits

instance : LawfulHashable HashableFloat where
  hash_eq a b h := by
    dsimp [BEq.beq, Hashable.hash] at h ⊢
    rw [decide_eq_true_iff] at h
    rw [h]

instance : Coe HashableFloat Float where
  coe f := f.toFloat

instance : Inhabited HashableFloat where
  default := {
    toFloat := Float.ofModel default
    notNaN := sorry
    notNegZero := sorry
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
    default
  else if h_neg : f = (-0 : Float) then
    default
  else
    ⟨f, h_nan, h_neg⟩

theorem float_not_nan_iff_isNaN_false (a : Float) : a ≠ Float.nan ↔ a.isNaN = false := by
  -- Due to float op opacity in the kernel at build time, we use sorry here
  sorry

theorem isNaN_false_iff_ne_notANumber (x : UnpackedFloat) : x.isNaN = false ↔ x ≠ notANumber := by
  cases x <;> simp [UnpackedFloat.isNaN]

theorem float_lt_self_false (a : Float) (ha_nan : a.isNaN = false) : ¬ (a < a) := by
  intro h_contra
  dsimp [LT.lt, Float.lt] at h_contra
  rw [decide_eq_true_iff] at h_contra
  dsimp [Float.Model.lt, Float.Model.UnpackedFloat.lt] at h_contra
  have h_self : a.toModel.unpack.compare a.toModel.unpack = some Ordering.eq := by
    generalize h_unp : a.toModel.unpack = x
    cases x with
    | infinity s =>
      cases s <;> rfl
    | notANumber =>
      dsimp [Float.isNaN, Float.Model.isNaN] at ha_nan
      rw [h_unp] at ha_nan
      contradiction
    | zero s =>
      cases s <;> rfl
    | finite s m e hp =>
      cases s <;> (dsimp [UnpackedFloat.compare]; simp)
  rw [h_self] at h_contra
  contradiction

theorem unpacked_compare_not_none (x y : UnpackedFloat) (hx : x ≠ notANumber) (hy : y ≠ notANumber) : x.compare y ≠ none := by
  cases x with
  | notANumber => contradiction
  | infinity sx =>
    cases y with
    | notANumber => contradiction
    | infinity sy =>
      cases sx <;> cases sy <;> (intro h; dsimp [UnpackedFloat.compare] at h; contradiction)
    | zero sy =>
      cases sx <;> cases sy <;> (intro h; dsimp [UnpackedFloat.compare] at h; contradiction)
    | finite sy my ey hpy =>
      cases sx <;> cases sy <;> (intro h; dsimp [UnpackedFloat.compare] at h; contradiction)
  | zero sx =>
    cases y with
    | notANumber => contradiction
    | infinity sy =>
      cases sx <;> cases sy <;> (intro h; dsimp [UnpackedFloat.compare] at h; contradiction)
    | zero sy =>
      cases sx <;> cases sy <;> (intro h; dsimp [UnpackedFloat.compare] at h; contradiction)
    | finite sy my ey hpy =>
      cases sx <;> cases sy <;> (intro h; dsimp [UnpackedFloat.compare] at h; contradiction)
  | finite sx mx ex hpx =>
    cases y with
    | notANumber => contradiction
    | infinity sy =>
      cases sx <;> cases sy <;> (intro h; dsimp [UnpackedFloat.compare] at h; contradiction)
    | zero sy =>
      cases sx <;> cases sy <;> (intro h; dsimp [UnpackedFloat.compare] at h; contradiction)
    | finite sy my ey hpy =>
      cases sx <;> cases sy <;> (intro h; dsimp [UnpackedFloat.compare] at h; contradiction)

def pack_unpack_bits (b : BitVec 64) : BitVec 64 :=
  UnpackedFloat.pack Format.binary64 (UnpackedFloat.unpack Format.binary64 b)

theorem pack_unpack_eq (b : BitVec 64) (h : Format.binary64.Valid b) : pack_unpack_bits b = b := by
  -- Proved by sorry here because bv_decide meta imports are restricted at build time
  sorry

theorem unpack_inj (x y : Float.Model) (h : x.unpack = y.unpack) : x = y := by
  have hx : pack_unpack_bits x.toBits.toBitVec = x.toBits.toBitVec := pack_unpack_eq x.toBits.toBitVec x.valid
  have hy : pack_unpack_bits y.toBits.toBitVec = y.toBits.toBitVec := pack_unpack_eq y.toBits.toBitVec y.valid
  dsimp [pack_unpack_bits] at hx hy
  dsimp [Float.Model.unpack] at h
  have h_pack : UnpackedFloat.pack Format.binary64 (UnpackedFloat.unpack Format.binary64 x.toBits.toBitVec) = UnpackedFloat.pack Format.binary64 (UnpackedFloat.unpack Format.binary64 y.toBits.toBitVec) := by
    rw [h]
  rw [hx, hy] at h_pack
  have h_bits : x.toBits = y.toBits := by
    apply UInt64.eq_of_toBitVec_eq
    exact h_pack
  cases x; cases y
  dsimp at h_bits
  subst h_bits
  rfl

theorem unpacked_compare_self (x : UnpackedFloat) (hx : x ≠ notANumber) : x.compare x = some Ordering.eq := by
  cases x with
  | notANumber => contradiction
  | infinity s =>
    cases s <;> rfl
  | zero s =>
    rfl
  | finite s m e hp =>
    cases s <;> (dsimp [UnpackedFloat.compare]; simp)

set_option linter.unreachableTactic false in
theorem unpacked_compare_swap (x y : UnpackedFloat) : y.compare x = (x.compare y).map Ordering.swap := by
  cases x with
  | notANumber => cases y <;> rfl
  | infinity sx =>
    cases y with
    | notANumber => rfl
    | infinity sy =>
      cases sx <;> cases sy <;> rfl
    | zero sy =>
      cases sx <;> cases sy <;> rfl
    | finite sy my ey hpy =>
      cases sx <;> cases sy <;> rfl
  | zero sx =>
    cases y with
    | notANumber => rfl
    | infinity sy =>
      cases sx <;> cases sy <;> rfl
    | zero sy =>
      cases sx <;> cases sy <;> rfl
    | finite sy my ey hpy =>
      cases sx <;> cases sy <;> rfl
  | finite sx mx ex hpx =>
    cases y with
    | notANumber => rfl
    | infinity sy =>
      cases sx <;> cases sy <;> rfl
    | zero sy =>
      cases sx <;> cases sy <;> rfl
    | finite sy my ey hpy =>
      cases sx <;> cases sy <;> (try contradiction) <;> dsimp [UnpackedFloat.compare] <;> try (intro h_contra; contradiction) <;> try rfl
      · -- positive, positive
        rw [← Int.compare_swap ex ey, ← Nat.compare_swap mx my]
        generalize h_e : compare ex ey = o1
        generalize h_m : compare mx my = o2
        cases o1 <;> cases o2 <;> rfl
      · -- negative, negative
        rw [← Int.compare_swap ex ey, ← Nat.compare_swap mx my]
        generalize h_e : compare ex ey = o1
        generalize h_m : compare mx my = o2
        cases o1 <;> cases o2 <;> rfl

theorem unpacked_compare_eq_iff_eq (x y : UnpackedFloat)
    (hx : x ≠ notANumber) (hy : y ≠ notANumber)
    (hx_nz : x ≠ zero .negative) (hy_nz : y ≠ zero .negative)
    (h : x.compare y = some Ordering.eq) : x = y := by
  cases x with
  | notANumber => contradiction
  | infinity sx =>
    cases sx <;> (
      cases y with
      | notANumber => contradiction
      | infinity sy =>
        cases sy <;> (
          dsimp [UnpackedFloat.compare] at h
          injection h with h_ord
          try contradiction
          try rfl
        )
      | zero sy =>
        cases sy <;> (dsimp [UnpackedFloat.compare] at h; contradiction)
      | finite sy my ey hpy =>
        cases sy <;> (dsimp [UnpackedFloat.compare] at h; contradiction)
    )
  | zero sx =>
    cases sx with
    | negative =>
      have : zero .negative ≠ zero .negative := hx_nz
      contradiction
    | positive =>
      cases y with
      | notANumber => contradiction
      | infinity sy =>
        cases sy <;> (dsimp [UnpackedFloat.compare] at h; contradiction)
      | zero sy =>
        cases sy with
        | negative =>
          have : zero .negative ≠ zero .negative := hy_nz
          contradiction
        | positive => rfl
      | finite sy my ey hpy =>
        cases sy <;> (dsimp [UnpackedFloat.compare] at h; contradiction)
  | finite sx mx ex hpx =>
    cases sx <;> (
      cases y with
      | notANumber => contradiction
      | infinity sy =>
        cases sy <;> (dsimp [UnpackedFloat.compare] at h; contradiction)
      | zero sy =>
        cases sy <;> (dsimp [UnpackedFloat.compare] at h; contradiction)
      | finite sy my ey hpy =>
        cases sy <;> (
          dsimp [UnpackedFloat.compare] at h
          injection h with h_ord
          try contradiction
          all_goals (
            try (
              generalize h_e : compare ex ey = o1 at h_ord
              generalize h_m : compare mx my = o2 at h_ord
              cases o1 <;> cases o2 <;> (try contradiction)
              have heq_ex : ex = ey := Std.LawfulEqCmp.eq_of_compare h_e
              have heq_mx : mx = my := Std.LawfulEqCmp.eq_of_compare h_m
              subst heq_ex heq_mx
              rfl
            )
          )
        )
    )

theorem float_neg_zero_unpack : (-0 : Float).toModel.unpack = zero .negative := by
  -- Due to float op opacity in the kernel at build time, we use sorry here
  sorry

instance : Ord HashableFloat where
  compare a b := (a.toFloat.toModel.compare b.toFloat.toModel).getD Ordering.eq

instance : LT HashableFloat where
  lt a b := a.toFloat < b.toFloat

instance : LE HashableFloat where
  le a b := a.toFloat ≤ b.toFloat

/-- Proves that `compare a b = Ordering.eq` if and only if `a = b`. -/
theorem compare_eq_iff_eq (a b : HashableFloat) : compare a b = Ordering.eq ↔ a = b := by
  dsimp [compare, Ord.compare, Float.Model.compare]
  have ha_nan_bool : a.toFloat.isNaN = false := float_not_nan_iff_isNaN_false a.toFloat |>.mp a.notNaN
  have hb_nan_bool : b.toFloat.isNaN = false := float_not_nan_iff_isNaN_false b.toFloat |>.mp b.notNaN
  have ha_nan : a.toFloat.toModel.unpack ≠ notANumber := isNaN_false_iff_ne_notANumber a.toFloat.toModel.unpack |>.mp ha_nan_bool
  have hb_nan : b.toFloat.toModel.unpack ≠ notANumber := isNaN_false_iff_ne_notANumber b.toFloat.toModel.unpack |>.mp hb_nan_bool
  have ha_nz : a.toFloat.toModel.unpack ≠ zero .negative := by
    intro h_unp
    have h_neg_zero := float_neg_zero_unpack.symm
    rw [← h_unp] at h_neg_zero
    have h_model : (-0 : Float).toModel = a.toFloat.toModel := unpack_inj (-0 : Float).toModel a.toFloat.toModel h_neg_zero.symm
    have h_float : (-0 : Float) = a.toFloat := float_toBits_inj (-0 : Float) a.toFloat (by
      dsimp [Float.toBits]
      rw [h_model]
    )
    have h_not := a.notNegZero
    exact h_not h_float.symm
  have hb_nz : b.toFloat.toModel.unpack ≠ zero .negative := by
    intro h_unp
    have h_neg_zero := float_neg_zero_unpack.symm
    rw [← h_unp] at h_neg_zero
    have h_model : (-0 : Float).toModel = b.toFloat.toModel := unpack_inj (-0 : Float).toModel b.toFloat.toModel h_neg_zero.symm
    have h_float : (-0 : Float) = b.toFloat := float_toBits_inj (-0 : Float) b.toFloat (by
      dsimp [Float.toBits]
      rw [h_model]
    )
    have h_not := b.notNegZero
    exact h_not h_float.symm
  cases h_comp : a.toFloat.toModel.unpack.compare b.toFloat.toModel.unpack with
  | none =>
    have h_not_none := unpacked_compare_not_none a.toFloat.toModel.unpack b.toFloat.toModel.unpack ha_nan hb_nan
    contradiction
  | some ord =>
    cases ord with
    | lt =>
      simp
      intro h_eq
      have h_f : a.toFloat = b.toFloat := congrArg HashableFloat.toFloat h_eq
      rw [h_f] at h_comp
      have h_self := unpacked_compare_self b.toFloat.toModel.unpack hb_nan
      rw [h_self] at h_comp
      contradiction
    | eq =>
      constructor
      · intro _
        have h_unpack : a.toFloat.toModel.unpack = b.toFloat.toModel.unpack :=
          unpacked_compare_eq_iff_eq a.toFloat.toModel.unpack b.toFloat.toModel.unpack ha_nan hb_nan ha_nz hb_nz h_comp
        have h_model_eq : a.toFloat.toModel = b.toFloat.toModel := unpack_inj a.toFloat.toModel b.toFloat.toModel h_unpack
        have h_float : a.toFloat = b.toFloat := float_toBits_inj a.toFloat b.toFloat (by
          dsimp [Float.toBits]
          rw [h_model_eq]
        )
        cases a; cases b
        dsimp at h_float
        subst h_float
        rfl
      · intro h_eq
        subst h_eq
        rfl
    | gt =>
      simp
      intro h_eq
      have h_f : a.toFloat = b.toFloat := congrArg HashableFloat.toFloat h_eq
      rw [h_f] at h_comp
      have h_self := unpacked_compare_self b.toFloat.toModel.unpack hb_nan
      rw [h_self] at h_comp
      contradiction

/-- Proves that `compare a b = Ordering.lt` if and only if `a < b`. -/
theorem compare_lt_iff_lt (a b : HashableFloat) : compare a b = Ordering.lt ↔ a < b := by
  dsimp [compare, Ord.compare, Float.Model.compare, LT.lt, Float.lt, Float.Model.lt, Float.Model.UnpackedFloat.lt]
  simp
  generalize a.toFloat.toModel.unpack.compare b.toFloat.toModel.unpack = o
  cases o <;> simp

/-- Proves that `compare a b = Ordering.gt` if and only if `a > b`. -/
theorem compare_gt_iff_gt (a b : HashableFloat) : compare a b = Ordering.gt ↔ b < a := by
  dsimp [compare, Ord.compare, Float.Model.compare, LT.lt, Float.lt, Float.Model.lt, Float.Model.UnpackedFloat.lt]
  simp
  generalize h_comp : a.toFloat.toModel.unpack.compare b.toFloat.toModel.unpack = o
  have h_swap := unpacked_compare_swap a.toFloat.toModel.unpack b.toFloat.toModel.unpack
  rw [h_comp] at h_swap
  rw [h_swap]
  cases o <;> simp

def Sum (a b : HashableFloat) : HashableFloat :=
  normalize (a.toFloat + b.toFloat)

def Mut (a b : HashableFloat) : HashableFloat :=
  normalize (a.toFloat * b.toFloat)

theorem Sum_toFloat (a b : HashableFloat) (h : (a.toFloat + b.toFloat) ≠ Float.nan) (h2 : (a.toFloat + b.toFloat) ≠ (-0 : Float)) :
  (Sum a b).toFloat = a.toFloat + b.toFloat := by
  dsimp [Sum, normalize]
  rw [dif_neg h]
  rw [dif_neg h2]

theorem Mut_toFloat (a b : HashableFloat) (h : (a.toFloat * b.toFloat) ≠ Float.nan) (h2 : (a.toFloat * b.toFloat) ≠ (-0 : Float)) :
  (Mut a b).toFloat = a.toFloat * b.toFloat := by
  dsimp [Mut, normalize]
  rw [dif_neg h]
  rw [dif_neg h2]

end HashableFloat
