import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Cast.Order.Field

namespace LCTR.CoreAffineFrequency
universe u v w
set_option autoImplicit false
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {P : Type v} [LinearOrder P]

structure AffineData (K : Type u) (P : Type v) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [LinearOrder P] where
  act : P → K → P
  diff : P → P → K
  zero_action : ∀ a, act a 0 = a
  diff_spec : ∀ a b z, act a z = b ↔ z = diff b a
  strict_sign : ∀ a b, a < b ↔ 0 < diff b a

theorem difference_reflexive (A : AffineData K P) (a : P) : A.diff a a = 0 :=
  ((A.diff_spec a a 0).mp (A.zero_action a)).symm

theorem difference_zero_iff (A : AffineData K P) (a b : P) : A.diff b a = 0 ↔ a=b := by
  constructor
  · intro h
    exact (A.zero_action a).symm.trans ((A.diff_spec a b 0).mpr h.symm)
  · intro h
    subst b
    exact difference_reflexive A a

theorem difference_nonnegative (A : AffineData K P) (a b : P) :
    a ≤ b ↔ 0 ≤ A.diff b a := by
  rw [le_iff_lt_or_eq,le_iff_lt_or_eq,A.strict_sign]
  constructor
  · rintro (h|h)
    · exact Or.inl h
    · exact Or.inr ((difference_zero_iff A a b).mpr h).symm
  · rintro (h|h)
    · exact Or.inl h
    · exact Or.inr ((difference_zero_iff A a b).mp h.symm)

structure Window (Q : Type w) (r : Q → Q → Prop) where
  k0 : Nat
  k1 : Nat
  increasing : k0 < k1
  lower : Q
  upper : Q
  ordered : r lower upper

variable {Q : Type w} {r : Q → Q → Prop}

def countDifference (x : Window Q r) : K := (x.k1-x.k0 : Nat)
def coordinateDifference (A : AffineData K P) (embed : Q → P) (x : Window Q r) : K :=
  A.diff (embed x.upper) (embed x.lower)
def frequency (A : AffineData K P) (embed : Q → P) (x : Window Q r) : K :=
  countDifference x / coordinateDifference A embed x
def period (A : AffineData K P) (embed : Q → P) (x : Window Q r) : K :=
  (frequency A embed x)⁻¹

theorem count_difference_positive (x : Window Q r) : 0 < (countDifference x : K) := by
  exact Nat.cast_pos.mpr (Nat.sub_pos_of_lt x.increasing)

theorem coordinate_difference_positive (A : AffineData K P) (embed : Q → P)
    (strict : ∀ a b, r a b ↔ embed a < embed b) (x : Window Q r) :
    0 < coordinateDifference A embed x :=
  (A.strict_sign _ _).mp ((strict _ _).mp x.ordered)

theorem frequency_positive (A : AffineData K P) (embed : Q → P)
    (strict : ∀ a b, r a b ↔ embed a < embed b) (x : Window Q r) :
    0 < frequency A embed x :=
  div_pos (count_difference_positive x) (coordinate_difference_positive A embed strict x)

theorem period_positive_and_product (A : AffineData K P) (embed : Q → P)
    (strict : ∀ a b, r a b ↔ embed a < embed b) (x : Window Q r) :
    0 < period A embed x ∧ frequency A embed x * period A embed x = 1 :=
  ⟨inv_pos.mpr (frequency_positive A embed strict x),
    mul_inv_cancel₀ (ne_of_gt (frequency_positive A embed strict x))⟩

theorem window_constant_value_unique (A : AffineData K P) (embed : Q → P)
    (W : Set (Window Q r)) (nonempty : W.Nonempty)
    (constant : ∀ x ∈ W, ∀ y ∈ W, frequency A embed x = frequency A embed y) :
    ∃! value : K, ∀ x ∈ W, frequency A embed x = value := by
  obtain ⟨x,hx⟩ := nonempty
  refine ⟨frequency A embed x,fun y hy => constant y hy x hx,?_⟩
  intro value h
  exact (h x hx).symm

theorem period_window_invariance (A : AffineData K P) (embed : Q → P)
    (x y : Window Q r) (same : frequency A embed x = frequency A embed y) :
    period A embed x = period A embed y := congrArg Inv.inv same

def hzNumber (value unit : K) : K := value / unit
def hzUnit (standard : K) (n : Nat) : K := standard / (n : K)

theorem hz_number_positive (value unit : K) (hv : 0 < value) (hu : 0 < unit) :
    0 < hzNumber value unit := div_pos hv hu

theorem standard_normalization (standard : K) (n : Nat) (hs : 0 < standard) (hn : 0 < n) :
    0 < hzUnit standard n ∧ hzNumber standard (hzUnit standard n) = (n : K) := by
  constructor
  · exact div_pos hs (Nat.cast_pos.mpr hn)
  · exact div_div_cancel₀ (ne_of_gt hs)

theorem zero_count_invalidates_product (d : K) :
    (0 / d) * (0 / d)⁻¹ ≠ (1 : K) := by
  simp only [zero_div,inv_zero,mul_zero,ne_eq,zero_ne_one,not_false_eq_true]

end LCTR.CoreAffineFrequency
