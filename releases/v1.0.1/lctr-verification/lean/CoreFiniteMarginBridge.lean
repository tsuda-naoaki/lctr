import CoreContinuumEncoding

namespace LCTR.CoreFiniteMarginBridge
open LCTR.CoreContinuumBoundary LCTR.CoreContinuumEncoding
open scoped ENNReal NNReal

theorem arith_elim_gt (t s : ℝ) : (t > s) ↔ ¬ (s ≥ t) := by
  exact (not_le).symm
theorem arith_elim_leq (t s : ℝ) : (t ≤ s) ↔ (s ≥ t) := by rfl
theorem arith_elim_lt (t s : ℝ) : (t < s) ↔ ¬ (t ≥ s) := by
  exact (not_le).symm
theorem arith_eq_elim_real (t s : ℝ) : (t = s) ↔ (t ≥ s ∧ t ≤ s) := by
  constructor
  · rintro rfl; exact ⟨le_rfl, le_rfl⟩
  · rintro ⟨h₁,h₂⟩; exact le_antisymm h₂ h₁

theorem finite_margin (a b : ℝ≥0∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    margin a b = ((a.toReal - b.toReal : ℝ) : EReal) := by
  simp only [margin, if_neg ha, if_neg hb]

theorem finite_excess (a b : ℝ≥0∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    excess a b = ((if a.toReal - b.toReal < 0
      then -(a.toReal - b.toReal) else 0 : ℝ) : EReal) := by
  rw [excess, finite_margin a b ha hb]
  by_cases h : a.toReal - b.toReal < 0
  · rw [if_pos h, max_eq_right]
    · rfl
    · exact le_of_lt (EReal.neg_pos.mpr (EReal.coe_neg'.mpr h))
  · rw [if_neg h, max_eq_left]
    · rfl
    · exact EReal.neg_le_zero.mpr (EReal.coe_nonneg.mpr (not_lt.mp h))

theorem bool_defect_real (b : Bool) :
    (boolDefect b).toReal = (if b then (0 : ℝ) else 1) := by
  cases b <;> simp [boolDefect]
theorem half_real : half.toReal = (1/2 : ℝ) := by
  norm_num [half]

theorem reject_reverse_margin :
    ¬ (((0 : ℝ) - 1 ≥ 0) ↔ ((0 : ℝ) ≤ 1)) := by norm_num
theorem reject_zero_threshold_robust :
    ¬ (((0 : ℝ) - (if true then 0 else 1) > 0) ↔ (true = true)) := by norm_num
theorem reject_unit_threshold :
    ¬ (((if false then (0 : ℝ) else 1) ≤ 1) ↔ (false = true)) := by norm_num

#print axioms arith_elim_gt
#print axioms arith_elim_leq
#print axioms arith_elim_lt
#print axioms arith_eq_elim_real
#print axioms finite_margin
#print axioms finite_excess
#print axioms bool_defect_real
#print axioms half_real
#print axioms reject_reverse_margin
#print axioms reject_zero_threshold_robust
#print axioms reject_unit_threshold
end LCTR.CoreFiniteMarginBridge
