import CoreContinuumTopology
import Mathlib.Tactic.NormNum
import Mathlib.Data.ENNReal.Inv

namespace LCTR.CoreContinuumEncoding
set_option autoImplicit false
open LCTR.CoreContinuumBoundary LCTR.CoreContinuumIntegration LCTR.CoreContinuumTopology
open LCTR.CoreTokenGraph LCTR.CoreEvaluation LCTR.SelectedInputEvaluation
open scoped ENNReal NNReal

def boolDefect (b : Bool) : ℝ≥0∞ := if b then 0 else 1
noncomputable def half : ℝ≥0∞ := ((1/2 : ℝ≥0) : ℝ≥0∞)

theorem half_exact : half = (1/2 : ℝ≥0∞) := by
  simp [half]

theorem midpoint_encoding (b : Bool) : boolDefect b ≤ half ↔ b = true := by
  cases b <;> norm_num [boolDefect,half]

theorem midpoint_margin (b : Bool) :
    margin half (boolDefect b) = if b then ((1/2 : ℝ) : EReal) else -((1/2 : ℝ) : EReal) := by
  cases b <;> norm_num [boolDefect,margin,half]

theorem midpoint_positive_margin (b : Bool) :
    0 < margin half (boolDefect b) ↔ b = true := by
  rw [margin_positive]
  cases b <;> norm_num [boolDefect,half]

noncomputable def paperCondition (d eps : Fin 9 → ℝ≥0∞) (b : Fin 9 → Bool) (i : Fin 9) : Bool :=
  if i.val < 6 then by classical exact decide (d i ≤ eps i) else b i
def paperDefect (d : Fin 9 → ℝ≥0∞) (b : Fin 9 → Bool) (i : Fin 9) : ℝ≥0∞ :=
  if i.val < 6 then d i else boolDefect (b i)
noncomputable def paperTolerance (eps : Fin 9 → ℝ≥0∞) (i : Fin 9) : ℝ≥0∞ :=
  if i.val < 6 then eps i else half

theorem nine_component_encoding (d eps : Fin 9 → ℝ≥0∞) (b : Fin 9 → Bool) (i : Fin 9) :
    paperCondition d eps b i = true ↔ paperDefect d b i ≤ paperTolerance eps i := by
  classical
  by_cases h : i.val < 6
  · simp [paperCondition,paperDefect,paperTolerance,h]
  · simp only [paperCondition,paperDefect,paperTolerance,if_neg h]
    exact (midpoint_encoding (b i)).symm

theorem first_six_preserved (d eps : Fin 9 → ℝ≥0∞) (b : Fin 9 → Bool) (i : Fin 9) (h : i.val < 6) :
    paperDefect d b i = d i ∧ paperTolerance eps i = eps i := by
  simp [paperDefect,paperTolerance,h]

theorem final_three_margin (d eps : Fin 9 → ℝ≥0∞) (b : Fin 9 → Bool) (i : Fin 9) (h : ¬ i.val < 6) :
    margin (paperTolerance eps i) (paperDefect d b i) =
    if b i then ((1/2 : ℝ) : EReal) else -((1/2 : ℝ) : EReal) := by
  simpa only [paperDefect,paperTolerance,if_neg h] using midpoint_margin (b i)

theorem source_quantitative_validity (f e c : Token → Bool) (s : Token → State)
    (h : Recurs Edge f e c s) (inp : InputSat f e s)
    (d eps : Fin 9 → ℝ≥0∞) (b : Fin 9 → Bool)
    (matching : ∀ i, c (approxToken i) = paperCondition d eps b i) :
    ((∀ i, s (approxToken i) = .sat) ↔ Valid (paperDefect d b) (paperTolerance eps)) ∧
    ((∀ i, s (approxToken i) = .sat) ↔ ∀ i, 0 ≤ margin (paperTolerance eps i) (paperDefect d b i)) ∧
    ((∀ i, s (approxToken i) = .sat) ↔ ∀ i, excess (paperTolerance eps i) (paperDefect d b i) = 0) ∧
    ((∀ i, s (approxToken i) = .sat) ↔ Exceeded (paperDefect d b) (paperTolerance eps) = ∅) := by
  apply quantitative_validity f e c s h inp (paperDefect d b) (paperTolerance eps)
  intro i
  rw [matching i]
  exact nine_component_encoding d eps b i

theorem source_robust_validity (f e c : Token → Bool) (s : Token → State)
    (h : Recurs Edge f e c s) (inp : InputSat f e s)
    (d eps : Fin 9 → ℝ≥0∞) (b : Fin 9 → Bool)
    (matching : ∀ i, c (approxToken i) = paperCondition d eps b i) :
    OperationalRobust s (paperDefect d b) (paperTolerance eps) ↔
    ∀ i, 0 < margin (paperTolerance eps i) (paperDefect d b i) := by
  apply robust_positive_iff f e c s h inp (paperDefect d b) (paperTolerance eps)
  intro i; rw [matching i]; exact nine_component_encoding d eps b i

theorem wrong_threshold_controls :
    ¬ (0 < margin 0 (boolDefect true)) ∧ boolDefect false ≤ (1 : ℝ≥0∞) := by
  norm_num [margin,boolDefect]

end LCTR.CoreContinuumEncoding
