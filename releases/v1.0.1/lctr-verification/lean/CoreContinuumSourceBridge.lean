import CoreContinuumEncoding

namespace LCTR.CoreContinuumSourceBridge
set_option autoImplicit false
open LCTR.CoreContinuumBoundary LCTR.CoreContinuumIntegration LCTR.CoreContinuumEncoding
open LCTR.CoreTokenGraph LCTR.CoreEvaluation LCTR.SelectedInputEvaluation
open scoped ENNReal
variable {E L : Type*}

def approxDomain (s : E → L → Token → State) : Set (E × L) :=
  {x | ∀ i : Fin 9, s x.1 x.2 (approxToken i) = .sat}
def scaleFibre (s : E → L → Token → State) (ev : E) : Set L :=
  {l | (ev,l) ∈ approxDomain s}
def conditionAll (c : Token → Bool) : Prop := ∀ i : Fin 9, c (approxToken i) = true

theorem fibre_membership (s : E → L → Token → State) (ev : E) (l : L) :
    l ∈ scaleFibre s ev ↔ (ev,l) ∈ approxDomain s := by rfl

theorem eight_conditions (s : E → L → Token → State) (ev : E) (l : L)
    (f e c : Token → Bool) (d eps : Fin 9 → ℝ≥0∞) (b : Fin 9 → Bool)
    (recurs : Recurs Edge f e c (s ev l)) (inp : InputSat f e (s ev l))
    (matching : ∀ i, c (approxToken i) = paperCondition d eps b i) :
    (l ∈ scaleFibre s ev ↔ (ev,l) ∈ approxDomain s) ∧
    ((ev,l) ∈ approxDomain s ↔ conditionAll c) ∧
    (conditionAll c ↔ ∀ i, c (approxToken i) = true) ∧
    ((∀ i, c (approxToken i) = true) ↔ ∀ i, paperDefect d b i ≤ paperTolerance eps i) ∧
    ((∀ i, paperDefect d b i ≤ paperTolerance eps i) ↔
      ∀ i, 0 ≤ margin (paperTolerance eps i) (paperDefect d b i)) ∧
    ((∀ i, 0 ≤ margin (paperTolerance eps i) (paperDefect d b i)) ↔
      ∀ i, excess (paperTolerance eps i) (paperDefect d b i) = 0) ∧
    ((∀ i, excess (paperTolerance eps i) (paperDefect d b i) = 0) ↔
      Exceeded (paperDefect d b) (paperTolerance eps) = ∅) := by
  have q := validity_characterizations (paperDefect d b) (paperTolerance eps)
  refine ⟨fibre_membership s ev l, approx_states_iff_conditions f e c (s ev l) recurs inp,
    Iff.rfl, ?_, q.1, q.1.symm.trans q.2.1, q.2.1.symm.trans q.2.2⟩
  apply forall_congr'
  intro i
  rw [matching i]
  exact nine_component_encoding d eps b i

#print axioms fibre_membership
#print axioms eight_conditions
end LCTR.CoreContinuumSourceBridge
