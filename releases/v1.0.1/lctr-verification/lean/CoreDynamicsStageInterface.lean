import CoreDynamicsTokens

namespace LCTR.CoreDynamicsStageInterface
set_option autoImplicit false
open LCTR.CoreTokenGraph LCTR.CoreEvaluation LCTR.CoreDynamicsTokens
open LCTR.SelectedInputEvaluation

structure Conditions where
  generatedOrder : Prop
  trajectoryDescent : Prop
  trajectoryFunction : Prop
  observableDescent : Prop
  changeCommutation : Prop
  incomparabilityTransitive : Prop
  realEmbedding : Prop
  trajectoryFactor : Prop

def indexed (p : Conditions) (i : Fin 8) : Prop :=
  match i.val with
  | 0 => p.generatedOrder
  | 1 => p.trajectoryDescent
  | 2 => p.trajectoryFunction
  | 3 => p.observableDescent
  | 4 => p.changeCommutation
  | 5 => p.incomparabilityTransitive
  | 6 => p.realEmbedding
  | _ => p.trajectoryFactor
def canonicalBundle (p : Conditions) : Prop :=
  p.generatedOrder ∧ p.trajectoryDescent ∧ p.trajectoryFunction
def lawBundle (p : Conditions) : Prop :=
  canonicalBundle p ∧ p.observableDescent ∧ p.changeCommutation
def allConditions (p : Conditions) : Prop :=
  lawBundle p ∧ p.incomparabilityTransitive ∧ p.realEmbedding ∧ p.trajectoryFactor

theorem index_assignment (p : Conditions) :
    indexed p 0 = p.generatedOrder ∧ indexed p 1 = p.trajectoryDescent ∧
    indexed p 2 = p.trajectoryFunction ∧ indexed p 3 = p.observableDescent ∧
    indexed p 4 = p.changeCommutation ∧ indexed p 5 = p.incomparabilityTransitive ∧
    indexed p 6 = p.realEmbedding ∧ indexed p 7 = p.trajectoryFactor := by
  simp [indexed]

theorem canonical_bundle (p : Conditions) :
    canonicalBundle p ↔ indexed p 0 ∧ indexed p 1 ∧ indexed p 2 := by
  simp [canonicalBundle, indexed]

theorem law_bundle (p : Conditions) :
    lawBundle p ↔ canonicalBundle p ∧ indexed p 3 ∧ indexed p 4 := by
  simp [lawBundle, indexed]

theorem all_conditions (p : Conditions) : allConditions p ↔ ∀ i, indexed p i := by
  simp [allConditions, lawBundle, canonicalBundle, indexed, Fin.forall_fin_succ, and_assoc]

theorem readiness_exact (exactInput : Prop) (f e : Token → Bool)
    (s : Token → State) (formExact : ∀ i, f (token i) = true → exactInput)
    (i : Node) (ready : Ready f e s i) : exactInput :=
  formExact i ready.1

theorem failure_exact (exactInput : Prop) (f e c : Token → Bool)
    (s : Token → State) (rec : Recurs Edge f e c s)
    (formExact : ∀ i, f (token i) = true → exactInput)
    (i : Node) (failed : s (token i) = .failed) : exactInput :=
  readiness_exact exactInput f e s formExact i
    ((recursive_failure f e c s rec i).mp failed).1

theorem outside_exact_unformed (exactInput : Prop) (f e c : Token → Bool)
    (s : Token → State) (rec : Recurs Edge f e c s)
    (formExact : ∀ i, f (token i) = true → exactInput)
    (outside : ¬ exactInput) (i : Node) : s (token i) = .unformed := by
  have hf : f (token i) = false := by
    cases h : f (token i)
    · rfl
    · exact False.elim (outside (formExact i h))
  rw [rec (token i)]
  simp [update, hf, state]

theorem condition_failure (p : Conditions) (f e c : Token → Bool)
    (s : Token → State) (rec : Recurs Edge f e c s)
    (assignment : ∀ i, c (token i) = true ↔ indexed p i) (i : Node) :
    token i ∈ FailedStrict s ↔ Ready f e s i ∧ ¬ indexed p i :=
  condition_correspondence f e c s rec (indexed p) assignment i

end LCTR.CoreDynamicsStageInterface
