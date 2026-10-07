import CoreDynamicsTokens
import CoreNativeLawFailure
import CoreDifferentialFailure

namespace LCTR.CoreStageBoundaries
set_option autoImplicit false
open LCTR.CoreTokenGraph LCTR.CoreEvaluation LCTR.SelectedInputEvaluation
open LCTR.LawFamilyTransport
variable {E T A Ω : Type} {X Y : A → Type}

def DynOperative (exactInput : E → Prop) (K : E → Fin 8 → Prop) (ev : E) : Prop :=
  exactInput ev ∧ ∀ i, K ev i
def LawOperative (law : Selected E (Family T A X Y)) (ev : E) : Prop :=
  ∃ h : law.domain ev, AllConditions (law.datum ⟨ev,h⟩)
def DiffOperative (law : Selected E (Family T A X Y))
    (diff : MatchingDifferential E (Family T A X Y) (LCTR.DifferentialNativeDomains.Input Ω) law)
    (ev : E) : Prop := ∃ h : diff.domain ev,
  AllConditions (law.datum ⟨ev,diff.subdomain ev h⟩) ∧
    LCTR.DifferentialNativeDomains.complete (diff.structureAt ⟨ev,h⟩)

theorem dynamics_failure_not_operative (exactInput : E → Prop) (K : E → Fin 8 → Prop)
    (ev : E) (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s)
    (assignment : ∀ i, c (LCTR.CoreDynamicsTokens.token i) = true ↔ K ev i)
    (failure : ∃ i, s (LCTR.CoreDynamicsTokens.token i) = .failed) :
    ¬ DynOperative exactInput K ev := by
  rintro ⟨_,allK⟩
  obtain ⟨i,hi⟩ := failure
  have no := ((LCTR.CoreDynamicsTokens.recursive_failure f e c s rec i).mp hi).2
  have yes := (assignment i).mpr (allK i)
  rw [yes] at no
  cases no

theorem law_failure_requires_dynamics (exactInput : E → Prop) (K : E → Fin 8 → Prop)
    (law : Selected E (Family T A X Y))
    (domain : ∀ ev, law.domain ev ↔ DynOperative exactInput K ev) (ev : E)
    (failure : LCTR.CoreNativeLawFailure.failure law ev) : DynOperative exactInput K ev :=
  (domain ev).mp failure.1

theorem dynamics_law_failures_disjoint (exactInput : E → Prop) (K : E → Fin 8 → Prop)
    (law : Selected E (Family T A X Y))
    (domain : ∀ ev, law.domain ev ↔ DynOperative exactInput K ev)
    (ev : E) (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s)
    (assignment : ∀ i, c (LCTR.CoreDynamicsTokens.token i) = true ↔ K ev i) :
    ¬ ((∃ i, s (LCTR.CoreDynamicsTokens.token i) = .failed) ∧
      LCTR.CoreNativeLawFailure.failure law ev) := by
  rintro ⟨hd,hl⟩
  exact dynamics_failure_not_operative exactInput K ev f e c s rec assignment hd
    (law_failure_requires_dynamics exactInput K law domain ev hl)

theorem law_failure_not_operative (law : Selected E (Family T A X Y)) (ev : E)
    (failure : LCTR.CoreNativeLawFailure.failure law ev) : ¬ LawOperative law ev := by
  rintro ⟨h,hl⟩
  exact (LCTR.CoreNativeLawFailure.failure_on_selected_datum law ev h).mp failure hl

variable (law : Selected E (Family T A X Y))
variable (diff : MatchingDifferential E (Family T A X Y) (LCTR.DifferentialNativeDomains.Input Ω) law)

theorem differential_failure_boundary (ev : E)
    (failure : LCTR.CoreDifferentialFailure.failure diff AllConditions ev) :
    LawOperative law ev ∧ ¬ DiffOperative law diff ev := by
  obtain ⟨h,hl⟩ := failure.1
  refine ⟨⟨diff.subdomain ev h,hl⟩,?_⟩
  rintro ⟨h',_,hd⟩
  apply failure.2
  intro i
  exact (LCTR.CoreDifferentialFailure.selected_restricts diff ev h' i).mpr
    ((LCTR.CoreDifferentialFailure.all_conditions_complete _).mpr hd i)

theorem differential_requires_same_law (ev : E) :
    DiffOperative law diff ev → LawOperative law ev := by
  rintro ⟨h,hl,_⟩
  exact ⟨diff.subdomain ev h,hl⟩

theorem law_differential_failures_disjoint (ev : E) :
    ¬ (LCTR.CoreNativeLawFailure.failure law ev ∧
      LCTR.CoreDifferentialFailure.failure diff AllConditions ev) := by
  rintro ⟨hl,hd⟩
  exact law_failure_not_operative law ev hl (differential_failure_boundary law diff ev hd).1

theorem differential_failure_outside_domain (ev : E) (outside : ¬ diff.domain ev) :
    ¬ LCTR.CoreDifferentialFailure.failure diff AllConditions ev :=
  (LCTR.CoreDifferentialFailure.outside_selection_no_failure diff AllConditions ev outside).1

end LCTR.CoreStageBoundaries
