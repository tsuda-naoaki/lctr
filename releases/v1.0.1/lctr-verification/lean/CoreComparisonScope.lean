import CoreComparisonFailure
import CoreFirstFailureReport

namespace LCTR.CoreComparisonScope
set_option autoImplicit false
open Set LCTR.CoreTokenGraph LCTR.CoreEvaluation LCTR.CoreFiniteAudit
open LCTR.SelectedInputEvaluation LCTR.CoreComparisonFailure LCTR.CoreFirstFailureReport

def condition (localConditions : Fin 7 → Prop) (gluingCondition : Prop) (i : Fin 8) : Prop :=
  if h : i.val < 7 then localConditions ⟨i.val,h⟩ else gluingCondition

def operative (localConditions : Fin 7 → Prop) (gluingCondition : Prop) : Prop := (∀ i, localConditions i) ∧ gluingCondition

theorem all_conditions_iff_operative (localConditions : Fin 7 → Prop) (gluingCondition : Prop) :
    (∀ i, condition localConditions gluingCondition i) ↔ operative localConditions gluingCondition := by
  constructor
  · intro h
    constructor
    · intro j
      simpa [condition,j.isLt] using h j.castSucc
    · simpa [condition] using h 7
  · rintro ⟨hl,hg⟩ i
    unfold condition
    split_ifs with h
    · exact hl ⟨i.val,h⟩
    · exact hg

theorem failure_condition_equivalence (localConditions : Fin 7 → Prop) (gluingCondition : Prop) :
    ¬ operative localConditions gluingCondition ↔ ¬ ((∀ i, localConditions i) ∧ gluingCondition) := Iff.rfl

theorem assigned_failure_equivalence (localConditions : Fin 7 → Prop) (gluingCondition : Prop)
    (c : Token → Bool) (assignment : ∀ i, c (cmpToken i) = true ↔ condition localConditions gluingCondition i) :
    ¬ operative localConditions gluingCondition ↔ ¬ ∀ i, c (cmpToken i) = true := by
  rw [← all_conditions_iff_operative localConditions gluingCondition]
  exact not_congr (forall_congr' assignment).symm

theorem native_first_failure_unique (localConditions : Fin 7 → Prop) (gluingCondition : Prop)
    (f e c : Token → Bool)
    (ready : ∀ i, f (cmpToken i) = true ∧ e (cmpToken i) = true)
    (assignment : ∀ i, c (cmpToken i) = true ↔ condition localConditions gluingCondition i) :
    ¬ operative localConditions gluingCondition ↔ ∃! i : Fin 8, run f e c 40 (cmpToken i) = .failed :=
  (assigned_failure_equivalence localConditions gluingCondition c assignment).trans (native_failure_partition f e c ready)

theorem native_failed_class_membership (f e c : Token → Bool)
    (ready : ∀ i, f (cmpToken i) = true ∧ e (cmpToken i) = true) (i : Fin 8) :
    cmpToken i ∈ failedSet (run f e c 40) ↔ First c i :=
  comparison_failed_prefix f e c _ (finite_run_solves f e c) ready i

theorem native_series_partition :
    (Set.univ : Set Token) = {t | t.1 = 0} ∪ {t | t.1 ≠ 0} ∧
    Disjoint ({t : Token | t.1 = 0}) {t | t.1 ≠ 0} := by
  constructor
  · ext t; by_cases h : t.1 = 0 <;> simp [h]
  · apply Set.disjoint_left.mpr
    exact fun _ h hn => hn h

theorem comparison_series_exact : {t : Token | t.1 = 0} = Set.range cmpToken := by
  ext t
  constructor
  · rcases t with ⟨i,j⟩
    intro h
    change i = 0 at h
    subst i
    exact ⟨j,rfl⟩
  · rintro ⟨i,rfl⟩
    rfl

theorem native_failed_antichain_and_minimal (f e c : Token → Bool) :
    (∀ a ∈ failedSet (run f e c 40), ∀ b ∈ failedSet (run f e c 40),
      ¬ Relation.TransGen Edge a b) ∧
    minimalSet (run f e c 40) = failedSet (run f e c 40) := by
  refine ⟨?_,minimal_positions_exact f e c _ (finite_run_solves f e c)⟩
  intro a ha b hb
  exact failed_antichain Edge f e c _ (finite_run_solves f e c) ha hb

end LCTR.CoreComparisonScope
