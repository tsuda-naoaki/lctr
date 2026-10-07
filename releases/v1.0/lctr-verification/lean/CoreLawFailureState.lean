import CoreNativeLawFailure
import CoreEvaluation

namespace LCTR.CoreLawFailureState
set_option autoImplicit false
open LCTR.CoreLawConditionGraph LCTR.CoreNativeLawFailure
open LCTR.SelectedInputEvaluation LCTR.CoreEvaluation
variable {E T A : Type} {X Y : A → Type}
variable (s : Selection (E := E) (T := T) (A := A) (X := X) (Y := Y)) (e : E)

noncomputable def truth (i : Node) : Bool := by classical exact decide (totalCondition s e i)
noncomputable def available : Bool := by classical exact decide (s.domain e)

noncomputable def idealState (i : Node) : State := by
  classical
  exact if totalCondition s e i then .sat
    else if s.domain e ∧ ancestorAll s e i then .failed else .unformed

theorem ideal_sat_iff (i : Node) : idealState s e i = .sat ↔ totalCondition s e i := by
  classical
  unfold idealState
  split_ifs <;> simp_all

theorem total_ancestor_condition (i j : Node) (path : Relation.TransGen Edge i j)
    (holds : totalCondition s e j) : totalCondition s e i := by
  obtain ⟨hd,hj⟩ := holds
  exact ⟨hd,ancestor_conditions_hold (s.datum ⟨e,hd⟩) i j path hj⟩

theorem direct_pass_iff_ancestors (i : Node) :
    (∀ j : {j : Node // Edge j i}, idealState s e j.val = .sat) ↔ ancestorAll s e i := by
  constructor
  · intro hd j hj
    have path := (ancestors_exact j i).mpr hj
    cases path with
    | single edge => exact (ideal_sat_iff s e j).mp (hd ⟨j,edge⟩)
    | tail path edge =>
      exact total_ancestor_condition s e _ _ path ((ideal_sat_iff s e _).mp (hd ⟨_,edge⟩))
  · intro ha j
    exact (ideal_sat_iff s e j.val).mpr (ha j.val (Or.inl j.property))

theorem ideal_recursion :
    Recurs Edge (fun _ => available s e) (fun _ => true) (truth s e) (idealState s e) := by
  classical
  intro i
  have prior := direct_pass_iff_ancestors s e i
  simp only [update]
  rw [propext prior]
  by_cases hc : totalCondition s e i
  · have hd : s.domain e := hc.1
    have ha : ancestorAll s e i :=
      fun j path => total_ancestor_condition s e j i ((ancestors_exact j i).mpr path) hc
    simp [idealState,available,truth,state,hc,hd,ha]
  · by_cases ready : s.domain e ∧ ancestorAll s e i
    · simp only [idealState,available,truth,state]
      simp_all
    · by_cases hd : s.domain e
      · have ha : ¬ ancestorAll s e i := fun h => ready ⟨hd,h⟩
        simp [idealState,available,state,hc,hd,ha]
      · simp only [idealState,available,truth,state]
        simp_all

theorem recursive_state_unique (q : Node → State)
    (recursion : Recurs Edge (fun _ => available s e) (fun _ => true) (truth s e) q) :
    q = idealState s e := by
  have result := unique_state_recursion Edge
    (LCTR.CoreDagRecursion.finite_acyclic_wellFounded Edge acyclic)
    (fun _ => available s e) (fun _ => true) (truth s e)
  obtain ⟨r,_,unique⟩ := result
  exact (unique q recursion).trans (unique (idealState s e) (ideal_recursion s e)).symm

theorem ideal_failed_iff (i : Node) : idealState s e i = .failed ↔ minimalClass s e i := by
  classical
  unfold idealState minimalClass
  split_ifs <;> simp_all

theorem recursive_failed_iff (q : Node → State)
    (recursion : Recurs Edge (fun _ => available s e) (fun _ => true) (truth s e) q) (i : Node) :
    q i = .failed ↔ minimalClass s e i := by
  rw [recursive_state_unique s e q recursion]
  exact ideal_failed_iff s e i

theorem recursive_completion_iff (q : Node → State)
    (recursion : Recurs Edge (fun _ => available s e) (fun _ => true) (truth s e) q)
    (h : s.domain e) :
    (∀ i, q i = .sat) ↔ LCTR.LawFamilyTransport.AllConditions (s.datum ⟨e,h⟩) := by
  rw [recursive_state_unique s e q recursion]
  exact (forall_congr' (ideal_sat_iff s e)).trans
    ((forall_congr' (selected_condition_exact s e h)).trans (all_conditions_exact _))

theorem recursive_failure_exists_iff (q : Node → State)
    (recursion : Recurs Edge (fun _ => available s e) (fun _ => true) (truth s e) q) :
    (∃ i, q i = .failed) ↔ failure s e := by
  exact (exists_congr fun i => recursive_failed_iff s e q recursion i).trans
    (failure_covered_by_minimal_classes s e).symm

end LCTR.CoreLawFailureState
