import CoreComparisonScope

namespace LCTR.CoreComparisonDefinitionInterfaces
set_option autoImplicit false
open Set LCTR.CoreTokenGraph LCTR.CoreEvaluation LCTR.CoreFiniteAudit
open LCTR.CoreComparisonFailure LCTR.CoreComparisonScope LCTR.CoreFirstFailureReport
open LCTR.SelectedInputEvaluation

noncomputable def indicator (P : Prop) : ℕ := by
  classical
  exact if P then 1 else 0
noncomputable def memberIndicator {X : Type} (A : Set X) (x : X) : ℕ := indicator (x ∈ A)

theorem indicator_true (P : Prop) (h : P) : indicator P = 1 := by simp [indicator,h]
theorem indicator_false (P : Prop) (h : ¬ P) : indicator P = 0 := by simp [indicator,h]
theorem membership_indicator {X : Type} (A : Set X) (x : X) :
    memberIndicator A x = indicator (x ∈ A) := rfl

def inputReady : Token → Bool := fun _ => true
noncomputable def raw (localConditions : Fin 7 → Prop) (gluing : Prop) (t : Token) : Bool := by
  classical
  exact if h : t.1 = 0 then
    decide (condition localConditions gluing ⟨t.2.val,by simpa [count,h] using t.2.isLt⟩)
  else true

theorem raw_exact (localConditions : Fin 7 → Prop) (gluing : Prop) (i : Fin 8) :
    raw localConditions gluing (cmpToken i) = true ↔ condition localConditions gluing i := by
  classical
  change decide (condition localConditions gluing i) = true ↔ condition localConditions gluing i
  exact decide_eq_true_iff

theorem raw_local (localConditions : Fin 7 → Prop) (gluing : Prop) (i : Fin 7) :
    raw localConditions gluing (cmpToken i.castSucc) = true ↔ localConditions i := by
  rw [raw_exact]
  simp [condition,i.isLt]

theorem raw_gluing (localConditions : Fin 7 → Prop) (gluing : Prop) :
    raw localConditions gluing (cmpToken 7) = true ↔ gluing := by
  rw [raw_exact]
  simp [condition]

theorem readiness (i : Fin 8) :
    inputReady (cmpToken i) = true ∧ inputReady (cmpToken i) = true := ⟨rfl,rfl⟩

theorem first_prefix_empty (localConditions : Fin 7 → Prop) (gluing : Prop) :
    Prefix (raw localConditions gluing) 0 := by simp [Prefix]

theorem failed_exact (localConditions : Fin 7 → Prop) (gluing : Prop) (i : Fin 8) :
    run inputReady inputReady (raw localConditions gluing) 40 (cmpToken i) = .failed ↔
      Prefix (raw localConditions gluing) i ∧ ¬ condition localConditions gluing i := by
  rw [comparison_failed_prefix _ _ _ _ (finite_run_solves _ _ _) readiness]
  unfold First
  exact and_congr Iff.rfl (Bool.eq_false_iff.trans (not_congr (raw_exact localConditions gluing i)))

theorem failed_token_membership (localConditions : Fin 7 → Prop) (gluing : Prop) (i : Fin 8) :
    cmpToken i ∈ failedSet (run inputReady inputReady (raw localConditions gluing) 40) ↔
      Prefix (raw localConditions gluing) i ∧ ¬ condition localConditions gluing i :=
  failed_exact localConditions gluing i

theorem failure_domain_partition (localConditions : Fin 7 → Prop) (gluing : Prop) :
    ¬ operative localConditions gluing ↔
      ∃! i : Fin 8, run inputReady inputReady (raw localConditions gluing) 40 (cmpToken i) = .failed :=
  native_first_failure_unique localConditions gluing inputReady inputReady
    (raw localConditions gluing) readiness (raw_exact localConditions gluing)

theorem signature_indicator (localConditions : Fin 7 → Prop) (gluing : Prop) (i : Fin 8) :
    CoreComparisonFailure.signature (run inputReady inputReady (raw localConditions gluing) 40) i =
      memberIndicator (failedSet (run inputReady inputReady (raw localConditions gluing) 40)) (cmpToken i) := by
  classical
  by_cases h : run inputReady inputReady (raw localConditions gluing) 40 (cmpToken i) = .failed
  all_goals simp [CoreComparisonFailure.signature,memberIndicator,indicator,failedSet,h]

theorem signature_binary (s : Token → State) (i : Fin 8) :
    CoreComparisonFailure.signature s i = 0 ∨ CoreComparisonFailure.signature s i = 1 := by
  unfold CoreComparisonFailure.signature
  split_ifs <;> simp

end LCTR.CoreComparisonDefinitionInterfaces
