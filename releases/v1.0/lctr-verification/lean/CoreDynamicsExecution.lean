import CoreDynamicsTokens

namespace LCTR.CoreDynamicsExecution
set_option autoImplicit false
open LCTR.CoreDynamicsTokens LCTR.CoreTokenGraph LCTR.CoreFiniteAudit
open LCTR.CoreEvaluation LCTR.SelectedInputEvaluation
open LCTR.CoreContinuumIntegration (all_sat_iff_tests)

def testCondition (b : Node → Bool) (t : Token) : Bool :=
  if h : t.1 = (2 : Fin 6) then b ⟨t.2.val,by simpa [h,count] using t.2.isLt⟩ else true
def testState (b : Node → Bool) : Token → State :=
  run (fun _ => true) (fun _ => true) (testCondition b) 40

theorem upstream_passes (b : Node → Bool) :
    ∀ t, series t < 2 → testState b t = .sat := by
  have outside : ∀ x y : Token, series x < 2 → Edge y x → series y < 2 := by decide
  apply (all_sat_iff_tests Edge
    (LCTR.CoreDagRecursion.finite_acyclic_wellFounded Edge acyclic)
    (fun _ => true) (fun _ => true) (testCondition b) (testState b)
    (finite_run_solves _ _ _) {t | series t < 2} (fun _ _ => ⟨rfl,rfl⟩) ?_).mpr
  · intro t ht
    have ne : t.1 ≠ (2 : Fin 6) := by
      intro eq
      change t.1.val < 2 at ht
      have h := congrArg Fin.val eq
      omega
    simp [testCondition,ne]
  · intro x hx y hy hn
    exact False.elim (hn (outside x y hx hy))

theorem test_input_sat (b : Node → Bool) :
    InputSat (fun _ => true) (fun _ => true) (testState b) :=
  ⟨fun _ => ⟨rfl,rfl⟩,fun t ht => upstream_passes b t (by omega)⟩

theorem root_failure (b : Node → Bool) (i : Node)
    (root : i.val ∈ [0,1,3,4]) : testState b (token i) = .failed ↔ b i = false := by
  have edges : ∀ i : Node, i.val ∈ [0,1,3,4] → ∀ y : Token,
      Edge y (token i) → series y = 1 := by decide
  have ready : Ready (fun _ => true) (fun _ => true) (testState b) i :=
    ⟨rfl,rfl,fun y hy => upstream_passes b y (by have h := edges i root y hy; omega)⟩
  rw [recursive_failure (fun _ => true) (fun _ => true) (testCondition b)
    (testState b) (finite_run_solves _ _ _) i, and_iff_right ready]
  simp [testCondition,token]

theorem four_root_failures_and_descendants :
    let s := testState (fun _ => false)
    s (token 0) = .failed ∧ s (token 1) = .failed ∧
    s (token 3) = .failed ∧ s (token 4) = .failed ∧
    s (token 2) = .unformed ∧ s (token 5) = .unformed ∧
    s (token 6) = .unformed ∧ s (token 7) = .unformed := by
  have h0 := (root_failure (fun _ => false) 0 (by decide)).mpr rfl
  have h1 := (root_failure (fun _ => false) 1 (by decide)).mpr rfl
  have h2 : testState (fun _ => false) (token 2) = .unformed := by
    apply direct_nonsat_unformed Edge _ _ _ _ (finite_run_solves _ _ _) (show Edge (token 1) (token 2) by decide)
    change testState (fun _ => false) (token 1) ≠ .sat
    rw [h1]
    decide
  have h5 : testState (fun _ => false) (token 5) = .unformed := by
    apply direct_nonsat_unformed Edge _ _ _ _ (finite_run_solves _ _ _) (show Edge (token 0) (token 5) by decide)
    change testState (fun _ => false) (token 0) ≠ .sat
    rw [h0]
    decide
  have no5 : testState (fun _ => false) (token 5) ≠ .sat := by rw [h5]; decide
  exact ⟨h0,h1,(root_failure (fun _ => false) 3 (by decide)).mpr rfl,
    (root_failure (fun _ => false) 4 (by decide)).mpr rfl,h2,h5,
    direct_nonsat_unformed Edge _ _ _ _ (finite_run_solves _ _ _) (by decide) no5,
    direct_nonsat_unformed Edge _ _ _ _ (finite_run_solves _ _ _) (by decide) no5⟩

def lateProfile (i : Node) : Bool := decide (i.val ≠ 6 ∧ i.val ≠ 7)

theorem final_pair_failure :
    testState lateProfile (token 6) = .failed ∧ testState lateProfile (token 7) = .failed := by
  have rankCheck : ∀ i j : Node, scalarRank (token j) < scalarRank (token i) → lateProfile j = true := by decide
  have ready : ∀ i : Node, Ready (fun _ => true) (fun _ => true) (testState lateProfile) i := by
    intro i
    apply (ready_iff_ancestor_conditions _ _ _ _ (finite_run_solves _ _ _) (test_input_sat lateProfile) i).mpr
    intro j hp
    have hj := rankCheck i j (path_increases Edge (· < ·) scalarRank (fun _ _ => edge_rank_increasing) hp)
    simpa [testCondition,token] using hj
  constructor
  · apply (recursive_failure _ _ _ _ (finite_run_solves _ _ _) 6).mpr
    exact ⟨ready 6,by simp [testCondition,token,lateProfile]⟩
  · apply (recursive_failure _ _ _ _ (finite_run_solves _ _ _) 7).mpr
    exact ⟨ready 7,by simp [testCondition,token,lateProfile]⟩

def absentFormation (t : Token) : Bool := decide (t ≠ token 0)
def absentState : Token → State :=
  run absentFormation (fun _ => true) absentFormation 40

theorem absent_upstream_passes : ∀ t, series t < 2 → absentState t = .sat := by
  have outside : ∀ x y : Token, series x < 2 → Edge y x → series y < 2 := by decide
  have formed : ∀ t, series t < 2 → absentFormation t = true := by
    intro t ht
    simp only [absentFormation,decide_eq_true_eq]
    intro eq
    subst t
    norm_num [series,token] at ht
  apply (all_sat_iff_tests Edge
    (LCTR.CoreDagRecursion.finite_acyclic_wellFounded Edge acyclic)
    absentFormation (fun _ => true) absentFormation absentState
    (finite_run_solves _ _ _) {t | series t < 2} (fun t ht => ⟨formed t ht,rfl⟩) ?_).mpr
  · exact formed
  · intro x hx y hy hn
    exact False.elim (hn (outside x y hx hy))

theorem missing_formation_not_failure :
    absentState (token 0) = .unformed ∧ absentState (token 0) ≠ .failed := by
  have h : absentState (token 0) = .unformed := by
    rw [show absentState (token 0) = update Edge absentFormation (fun _ => true)
      absentFormation (token 0) (fun y => absentState y.val) from finite_run_solves _ _ _ (token 0)]
    simp [update,absentFormation,state]
  exact ⟨h,by rw [h]; decide⟩

theorem missing_formation_blocks_descendant : absentState (token 5) = .unformed := by
  apply direct_nonsat_unformed Edge _ _ _ _ (finite_run_solves _ _ _) (show Edge (token 0) (token 5) by decide)
  change absentState (token 0) ≠ .sat
  rw [missing_formation_not_failure.1]
  decide

end LCTR.CoreDynamicsExecution
