import CoreDifferentialTokens
import CoreContinuumIntegration

namespace LCTR.CoreDifferentialExecution
set_option autoImplicit false
open LCTR.CoreDifferentialFailure LCTR.CoreDifferentialTokens
open LCTR.CoreEvaluation LCTR.SelectedInputEvaluation LCTR.CoreFiniteAudit
open LCTR.CoreTokenGraph (Token series)
open LCTR.CoreContinuumIntegration (all_sat_iff_tests)

def testCondition (b : Node → Bool) (t : Token) : Bool :=
  if h : t.1 = (5 : Fin 6) then
    b ⟨t.2.val,by simpa [h,LCTR.CoreTokenGraph.count] using t.2.isLt⟩ else true
def testState (b : Node → Bool) : Token → State :=
  run (fun _ => true) (fun _ => true) (testCondition b) 40

theorem outside_differential_passes (b : Node → Bool) :
    ∀ t, series t ≠ 5 → testState b t = .sat := by
  have outside : ∀ x y : Token, series x ≠ 5 → FullEdge y x → series y ≠ 5 := by decide
  apply (all_sat_iff_tests FullEdge
    (LCTR.CoreDagRecursion.finite_acyclic_wellFounded FullEdge LCTR.CoreTokenGraph.acyclic)
    (fun _ => true) (fun _ => true) (testCondition b) (testState b)
    (finite_run_solves _ _ _) {t | series t ≠ 5} (fun _ _ => ⟨rfl,rfl⟩) ?_).mpr
  · intro t ht
    have ne : t.1 ≠ (5 : Fin 6) := fun eq => ht (congrArg Fin.val eq)
    simp [testCondition,ne]
  · intro x hx y hy hn
    exact False.elim (hn (outside x y hx hy))

theorem test_ready_and_satisfaction (b : Node → Bool) (i : Node)
    (anc : ∀ j, Ancestor j i → b j = true) :
    Ready (fun _ => true) (fun _ => true) (testState b) i ∧
      (testState b (token i) = .sat ↔ b i = true) := by
  have wf : WellFounded Edge := LCTR.CoreDagRecursion.finite_acyclic_wellFounded Edge
    (fun i h => ancestor_irreflexive i ((ancestors_exact i i).mp h))
  have result : ∀ i : Node, (∀ j, Ancestor j i → b j = true) →
      Ready (fun _ => true) (fun _ => true) (testState b) i ∧
      (testState b (token i) = .sat ↔ b i = true) := by
    intro i
    apply wf.induction i
    intro i ih ha
    have prior : ∀ y, FullEdge y (token i) → testState b y = .sat := by
      intro y hy
      rcases (incoming_edges_exact i y).mp hy with law | ⟨j,rfl,edge⟩
      · exact outside_differential_passes b y (by omega)
      · exact (ih j edge (fun k hk => ha k (ancestor_transitive _ _ _ hk
          (edge_ancestor _ _ edge)))).2.mpr (ha j (edge_ancestor _ _ edge))
    refine ⟨⟨rfl,rfl,prior⟩,?_⟩
    have recursion : Recurs FullEdge (fun _ => true) (fun _ => true) (testCondition b) (testState b) :=
      finite_run_solves _ _ _
    rw [recursion (token i)]
    simp only [update,state_sat_iff,decide_eq_true_eq,true_and]
    rw [← predecessor_iff]
    simpa [testCondition,token] using and_iff_right prior
  exact result i anc

theorem test_failure (b : Node → Bool) (i : Node)
    (anc : ∀ j, Ancestor j i → b j = true) :
    testState b (token i) = .failed ↔ b i = false := by
  simpa [testCondition,token,testState] using ready_failure _ _ _ _
    (finite_run_solves _ _ _) i (test_ready_and_satisfaction b i anc).1

def pairProfile (i : Node) : Bool := decide (i.val < 3)
def tripleProfile (i : Node) : Bool := decide (i.val = 0)
def atlasProfile (_ : Node) : Bool := false

theorem simultaneous_pair_execution :
    testState pairProfile (token 3) = .failed ∧ testState pairProfile (token 4) = .failed ∧
    testState pairProfile (token 0) = .sat ∧ testState pairProfile (token 2) = .sat := by
  have ready : ∀ i : Node, ∀ j, Ancestor j i → pairProfile j = true := by decide
  exact ⟨(test_failure pairProfile 3 (ready 3)).mpr (by decide),
    (test_failure pairProfile 4 (ready 4)).mpr (by decide),
    (test_ready_and_satisfaction pairProfile 0 (ready 0)).2.mpr (by decide),
    (test_ready_and_satisfaction pairProfile 2 (ready 2)).2.mpr (by decide)⟩

theorem simultaneous_three_with_blocked_descendant :
    testState tripleProfile (token 1) = .failed ∧ testState tripleProfile (token 3) = .failed ∧
    testState tripleProfile (token 4) = .failed ∧ testState tripleProfile (token 2) = .unformed := by
  have one : testState tripleProfile (token 1) = .failed :=
    (test_failure tripleProfile 1 (by decide)).mpr (by decide)
  refine ⟨one,(test_failure tripleProfile 3 (by decide)).mpr (by decide),
    (test_failure tripleProfile 4 (by decide)).mpr (by decide),?_⟩
  apply direct_nonsat_unformed FullEdge _ _ _ _ (finite_run_solves _ _ _)
    (show FullEdge (token 1) (token 2) by decide)
  change testState tripleProfile (token 1) ≠ .sat
  rw [one]
  decide

theorem atlas_only_failure_execution :
    testState atlasProfile (token 0) = .failed ∧
      ∀ i : Node, i ≠ 0 → testState atlasProfile (token i) = .unformed := by
  have zero : testState atlasProfile (token 0) = .failed :=
    (test_failure atlasProfile 0 (by decide)).mpr (by decide)
  exact ⟨zero,atlas_failure_blocks_descendants _ _ _ _ (finite_run_solves _ _ _) zero⟩

def nativeProfile (b : Node → Bool) : LCTR.DifferentialNativeDomains.Input Unit where
  atlas _ := b 0 = true
  jet _ := b 1 = true
  member _ _ := b 2 = true
  value _ _ := b 3 = true
  time _ _ _ _ := b 4 = true
def nativeTruth (b : Node → Bool) : Node → Bool :=
  ![b 0,b 1,b 1 && b 2,b 0 && b 3,b 0 && b 4]

theorem profile_truth_is_native (b : Node → Bool) (i : Node) :
    nativeTruth b i = true ↔ condition (nativeProfile b) i := by
  fin_cases i <;>
    simp [nativeTruth,condition,nativeProfile,LCTR.DifferentialNativeDomains.c1,
      LCTR.DifferentialNativeDomains.c2,LCTR.DifferentialNativeDomains.c3,
      LCTR.DifferentialNativeDomains.c4,LCTR.DifferentialNativeDomains.c5]

theorem control_profiles_have_native_inputs :
    (∀ i, pairProfile i = true ↔ condition (nativeProfile pairProfile) i) ∧
    (∀ i, tripleProfile i = true ↔ condition (nativeProfile tripleProfile) i) ∧
    (∀ i, atlasProfile i = true ↔ condition (nativeProfile atlasProfile) i) := by
  have hp : nativeTruth pairProfile = pairProfile := by decide
  have ht : nativeTruth tripleProfile = tripleProfile := by decide
  have ha : nativeTruth atlasProfile = atlasProfile := by decide
  exact ⟨fun i => hp ▸ profile_truth_is_native pairProfile i,
    fun i => ht ▸ profile_truth_is_native tripleProfile i,
    fun i => ha ▸ profile_truth_is_native atlasProfile i⟩

end LCTR.CoreDifferentialExecution
