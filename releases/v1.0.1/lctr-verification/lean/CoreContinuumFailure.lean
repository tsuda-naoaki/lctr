import CoreFiniteAudit
import CoreContinuumEncoding

namespace LCTR.CoreContinuumFailure
set_option autoImplicit false
open LCTR.CoreTokenGraph LCTR.CoreEvaluation LCTR.CoreFiniteAudit
open LCTR.SelectedInputEvaluation LCTR.CoreContinuumIntegration
open LCTR.CoreContinuumBoundary LCTR.CoreContinuumEncoding
open scoped ENNReal

 
def First (i : Fin 6) : Fin 9 := ⟨i.val, by omega⟩
def Pred (s : Token → State) (i : Fin 9) : Prop :=
  ∀ y : Token, Edge y (approxToken i) → s y = .sat
def Ready (f e : Token → Bool) (s : Token → State) (i : Fin 9) : Prop :=
  f (approxToken i) = true ∧ e (approxToken i) = true ∧ Pred s i
def FA (s : Token → State) (i : Fin 9) : Prop := s (approxToken i) = .failed
def Failed (s : Token → State) : Set Token := {t | series t = 3 ∧ s t = .failed}

theorem incoming_exact : ∀ i : Fin 9, ∀ y : Token,
    Edge y (approxToken i) ↔ series y = 2 ∨
      (series y = 3 ∧ ((y.2.val < 6 ∧ i.val = 6) ∨
        (y.2.val = 6 ∧ (i.val = 7 ∨ i.val = 8)))) := by decide

theorem first_incoming_exact : ∀ i : Fin 6, ∀ y : Token,
    Edge y (approxToken (First i)) ↔ series y = 2 := by decide

theorem seventh_incoming_exact : ∀ y : Token,
    Edge y (approxToken 6) ↔ series y = 2 ∨
      ∃ i : Fin 6, y = approxToken (First i) := by decide

theorem final_incoming_exact : ∀ i : Fin 9, 7 ≤ i.val → ∀ y : Token,
    Edge y (approxToken i) ↔ series y = 2 ∨ y = approxToken 6 := by decide

theorem first_incomparable (i j : Fin 6) (ne : i ≠ j) :
    ¬ Relation.ReflTransGen Edge (approxToken (First i)) (approxToken (First j)) ∧
    ¬ Relation.ReflTransGen Edge (approxToken (First j)) (approxToken (First i)) := by
  have hi : i.val ≠ j.val := fun h => ne (Fin.ext h)
  rcases lt_or_gt_of_ne hi with h | h
  · apply parallel_branches
    simp only [designated,approxToken,First,series,index]
    omega
  · have p : designated (approxToken (First j)) (approxToken (First i)) := by
      simp only [designated,approxToken,First,series,index]
      omega
    exact (parallel_branches p).symm

theorem final_incomparable :
    ¬ Relation.ReflTransGen Edge (approxToken 7) (approxToken 8) ∧
    ¬ Relation.ReflTransGen Edge (approxToken 8) (approxToken 7) :=
  parallel_branches (by decide)

theorem recursive_failure (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) (i : Fin 9) :
    FA s i ↔ Ready f e s i ∧ c (approxToken i) = false := by
  unfold FA Ready Pred
  rw [rec (approxToken i),update_failed_iff]
  rw [← predecessor_iff]
  tauto

theorem ready_failure_iff (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) (i : Fin 9) (r : Ready f e s i) :
    FA s i ↔ c (approxToken i) = false := by
  rw [recursive_failure f e c s rec i]
  exact and_iff_right r

theorem ready_sat_iff (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) (i : Fin 9) (r : Ready f e s i) :
    s (approxToken i) = .sat ↔ c (approxToken i) = true := by
  classical
  rw [rec (approxToken i)]
  simp only [update,state_sat_iff,decide_eq_true_eq]
  rw [← predecessor_iff]
  exact ⟨fun h => h.2.2.2,fun h => ⟨r.1,r.2.1,r.2.2,h⟩⟩

theorem first_ready (f e : Token → Bool) (s : Token → State)
    (inp : InputSat f e s) (i : Fin 6) : Ready f e s (First i) := by
  refine ⟨(inp.2 _ rfl).1,(inp.2 _ rfl).2,?_⟩
  intro y hy
  exact inp.1 y ((first_incoming_exact i y).mp hy)

theorem seventh_pred (s : Token → State) (dyn : ∀ t, series t = 2 → s t = .sat) :
    Pred s 6 ↔ ∀ i : Fin 6, s (approxToken (First i)) = .sat := by
  constructor
  · intro h i
    exact h _ ((seventh_incoming_exact _).mpr (Or.inr ⟨i,rfl⟩))
  · intro h y hy
    rcases (seventh_incoming_exact y).mp hy with hd | ⟨i,rfl⟩
    · exact dyn y hd
    · exact h i

theorem final_pred (s : Token → State) (dyn : ∀ t, series t = 2 → s t = .sat)
    (i : Fin 9) (hi : 7 ≤ i.val) : Pred s i ↔ s (approxToken 6) = .sat := by
  constructor
  · intro h
    exact h _ ((final_incoming_exact i hi _).mpr (Or.inr rfl))
  · intro h y hy
    rcases (final_incoming_exact i hi y).mp hy with hd | rfl
    · exact dyn y hd
    · exact h

theorem ninth_not_dependent_on_eighth : ¬ Edge (approxToken 7) (approxToken 8) := by decide

theorem quantitative_failure (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) (d eps : Fin 9 → ℝ≥0∞)
    (encoding : ∀ i, c (approxToken i) = true ↔ d i ≤ eps i)
    (i : Fin 9) (r : Ready f e s i) :
    (FA s i ↔ eps i < d i) ∧ (FA s i ↔ i ∈ Exceeded d eps) := by
  have q : FA s i ↔ eps i < d i := by
    rw [ready_failure_iff f e c s rec i r, ← Bool.not_eq_true, encoding i, not_le]
  exact ⟨q,q.trans (excess_positive _ _).symm⟩

theorem source_nine_witnesses (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) (d eps : Fin 9 → ℝ≥0∞) (b : Fin 9 → Bool)
    (matching : ∀ i, c (approxToken i) = paperCondition d eps b i)
    (i : Fin 9) (r : Ready f e s i) :
    (FA s i ↔ paperTolerance eps i < paperDefect d b i) ∧
    (FA s i ↔ i ∈ Exceeded (paperDefect d b) (paperTolerance eps)) := by
  apply quantitative_failure f e c s rec _ _ _ i r
  intro j
  rw [matching j]
  exact nine_component_encoding d eps b j

theorem source_first_witness (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) (d eps : Fin 9 → ℝ≥0∞) (b : Fin 9 → Bool)
    (matching : ∀ i, c (approxToken i) = paperCondition d eps b i)
    (i : Fin 6) (r : Ready f e s (First i)) :
    FA s (First i) ↔ eps (First i) < d (First i) := by
  have h := (source_nine_witnesses f e c s rec d eps b matching (First i) r).1
  have preserved := first_six_preserved d eps b (First i) i.isLt
  rw [preserved.1,preserved.2] at h
  exact h

theorem failed_set_exact (s : Token → State) : Failed s = approxToken '' {i | FA s i} := by
  ext t
  constructor
  · intro h
    obtain ⟨i,hi⟩ := approx_index_bijection.2 ⟨t,h.1⟩
    have he : approxToken i = t := congrArg Subtype.val hi
    refine ⟨i,?_,he⟩
    change s (approxToken i) = .failed
    rw [he]
    exact h.2
  · rintro ⟨i,h,rfl⟩
    exact ⟨rfl,h⟩

theorem failure_disjunction (s : Token → State) : (Failed s).Nonempty ↔ ∃ i, FA s i := by
  rw [failed_set_exact]
  rw [Set.image_nonempty]
  rfl

noncomputable def firstFailures (s : Token → State) : Finset Token := by
  classical
  exact (Finset.univ.filter (fun i : Fin 6 => FA s (First i))).image (fun i => approxToken (First i))

theorem first_failures_card (s : Token → State) (i j : Fin 6) (ne : i ≠ j)
    (hi : FA s (First i)) (hj : FA s (First j)) : 2 ≤ (firstFailures s).card := by
  classical
  have hin : approxToken (First i) ∈ firstFailures s := by
    simp only [firstFailures,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨i,hi,rfl⟩
  have hjn : approxToken (First j) ∈ firstFailures s := by
    simp only [firstFailures,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨j,hj,rfl⟩
  have neq : approxToken (First i) ≠ approxToken (First j) := by
    intro h
    apply ne
    exact Fin.ext (congrArg (fun t : Token => t.2.val) h)
  have sub : {approxToken (First i),approxToken (First j)} ⊆ firstFailures s := by
    intro t ht
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl <;> assumption
  simpa only [Finset.card_pair neq] using Finset.card_le_card sub

theorem quantitative_first_pair (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) (d eps : Fin 9 → ℝ≥0∞) (b : Fin 9 → Bool)
    (matching : ∀ i, c (approxToken i) = paperCondition d eps b i)
    (i j : Fin 6) (ne : i ≠ j) (ri : Ready f e s (First i)) (rj : Ready f e s (First j))
    (hi : eps (First i) < d (First i)) (hj : eps (First j) < d (First j)) :
    2 ≤ (firstFailures s).card :=
  first_failures_card s i j ne
    ((source_first_witness f e c s rec d eps b matching i ri).mpr hi)
    ((source_first_witness f e c s rec d eps b matching j rj).mpr hj)

theorem final_pair (s : Token → State) (h8 : FA s 7) (h9 : FA s 8) :
    approxToken 7 ∈ Failed s ∧ approxToken 8 ∈ Failed s := ⟨⟨rfl,h8⟩,⟨rfl,h9⟩⟩

theorem all_failures_minimal (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) (x : Token) (hx : x ∈ Failed s) :
    ∀ y ∈ Failed s, Relation.ReflTransGen Edge y x → y = x := by
  intro y hy path
  exact failed_minimal Edge f e c s rec hy.2 hx.2 path

theorem first_failure_blocks_extension (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) (i : Fin 6) (h : FA s (First i)) :
    s (approxToken 6) = .unformed := by
  apply direct_nonsat_unformed Edge f e c s rec
    ((seventh_incoming_exact _).mpr (Or.inr ⟨i,rfl⟩))
  rw [h]
  decide

theorem extension_failure_blocks_final (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) (h : FA s 6) :
    s (approxToken 7) = .unformed ∧ s (approxToken 8) = .unformed := by
  have no : s (approxToken 6) ≠ .sat := by rw [h]; decide
  exact ⟨direct_nonsat_unformed Edge f e c s rec (by decide) no,
    direct_nonsat_unformed Edge f e c s rec (by decide) no⟩

 
 
def testCondition (b : Fin 9 → Bool) (t : Token) : Bool :=
  if h : t.1 = (3 : Fin 6) then
    b ⟨t.2.val, by simpa [h,count] using t.2.isLt⟩ else true
def testState (b : Fin 9 → Bool) : Token → State :=
  run (fun _ => true) (fun _ => true) (testCondition b) 40

theorem test_input_sat (b : Fin 9 → Bool) :
    InputSat (fun _ => true) (fun _ => true) (testState b) := by
  have outside : ∀ x y : Token, series x ≠ 3 → Edge y x → series y ≠ 3 := by decide
  have allOther : ∀ t, series t ≠ 3 → testState b t = .sat := by
    apply (all_sat_iff_tests Edge (LCTR.CoreDagRecursion.finite_acyclic_wellFounded Edge acyclic)
      (fun _ => true) (fun _ => true) (testCondition b) (testState b)
      (finite_run_solves _ _ _) {t | series t ≠ 3}
      (fun _ _ => ⟨rfl,rfl⟩) ?_).mpr
    · intro t ht
      have ne : t.1 ≠ (3 : Fin 6) := fun h => ht (congrArg Fin.val h)
      simp [testCondition,ne]
    · intro x hx y hy hn
      exact False.elim (hn (outside x y hx hy))
  exact ⟨fun t ht => allOther t (by omega),fun _ _ => ⟨rfl,rfl⟩⟩

theorem test_first_sat (b : Fin 9 → Bool) (i : Fin 6) :
    testState b (approxToken (First i)) = .sat ↔ b (First i) = true := by
  simpa [testCondition,approxToken,testState] using
    ready_sat_iff _ _ _ _ (finite_run_solves _ _ _) (First i)
      (first_ready _ _ _ (test_input_sat b) i)

theorem test_first_failure (b : Fin 9 → Bool) (i : Fin 6) :
    FA (testState b) (First i) ↔ b (First i) = false := by
  simpa [testCondition,approxToken,testState] using
    ready_failure_iff _ _ _ _ (finite_run_solves _ _ _) (First i)
      (first_ready _ _ _ (test_input_sat b) i)

theorem test_extension_sat (b : Fin 9 → Bool) (h : ∀ i : Fin 6, b (First i) = true) :
    testState b (approxToken 6) = .sat ↔ b 6 = true := by
  have r : Ready (fun _ => true) (fun _ => true) (testState b) 6 := by
    refine ⟨rfl,rfl,(seventh_pred _ (test_input_sat b).1).mpr ?_⟩
    intro i
    exact (test_first_sat b i).mpr (h i)
  simpa [testCondition,approxToken,testState] using
    ready_sat_iff _ _ _ _ (finite_run_solves _ _ _) 6 r

theorem test_final_failure (b : Fin 9 → Bool) (h : ∀ i : Fin 6, b (First i) = true)
    (h7 : b 6 = true) (i : Fin 9) (hi : 7 ≤ i.val) :
    FA (testState b) i ↔ b i = false := by
  have r : Ready (fun _ => true) (fun _ => true) (testState b) i :=
    ⟨rfl,rfl,(final_pred _ (test_input_sat b).1 i hi).mpr
      ((test_extension_sat b h).mpr h7)⟩
  simpa [testCondition,approxToken,testState] using
    ready_failure_iff _ _ _ _ (finite_run_solves _ _ _) i r

def firstPairTest (i : Fin 9) : Bool := decide (i.val ≠ 0 ∧ i.val ≠ 1)
def finalPairTest (i : Fin 9) : Bool := decide (i.val < 7)

theorem first_pair_execution :
    FA (testState firstPairTest) 0 ∧ FA (testState firstPairTest) 1 ∧
    2 ≤ (firstFailures (testState firstPairTest)).card ∧
    testState firstPairTest (approxToken 6) = .unformed := by
  have h0 := (test_first_failure firstPairTest 0).mpr (by decide)
  have h1 := (test_first_failure firstPairTest 1).mpr (by decide)
  exact ⟨h0,h1,first_failures_card _ 0 1 (by decide) h0 h1,
    first_failure_blocks_extension _ _ _ _ (finite_run_solves _ _ _) 0 h0⟩

theorem final_pair_execution :
    FA (testState finalPairTest) 7 ∧ FA (testState finalPairTest) 8 ∧
    testState finalPairTest (approxToken 6) = .sat := by
  have first : ∀ i : Fin 6, finalPairTest (First i) = true := by decide
  exact ⟨(test_final_failure finalPairTest first (by decide) 7 (by decide)).mpr (by decide),
    (test_final_failure finalPairTest first (by decide) 8 (by decide)).mpr (by decide),
    (test_extension_sat finalPairTest first).mpr (by decide)⟩

end LCTR.CoreContinuumFailure
