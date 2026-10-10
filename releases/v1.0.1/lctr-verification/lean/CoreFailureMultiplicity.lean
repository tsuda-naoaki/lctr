import CoreFirstFailureReport

namespace LCTR.CoreFailureMultiplicity
set_option autoImplicit false
open Set LCTR.CoreFirstFailureReport LCTR.CoreTokenGraph LCTR.CoreEvaluation
open LCTR.SelectedInputEvaluation LCTR.CoreContinuumBoundary
open scoped ENNReal
variable {L : Type} [LinearOrder L]

noncomputable def support (V : Set L) (b : L → ApproxSignature) : Finset (Fin 9) := by
  classical
  exact Finset.univ.filter (fun i => ∃ l, IsLeast Vᶜ l ∧ b l i = true)

def signatureSupport (b : ApproxSignature) : Finset (Fin 9) :=
  Finset.univ.filter (fun i => b i = true)

theorem support_at_boundary (V : Set L) (b : L → ApproxSignature) (l : L)
    (hl : IsLeast Vᶜ l) : support V b = signatureSupport (b l) := by
  classical
  ext i
  simp only [support,signatureSupport,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨a,ha,h⟩
    have eq : a = l := le_antisymm (ha.2 hl.1) (hl.2 ha.1)
    simpa [eq] using h
  · exact fun h => ⟨l,hl,h⟩

theorem no_boundary_no_support (V : Set L) (b : L → ApproxSignature)
    (hn : ¬ ∃ l, IsLeast Vᶜ l) : support V b = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨l,hl,_⟩ := (Finset.mem_filter.mp hi).2
  exact hn ⟨l,hl⟩

theorem support_card_bound (V : Set L) (b : L → ApproxSignature) :
    (support V b).card ≤ 9 := by
  have h := Finset.card_le_card (Finset.subset_univ (support V b))
  simpa using h

inductive BoundaryCase where
  | absent | unique | parallel
  deriving DecidableEq

def classify (n : Nat) : BoundaryCase :=
  if n = 0 then .absent else if n = 1 then .unique else .parallel

theorem classification_exact (n : Nat) :
    (classify n = .absent ↔ n = 0) ∧
    (classify n = .unique ↔ n = 1) ∧
    (classify n = .parallel ↔ 2 ≤ n) := by
  unfold classify
  split_ifs <;> simp_all
  all_goals omega

noncomputable def boundaryCase (V : Set L) (b : L → ApproxSignature) : BoundaryCase :=
  classify (support V b).card

theorem absent_exact (V : Set L) (b : L → ApproxSignature) :
    boundaryCase V b = .absent ↔
      boundaryData V b ⊆ Set.univ ×ˢ {(fun _ : Fin 9 => false)} := by
  classical
  rw [boundaryCase,(classification_exact _).1,Finset.card_eq_zero]
  constructor
  · intro he p hp
    refine ⟨Set.mem_univ _,?_⟩
    change p.2 = (fun _ => false)
    rw [hp.2]
    funext i
    apply Bool.eq_false_iff.mpr
    intro hi
    have hm : i ∈ support V b := Finset.mem_filter.mpr ⟨Finset.mem_univ _,p.1,hp.1,hi⟩
    rw [he] at hm
    exact Finset.notMem_empty i hm
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨l,hl,hbi⟩ := (Finset.mem_filter.mp hi).2
    have hb : b l = (fun _ => false) := (h (show (l,b l) ∈ boundaryData V b from ⟨hl,rfl⟩)).2
    have := congrFun hb i
    simp_all

theorem unique_exact (V : Set L) (b : L → ApproxSignature) :
    boundaryCase V b = .unique ↔ (support V b).card = 1 :=
  (classification_exact _).2.1

theorem parallel_exact (V : Set L) (b : L → ApproxSignature) :
    boundaryCase V b = .parallel ↔ 2 ≤ (support V b).card :=
  (classification_exact _).2.2

theorem classified_nonzero_has_boundary (V : Set L) (b : L → ApproxSignature)
    (h : boundaryCase V b ≠ .absent) : ∃ l, IsLeast Vᶜ l := by
  classical
  by_contra hn
  apply h
  simp [boundaryCase,no_boundary_no_support V b hn,classify]

theorem parallel_boundary_card (V : Set L) (b : L → ApproxSignature)
    (h : boundaryCase V b = .parallel) :
    ∃ l, IsLeast Vᶜ l ∧ 2 ≤ (signatureSupport (b l)).card := by
  obtain ⟨l,hl⟩ := classified_nonzero_has_boundary V b (by simp [h])
  refine ⟨l,hl,?_⟩
  have hc := (parallel_exact V b).mp h
  rwa [support_at_boundary V b l hl] at hc

theorem quantitative_signature_support (d eps : Fin 9 → ℝ≥0∞) :
    (↑(signatureSupport (excessSignature d eps)) : Set (Fin 9)) = Exceeded d eps := by
  ext i
  simp [signatureSupport,excess_signature_exact,Exceeded,excess_positive]

theorem quantitative_parallel_at_boundary (d : L → Fin 9 → ℝ≥0∞)
    (eps : Fin 9 → ℝ≥0∞) (l : L) (hl : IsLeast {x | ¬ Valid (d x) eps} l)
    (h : boundaryCase {x | Valid (d x) eps} (fun x => excessSignature (d x) eps) = .parallel) :
    2 ≤ (signatureSupport (excessSignature (d l) eps)).card := by
  have hc := (parallel_exact _ _).mp h
  rwa [support_at_boundary {x | Valid (d x) eps} (fun x => excessSignature (d x) eps) l hl] at hc

noncomputable def multiplicityReport (s : Token → State) (V : Set L) (b : L → ApproxSignature) :
    FailureCase × BoundaryCase := (structuralCase s,boundaryCase V b)

theorem multiplicity_components (s : Token → State) (V : Set L) (b : L → ApproxSignature) :
    (multiplicityReport s V b).1 = failureCase (failedFinset s).card ∧
    (multiplicityReport s V b).2 = classify (support V b).card := ⟨rfl,rfl⟩

theorem multiplicity_depends_on_two_cardinalities (s t : Token → State)
    (V W : Set L) (b c : L → ApproxSignature)
    (hs : (failedFinset s).card = (failedFinset t).card)
    (hb : (support V b).card = (support W c).card) :
    multiplicityReport s V b = multiplicityReport t W c := by
  simp only [multiplicityReport,structuralCase,boundaryCase,hs,hb]

theorem parallel_structural_card (s : Token → State) (V : Set L) (b : L → ApproxSignature)
    (h : (multiplicityReport s V b).1 = .parallel) : 2 ≤ (failedFinset s).card :=
  parallel_structural_positions s h

theorem present_zero_boundary_is_absent :
    boundaryData {x : ℕ | x < 1} (fun _ _ => false) ≠ ∅ ∧
    boundaryCase {x : ℕ | x < 1} (fun _ _ => false) = .absent := by
  constructor
  · rw [boundary_presence_different_from_zero_signature]
    simp
  · apply (absent_exact _ _).mpr
    rintro p ⟨_,hp⟩
    exact ⟨Set.mem_univ _,hp⟩

end LCTR.CoreFailureMultiplicity
