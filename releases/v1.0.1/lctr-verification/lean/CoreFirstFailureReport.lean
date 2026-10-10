import CoreFiniteAudit
import CoreContinuumBoundary
import Mathlib.Data.Finset.Card

namespace LCTR.CoreFirstFailureReport
set_option autoImplicit false
open Set LCTR.CoreTokenGraph LCTR.CoreEvaluation LCTR.CoreFiniteAudit
open LCTR.SelectedInputEvaluation LCTR.CoreContinuumBoundary
open scoped ENNReal
variable {L : Type} [LinearOrder L]

abbrev SixSignature := (i : Fin 6) → Fin (count i) → Bool
abbrev ApproxSignature := Fin 9 → Bool
def failedSet (s : Token → State) : Set Token := {t | s t = .failed}
def minimalSet (s : Token → State) : Set Token :=
  {t | t ∈ failedSet s ∧ ∀ u ∈ failedSet s, Relation.ReflTransGen Edge u t → u = t}
def signature (s : Token → State) : SixSignature := fun i j => decide (s ⟨i,j⟩ = .failed)
noncomputable def setSignature (S : Set Token) : SixSignature := by
  classical
  exact fun i j => decide ((⟨i,j⟩ : Token) ∈ S)

theorem minimal_positions_exact (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) : minimalSet s = failedSet s := by
  ext t
  exact ⟨fun h => h.1,fun h => ⟨h,fun u hu path => failed_minimal Edge f e c s rec hu h path⟩⟩

theorem signature_support_exact (s : Token → State) (i : Fin 6) (j : Fin (count i)) :
    signature s i j = true ↔ (⟨i,j⟩ : Token) ∈ failedSet s := by
  simp [signature,failedSet]

theorem minimal_signature_exact (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) : signature s = setSignature (minimalSet s) := by
  rw [minimal_positions_exact f e c s rec]
  funext i j
  exact decide_eq_decide.mpr Iff.rfl

theorem localization_nonempty (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) (hf : (failedSet s).Nonempty) : (minimalSet s).Nonempty := by
  rw [minimal_positions_exact f e c s rec]
  exact hf

def failedFinset (s : Token → State) : Finset Token := Finset.univ.filter (fun t => s t = .failed)
def structuralCase (s : Token → State) : FailureCase := failureCase (failedFinset s).card

theorem unique_structural_position (s : Token → State) (h : structuralCase s = .unique) :
    ∃ t : Token, failedSet s = {t} ∧ ∀ u : Token,
      signature s u.1 u.2 = true ↔ u = t := by
  have card : (failedFinset s).card = 1 := (case_exact _).2.1.mp h
  obtain ⟨t,ht⟩ := Finset.card_eq_one.mp card
  have hs : failedSet s = {t} := by
    ext u
    have equal := Finset.ext_iff.mp ht u
    simpa [failedFinset,failedSet] using equal
  refine ⟨t,hs,?_⟩
  intro u
  rw [signature_support_exact,hs]
  rfl

theorem parallel_structural_positions (s : Token → State) (h : structuralCase s = .parallel) :
    2 ≤ (failedFinset s).card := (case_exact _).2.2.mp h

def boundaryData (V : Set L) (b : L → ApproxSignature) : Set (L × ApproxSignature) :=
  {p | IsLeast Vᶜ p.1 ∧ p.2 = b p.1}

theorem boundary_singleton (V : Set L) (b : L → ApproxSignature) (l : L)
    (hl : IsLeast Vᶜ l) : boundaryData V b = {(l,b l)} := by
  ext p
  constructor
  · rintro ⟨hp,hs⟩
    have eq : p.1 = l := le_antisymm (hp.2 hl.1) (hl.2 hp.1)
    exact Prod.ext eq (hs.trans (congrArg b eq))
  · rintro rfl
    exact ⟨hl,rfl⟩

theorem boundary_empty_iff (V : Set L) (b : L → ApproxSignature) :
    boundaryData V b = ∅ ↔ ¬ ∃ l, IsLeast Vᶜ l := by
  constructor
  · intro he ⟨l,hl⟩
    have mem : (l,b l) ∈ boundaryData V b := ⟨hl,rfl⟩
    rw [he] at mem
    exact mem
  · intro hn
    apply Set.eq_empty_iff_forall_notMem.mpr
    exact fun p hp => hn ⟨p.1,hp.1⟩

theorem boundary_empty_or_singleton (V : Set L) (b : L → ApproxSignature) :
    boundaryData V b = ∅ ∨ ∃ l, boundaryData V b = {(l,b l)} := by
  classical
  by_cases h : ∃ l, IsLeast Vᶜ l
  · obtain ⟨l,hl⟩ := h
    exact Or.inr ⟨l,boundary_singleton V b l hl⟩
  · exact Or.inl ((boundary_empty_iff V b).mpr h)

theorem full_validity_has_no_boundary (b : L → ApproxSignature) :
    boundaryData Set.univ b = ∅ := by
  apply (boundary_empty_iff _ _).mpr
  rintro ⟨l,hl⟩
  exact hl.1 (Set.mem_univ l)

noncomputable def excessSignature (d eps : Fin 9 → ℝ≥0∞) : ApproxSignature := by
  classical
  exact fun i => decide (i ∈ Exceeded d eps)

theorem excess_signature_exact (d eps : Fin 9 → ℝ≥0∞) (i : Fin 9) :
    excessSignature d eps i = true ↔ eps i < d i := by
  classical
  simp [excessSignature,Exceeded,excess_positive]

theorem excess_signature_zero_iff (d eps : Fin 9 → ℝ≥0∞) :
    excessSignature d eps = (fun _ => false) ↔ Valid d eps := by
  classical
  constructor
  · intro h i
    have hi := congrFun h i
    simpa [excessSignature,Exceeded,excess_positive] using hi
  · intro h
    funext i
    simp [excessSignature,Exceeded,excess_positive,not_lt.mpr (h i)]

theorem quantitative_boundary_singleton (d : L → Fin 9 → ℝ≥0∞) (eps : Fin 9 → ℝ≥0∞)
    (l : L) (hl : IsLeast {x | ¬ Valid (d x) eps} l) :
    boundaryData {x | Valid (d x) eps} (fun x => excessSignature (d x) eps) =
      {(l,excessSignature (d l) eps)} ∧ excessSignature (d l) eps ≠ (fun _ => false) :=
  ⟨boundary_singleton _ _ l hl,fun h => hl.1 ((excess_signature_zero_iff _ _).mp h)⟩

abbrev Report (L : Type) := Set Token × SixSignature × Set (L × ApproxSignature)
def report (s : Token → State) (V : Set L) (b : L → ApproxSignature) : Report L :=
  (failedSet s,signature s,boundaryData V b)

theorem report_independent_of_solution (f e c : Token → Bool) (s t : Token → State)
    (hs : Recurs Edge f e c s) (ht : Recurs Edge f e c t) (V : Set L) (b : L → ApproxSignature) :
    report s V b = report t V b := by
  have eq : s = t := (finite_run_unique f e c s hs).trans (finite_run_unique f e c t ht).symm
  rw [eq]

theorem report_components (f e c : Token → Bool) (s : Token → State)
    (hs : Recurs Edge f e c s) (V : Set L) (b : L → ApproxSignature) :
    (report s V b).1 = minimalSet s ∧
    (report s V b).2.1 = setSignature (failedSet s) ∧
    ((report s V b).2.2 = ∅ ∨ ∃ l, (report s V b).2.2 = {(l,b l)}) := by
  refine ⟨(minimal_positions_exact f e c s hs).symm,?_,boundary_empty_or_singleton V b⟩
  funext i j
  exact decide_eq_decide.mpr Iff.rfl

theorem no_least_boundary_control (b : ℝ → ApproxSignature) :
    boundaryData {x : ℝ | x ≤ 0} b = ∅ := by
  apply (boundary_empty_iff _ _).mpr
  simpa only [Set.compl_ofPred,not_le] using no_least_open_excess_control

theorem boundary_presence_different_from_zero_signature :
    boundaryData {x : ℕ | x < 1} (fun _ _ => false) = {(1,fun _ => false)} := by
  apply boundary_singleton
  constructor
  · norm_num
  · intro x hx
    change ¬ x < 1 at hx
    omega

end LCTR.CoreFirstFailureReport
