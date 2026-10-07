import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic

namespace LCTR.CoreFiniteReportComponents
set_option autoImplicit false
universe u v w z

variable {A : Type u} {Q : Type v} {S : Type w} {Y : Type z}
variable [Fintype A] [DecidableEq A] [DecidableEq Q] [DecidableEq S]

def fiber (s : A → Q) (q : Q) : Finset A :=
  Finset.univ.filter (fun a => s a = q)

def reasons (s : A → Q) (undefined : Q → Bool) : Finset (A × Q) :=
  (Finset.univ.filter (fun a => undefined (s a))).image (fun a => (a, s a))

def localReasons (s : A → Q) (undefined : Q → Bool) (G : Finset A) :
    Finset (A × Q) := (reasons s undefined).filter (fun p => p.1 ∈ G)

def burden (single : A → Finset S) (F : Finset A) : Finset S := F.biUnion single

def tagged {X : Type u} [DecidableEq X] (y : Y) (R : Finset X) : Y ⊕ Finset X :=
  if R = ∅ then .inl y else .inr R

noncomputable def setTagged {X : Type u} (y : Y) (R : Set X) : Y ⊕ Set X := by
  classical
  exact if R = ∅ then .inl y else .inr R

omit [DecidableEq A] in
theorem fiber_exact (s : A → Q) (q : Q) :
    (↑(fiber s q) : Set A) = {a | s a = q} := by
  ext a
  simp [fiber]

theorem reasons_exact (s : A → Q) (undefined : Q → Bool) :
    (↑(reasons s undefined) : Set (A × Q)) =
      {p | s p.1 = p.2 ∧ undefined p.2 = true} := by
  ext p
  rcases p with ⟨a, q⟩
  simp only [reasons, Finset.mem_coe, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Prod.mk.injEq, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨b, hb, rfl, rfl⟩
    exact ⟨rfl, hb⟩
  · rintro ⟨rfl, h⟩
    exact ⟨a, h, rfl, rfl⟩

theorem local_reasons_exact (s : A → Q) (undefined : Q → Bool) (G : Finset A) :
    (↑(localReasons s undefined G) : Set (A × Q)) =
      {p | p.1 ∈ G ∧ s p.1 = p.2 ∧ undefined p.2 = true} := by
  ext p
  have h := Set.ext_iff.mp (reasons_exact s undefined) p
  simp only [Finset.mem_coe, Set.mem_ofPred_eq] at h
  simp only [localReasons, Finset.mem_coe, Finset.mem_filter, h, Set.mem_ofPred_eq]
  tauto

omit [Fintype A] [DecidableEq A] in
theorem burden_exact (single : A → Finset S) (F : Finset A) :
    (↑(burden single F) : Set S) = {x | ∃ a ∈ F, x ∈ single a} := by
  ext x
  simp [burden]

omit [Fintype A] [DecidableEq A] in
theorem burden_from_singleton_images (single : A → Finset S) (F : Finset A)
    (R : A → A → Prop) (m : A → S)
    (hs : ∀ a, (↑(single a) : Set S) = m '' {b | R a b}) :
    (↑(burden single F) : Set S) = {x | ∃ a ∈ F, ∃ b, R a b ∧ m b = x} := by
  rw [burden_exact]
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, ha, hx⟩
    have hx' : x ∈ (↑(single a) : Set S) := hx
    rw [hs a] at hx'
    obtain ⟨b, hb, hbx⟩ := hx'
    exact ⟨a, ha, b, hb, hbx⟩
  · rintro ⟨a, ha, b, hb, hbx⟩
    refine ⟨a, ha, ?_⟩
    change x ∈ (↑(single a) : Set S)
    rw [hs a]
    exact ⟨b, hb, hbx⟩

theorem tagged_exact {X : Type u} [DecidableEq X] (y : Y) (R : Finset X) :
    Sum.map id (fun F : Finset X => (↑F : Set X)) (tagged y R) =
      setTagged y (↑R : Set X) := by
  classical
  by_cases h : R = ∅
  · subst R
    simp [tagged, setTagged]
  · have hn : (↑R : Set X) ≠ ∅ := by simpa using h
    simp [tagged, setTagged, h, hn]

theorem tagged_has_nonempty_reason {X : Type u} [DecidableEq X]
    (y : Y) (R T : Finset X) (h : tagged y R = .inr T) : T.Nonempty := by
  by_cases he : R = ∅
  · simp [tagged, he] at h
  · have ht : R = T := by simpa [tagged, he] using h
    exact ht ▸ Finset.nonempty_iff_ne_empty.mpr he

end LCTR.CoreFiniteReportComponents
