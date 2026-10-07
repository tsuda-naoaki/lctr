import Mathlib.Data.Set.Lattice
import Mathlib.Order.Minimal

namespace LCTR.CoreRawLocalizationInterfaces
set_option autoImplicit false
open Set
universe u v w z

def validity {A : Type u} (p : A → Bool) : Set A := {a | p a = true}
def sectionAt {A : Type u} {B : Type v} (q : B → A → Bool) (b : B) : Set A :=
  validity (q b)
def family {A : Type u} {I : Type v} (j : Set I) (k : I → A → Bool) : Set A :=
  {a | ∀ i ∈ j, k i a = true}

theorem valid_membership {A : Type u} (p : A → Bool) (a : A) :
    a ∈ validity p ↔ p a = true := Iff.rfl
theorem section_membership {A : Type u} {B : Type v} (q : B → A → Bool) (b : B) (a : A) :
    a ∈ sectionAt q b ↔ q b a = true := Iff.rfl
theorem family_intersection {A : Type u} {I : Type v} (j : Set I) (k : I → A → Bool) :
    family j k = ⋂ i ∈ j, validity (k i) := by ext a; simp [family, validity]
theorem empty_family {A : Type u} {I : Type v} (k : I → A → Bool) :
    family ∅ k = univ := by ext a; simp [family]

def approximation {E : Type u} {L : Type v} (k : E × L → Bool) (e : E) : Set L :=
  {l | k (e,l) = true}
theorem approximation_membership {E : Type u} {L : Type v} (k : E × L → Bool) (e : E) (l : L) :
    l ∈ approximation k e ↔ k (e,l) = true := Iff.rfl
theorem approximation_downward {E : Type u} {L : Type v} [LinearOrder L]
    (k : E × L → Bool) (e : E)
    (mono : ∀ l m, l ≤ m → k (e,m) = true → k (e,l) = true) :
    ∀ l m, m ∈ approximation k e → l ≤ m → l ∈ approximation k e := by
  intro l m hm hl
  exact mono l m hl hm

inductive EvaluationState where
  | sat | failed | unformed | unevaluable
  deriving DecidableEq

theorem state_exhaustive (s : EvaluationState) :
    s = .sat ∨ s = .failed ∨ s = .unformed ∨ s = .unevaluable := by cases s <;> simp
theorem state_distinct :
    EvaluationState.sat ≠ .failed ∧ EvaluationState.sat ≠ .unformed ∧
    EvaluationState.sat ≠ .unevaluable ∧ EvaluationState.failed ≠ .unformed ∧
    EvaluationState.failed ≠ .unevaluable ∧ EvaluationState.unformed ≠ .unevaluable := by decide

abbrev EvaluationInput {T : Type u} (s a : Set T) (E : Type v) (L : Type w) :=
  (s × E) ⊕ (a × (E × L))
def strictFailed {T : Type u} {E : Type v} {L : Type w} {s a : Set T}
    (q : EvaluationInput s a E L → EvaluationState) (e : E) : Set T :=
  {t | ∃ h : t ∈ s, q (.inl (⟨t,h⟩,e)) = .failed}
def approxFailed {T : Type u} {E : Type v} {L : Type w} {s a : Set T}
    (q : EvaluationInput s a E L → EvaluationState) (e : E) (l : L) : Set T :=
  {t | ∃ h : t ∈ a, q (.inr (⟨t,h⟩,(e,l))) = .failed}

def minima {T : Type u} [PartialOrder T] (p : Set T) : Set T :=
  {t | t ∈ p ∧ ∀ u ∈ p, u ≤ t → u = t}
def strictLocalization {T : Type u} [PartialOrder T] {E : Type v} {L : Type w} {s a : Set T}
    (q : EvaluationInput s a E L → EvaluationState) (e : E) : Set T := minima (strictFailed q e)
def approxLocalization {T : Type u} [PartialOrder T] {E : Type v} {L : Type w} {s a : Set T}
    (q : EvaluationInput s a E L → EvaluationState) (e : E) (l : L) : Set T := minima (approxFailed q e l)

theorem strict_failed_membership {T : Type u} {E : Type v} {L : Type w} {s a : Set T}
    (q : EvaluationInput s a E L → EvaluationState) (e : E) (t : T) (ht : t ∈ s) :
    t ∈ strictFailed q e ↔ q (.inl (⟨t,ht⟩,e)) = .failed := by
  exact ⟨fun ⟨_,h⟩ => h, fun h => ⟨ht,h⟩⟩
theorem approx_failed_membership {T : Type u} {E : Type v} {L : Type w} {s a : Set T}
    (q : EvaluationInput s a E L → EvaluationState) (e : E) (l : L) (t : T) (ht : t ∈ a) :
    t ∈ approxFailed q e l ↔ q (.inr (⟨t,ht⟩,(e,l))) = .failed := by
  exact ⟨fun ⟨_,h⟩ => h, fun h => ⟨ht,h⟩⟩
theorem strict_localization {T : Type u} [PartialOrder T] {E : Type v} {L : Type w} {s a : Set T}
    (q : EvaluationInput s a E L → EvaluationState) (e : E) (t : T) :
    t ∈ strictLocalization q e ↔
    t ∈ strictFailed q e ∧ ∀ u ∈ strictFailed q e, u ≤ t → u = t := Iff.rfl
theorem approx_localization {T : Type u} [PartialOrder T] {E : Type v} {L : Type w} {s a : Set T}
    (q : EvaluationInput s a E L → EvaluationState) (e : E) (l : L) (t : T) :
    t ∈ approxLocalization q e l ↔
    t ∈ approxFailed q e l ∧ ∀ u ∈ approxFailed q e l, u ≤ t → u = t := Iff.rfl
theorem localization_subset {T : Type u} [PartialOrder T] (p : Set T) : minima p ⊆ p := fun _ h => h.1
theorem localization_antichain {T : Type u} [PartialOrder T] (p : Set T) (x y : T)
    (hx : x ∈ minima p) (hy : y ∈ minima p) (hxy : x ≤ y) : x = y := hy.2 x hx.1 hxy

def nontrans {Y : Type u} (r : Y → Y → Prop) : Prop :=
  ∃ x y z, r x y ∧ r y z ∧ ¬ r x z
theorem nontrans_exact {Y : Type u} (r : Y → Y → Prop) :
    nontrans r ↔ ∃ x y z, r x y ∧ r y z ∧ ¬ r x z := Iff.rfl
theorem nontrans_iff_not_transitive {Y : Type u} (r : Y → Y → Prop) :
    nontrans r ↔ ¬ (∀ x y z, r x y → r y z → r x z) := by
  classical
  constructor
  · rintro ⟨x,y,z,hxy,hyz,hxz⟩ h
    exact hxz (h x y z hxy hyz)
  · intro h
    obtain ⟨x,hx⟩ := not_forall.mp h
    obtain ⟨y,hy⟩ := not_forall.mp hx
    obtain ⟨z,hz⟩ := not_forall.mp hy
    have a := Classical.not_imp.mp hz
    have b := Classical.not_imp.mp a.2
    exact ⟨x,y,z,a.1,b.1,b.2⟩

def split {A : Type u} {I : Type v} (parent : Set A) (children : I → Set A) : Set A × Set A :=
  (⋃ i, children i, parent \ ⋃ i, children i)
theorem split_components {A : Type u} {I : Type v} (p : Set A) (c : I → Set A) :
    (split p c).1 = ⋃ i, c i ∧ (split p c).2 = p \ ⋃ i, c i := ⟨rfl,rfl⟩
theorem split_empty {A : Type u} (p : Set A) (c : Empty → Set A) :
    split p c = (∅,p) := by simp [split]
theorem split_decomposition {A : Type u} {I : Type v} (p : Set A) (c : I → Set A)
    (within : ∀ i, c i ⊆ p) :
    p = (split p c).1 ∪ (split p c).2 ∧ Disjoint (split p c).1 (split p c).2 := by
  have sub : (⋃ i, c i) ⊆ p := iUnion_subset within
  constructor
  · ext x
    change x ∈ p ↔ x ∈ (⋃ i, c i) ∨ x ∈ p ∧ x ∉ (⋃ i, c i)
    constructor
    · intro hx; by_cases h : x ∈ (⋃ i, c i)
      · exact Or.inl h
      · exact Or.inr ⟨hx,h⟩
    · rintro (h | h)
      · exact sub h
      · exact h.1
  · exact disjoint_left.mpr (fun _ h k => k.2 h)

end LCTR.CoreRawLocalizationInterfaces
