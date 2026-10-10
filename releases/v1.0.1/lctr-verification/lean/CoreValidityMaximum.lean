import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Prod

namespace LCTR.CoreValidityMaximum
set_option autoImplicit false
universe u v
variable {E : Type u} {L : Type v}

def Greatest (F : Set (Set E)) (U : Set E) : Prop := U ∈ F ∧ ∀ V ∈ F, V ⊆ U

theorem greatest_equals_union (F : Set (Set E)) (U : Set E) (h : Greatest F U) :
    U = ⋃₀ F := by
  apply Set.Subset.antisymm
  · intro x hx; exact Set.mem_sUnion.mpr ⟨U,h.1,hx⟩
  · intro x hx
    obtain ⟨V,hV,hx⟩ := Set.mem_sUnion.mp hx
    exact h.2 V hV hx

theorem union_is_greatest (F : Set (Set E)) (member : ⋃₀ F ∈ F) : Greatest F (⋃₀ F) := by
  refine ⟨member,?_⟩
  intro V hV x hx
  exact Set.mem_sUnion.mpr ⟨V,hV,hx⟩

theorem maximum_exists_iff_union_member (F : Set (Set E)) :
    (∃ U, Greatest F U) ↔ ⋃₀ F ∈ F := by
  constructor
  · rintro ⟨U,h⟩
    rw [← greatest_equals_union F U h]
    exact h.1
  · intro h; exact ⟨⋃₀ F,union_is_greatest F h⟩

theorem maximum_unique (F : Set (Set E)) (U V : Set E)
    (hU : Greatest F U) (hV : Greatest F V) : U = V :=
  Set.Subset.antisymm (hV.2 U hU.1) (hU.2 V hV.1)

theorem maximum_validity_domain (V : Set E) (F : Set (Set E))
    (typed : ∀ U ∈ F, U ⊆ V) (member : ⋃₀ F ∈ F) :
    (∃! U, Greatest F U) ∧ ⋃₀ F ⊆ V := by
  exact ⟨⟨⋃₀ F,union_is_greatest F member,
    fun U hU => maximum_unique F U (⋃₀ F) hU (union_is_greatest F member)⟩,
    typed _ member⟩

theorem empty_family_no_maximum : ¬ ∃ U : Set E, Greatest ∅ U := by
  rintro ⟨_,h,_⟩
  exact h

theorem incomparable_family_no_maximum :
    ¬ ∃ U : Set Bool, Greatest {{false},{true}} U := by
  rintro ⟨U,hU,hgreat⟩
  have hf := hgreat {false} (by simp) (by simp : false ∈ ({false} : Set Bool))
  have ht := hgreat {true} (by simp) (by simp : true ∈ ({true} : Set Bool))
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hU
  rcases hU with rfl | rfl
  · simp at ht
  · simp at hf

def fullDomain (strict : Set E) (approximation : Set (E × L)) : Set (E × L) :=
  (strict ×ˢ Set.univ) ∩ approximation

theorem full_domain_membership (strict : Set E) (approximation : Set (E × L)) (e : E) (l : L) :
    (e,l) ∈ fullDomain strict approximation ↔ e ∈ strict ∧ (e,l) ∈ approximation := by
  simp [fullDomain]

end LCTR.CoreValidityMaximum
