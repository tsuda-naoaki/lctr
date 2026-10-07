import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Set.Function

namespace LCTR.CoreLeastScaleLift
set_option autoImplicit false
open Set
universe u v
variable {X : Type u} {L : Type v} [PartialOrder L]

def domain (S : X → Set L) : Set X := {x | ∃ l, IsLeast (S x) l}
noncomputable def value (S : X → Set L) (x : ↥(domain S)) : L := Classical.choose x.property
def graph (S : X → Set L) : Set (X × L) := {p | IsLeast (S p.1) p.2}

theorem domain_exact (S : X → Set L) (x : X) :
    x ∈ domain S ↔ ∃ l ∈ S x, ∀ m ∈ S x, l ≤ m := Iff.rfl
theorem value_is_least (S : X → Set L) (x : ↥(domain S)) : IsLeast (S x.val) (value S x) :=
  Classical.choose_spec x.property
theorem value_unique (S : X → Set L) (x : ↥(domain S)) (l : L) (h : IsLeast (S x.val) l) :
    value S x = l :=
  le_antisymm ((value_is_least S x).2 h.1) (h.2 (value_is_least S x).1)
theorem graph_exact (S : X → Set L) (x : X) (l : L) :
    (x,l) ∈ graph S ↔ ∃ h : x ∈ domain S, value S ⟨x,h⟩ = l := by
  constructor
  · intro h; exact ⟨⟨l,h⟩,value_unique S ⟨x,⟨l,h⟩⟩ l h⟩
  · rintro ⟨h,rfl⟩; exact value_is_least S ⟨x,h⟩
theorem graph_singlevalued (S : X → Set L) (x : X) (l m : L)
    (hl : (x,l) ∈ graph S) (hm : (x,m) ∈ graph S) : l = m :=
  le_antisymm (hl.2 hm.1) (hm.2 hl.1)
theorem empty_fibre_undefined (S : X → Set L) (x : X) (h : S x = ∅) : x ∉ domain S := by
  rintro ⟨l,hl⟩
  have mem := hl.1
  rw [h] at mem
  exact mem
theorem same_sets_domain (S T : X → Set L) (x : X) (h : S x = T x) :
    x ∈ domain S ↔ x ∈ domain T := by unfold domain; simp only [mem_ofPred_eq,h]
theorem same_sets_value (S T : X → Set L) (x : X) (h : S x = T x)
    (hs : x ∈ domain S) (ht : x ∈ domain T) : value S ⟨x,hs⟩ = value T ⟨x,ht⟩ := by
  apply value_unique
  rw [h]
  exact value_is_least T ⟨x,ht⟩

end LCTR.CoreLeastScaleLift
