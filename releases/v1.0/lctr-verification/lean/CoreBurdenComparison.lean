import Mathlib.Data.Set.SymmDiff

namespace LCTR.CoreBurdenComparison
set_option autoImplicit false
universe u v
variable {A : Type u} {S : Type v}

def burden (R : A → A → Prop) (m : A → S) (F : Set A) : Set S :=
  {s | ∃ a ∈ F, ∃ b, R a b ∧ m b = s}

theorem equality_iff_empty_symmetric_difference
    (R : A → A → Prop) (m : A → S) (F G : Set A) :
    burden R m F = burden R m G ↔
      symmDiff (burden R m F) (burden R m G) = ∅ :=
  Set.symmDiff_eq_empty.symm

theorem one_sided_separation
    (R : A → A → Prop) (m : A → S) (F G : Set A) (a : A)
    (ha : a ∈ F) (hn : ¬ burden R m {a} ⊆ burden R m G) :
    (burden R m F \ burden R m G).Nonempty := by
  obtain ⟨s, hs, hns⟩ := Set.not_subset.mp hn
  obtain ⟨b, hb, c, hbc, hcs⟩ := hs
  have hba : b = a := Set.mem_singleton_iff.mp hb
  subst b
  exact ⟨s, ⟨a, ha, c, hbc, hcs⟩, hns⟩

theorem two_sided_incomparability
    (R : A → A → Prop) (m : A → S) (F G : Set A)
    (hf : ∃ a ∈ F, ¬ burden R m {a} ⊆ burden R m G)
    (hg : ∃ a ∈ G, ¬ burden R m {a} ⊆ burden R m F) :
    ¬ burden R m F ⊆ burden R m G ∧ ¬ burden R m G ⊆ burden R m F := by
  obtain ⟨a, ha, hna⟩ := hf
  obtain ⟨b, hb, hnb⟩ := hg
  obtain ⟨s, hs, hns⟩ := one_sided_separation R m F G a ha hna
  obtain ⟨t, ht, hnt⟩ := one_sided_separation R m G F b hb hnb
  exact ⟨fun h => hns (h hs), fun h => hnt (h ht)⟩

end LCTR.CoreBurdenComparison
