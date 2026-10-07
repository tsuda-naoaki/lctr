import Mathlib.Data.Set.Card

namespace LCTR.CoreFiniteClassWitness
set_option autoImplicit false
universe u
variable {E : Type u}

theorem finite_witness_set (n : ℕ) (S : Set E) (P : E → Fin n → Prop)
    (typed : ∀ e i, P e i → e ∈ S) :
    ∃ W : Set E, W ⊆ S ∧ W.Finite ∧ W.ncard ≤ n ∧
      ∀ i : Fin n, (∃ e, P e i) ↔ ∃ e ∈ W, P e i := by
  classical
  by_cases inhabited : Nonempty E
  · let active : Set (Fin n) := {i | ∃ e, P e i}
    let pick : Fin n → E := fun i => if h : ∃ e, P e i
      then Classical.choose h else Classical.choice inhabited
    let W := pick '' active
    have chosen : ∀ i ∈ active, P (pick i) i := by
      intro i hi
      have ex : ∃ e, P e i := hi
      simpa only [pick, dif_pos ex] using Classical.choose_spec ex
    have hf : active.Finite := Set.toFinite _
    refine ⟨W, ?_, hf.image pick, ?_, ?_⟩
    · rintro e ⟨i,hi,rfl⟩
      exact typed _ i (chosen i hi)
    · calc
        W.ncard ≤ active.ncard := Set.ncard_image_le hf
        _ ≤ Nat.card (Fin n) := Set.ncard_le_card active
        _ = n := by simp [Nat.card_eq_fintype_card]
    · intro i
      constructor
      · intro hi
        exact ⟨pick i,⟨i,hi,rfl⟩,chosen i hi⟩
      · rintro ⟨e,_,he⟩; exact ⟨e,he⟩
  · refine ⟨∅, Set.empty_subset S, Set.finite_empty, by simp, ?_⟩
    intro i
    constructor
    · rintro ⟨e,_⟩; exact False.elim (inhabited ⟨e⟩)
    · rintro ⟨e,he,_⟩; exact False.elim he

theorem two_members (S : Set E) (finite : S.Finite) :
    2 ≤ S.ncard ↔ ∃ i ∈ S, ∃ j ∈ S, i ≠ j := by
  exact Set.one_lt_ncard finite

end LCTR.CoreFiniteClassWitness
