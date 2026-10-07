import Mathlib.Data.Set.Card

namespace LCTR.CoreRelativeClassWitness
set_option autoImplicit false
universe u
variable {E : Type u}

theorem product_nonempty (n : ℕ) (P : Fin n → Set E) :
    Nonempty ((i : Fin n) → {e : E // e ∈ P i}) ↔ ∀ i, (P i).Nonempty := by
  classical
  constructor
  · rintro ⟨w⟩ i
    exact ⟨(w i).val, (w i).property⟩
  · intro h
    exact ⟨fun i => ⟨Classical.choose (h i), Classical.choose_spec (h i)⟩⟩

theorem witness_family (n : ℕ) (P : Fin n → Set E) :
    (∀ i, (P i).Nonempty) ↔ ∃ w : Fin n → E, ∀ i, w i ∈ P i := by
  classical
  exact ⟨fun h => ⟨fun i => Classical.choose (h i), fun i => Classical.choose_spec (h i)⟩,
    fun ⟨w, h⟩ i => ⟨w i, h i⟩⟩

theorem supplied_image (n : ℕ) (S : Set E) (P : Fin n → Set E)
    (typed : ∀ i, P i ⊆ S) (w : Fin n → E) (hw : ∀ i, w i ∈ P i) :
    Set.range w ⊆ S ∧ (Set.range w).Finite ∧ (Set.range w).ncard ≤ n ∧
      ∀ i, (Set.range w ∩ P i).Nonempty := by
  classical
  have finiteRange : (Set.range w).Finite := by
    simpa only [Set.image_univ] using (Set.finite_univ : (Set.univ : Set (Fin n)).Finite).image w
  refine ⟨?_, finiteRange, ?_, ?_⟩
  · rintro e ⟨i, rfl⟩
    exact typed i (hw i)
  · calc
      (Set.range w).ncard ≤ (Set.univ : Set (Fin n)).ncard := by
        simpa only [Set.image_univ] using
          (Set.ncard_image_le (f := w) (Set.finite_univ : (Set.univ : Set (Fin n)).Finite))
      _ ≤ Nat.card (Fin n) := Set.ncard_le_card _
      _ = n := by simp [Nat.card_eq_fintype_card]
  · intro i
    exact ⟨w i, ⟨Set.mem_range_self i, hw i⟩⟩

end LCTR.CoreRelativeClassWitness
