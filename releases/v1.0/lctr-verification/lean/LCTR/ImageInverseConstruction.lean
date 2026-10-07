import Std

namespace LCTR.ImageInverseConstruction
universe u v

def Image {Source : Type u} {Target : Type v} (f : Source → Target) :=
  {target : Target // ∃ source, f source = target}

noncomputable def inverse {Source : Type u} {Target : Type v}
    (f : Source → Target) (target : Image f) : Source :=
  Classical.choose target.property

theorem inverse_right {Source : Type u} {Target : Type v}
    (f : Source → Target) (target : Image f) :
    f (inverse f target) = target.val :=
  Classical.choose_spec target.property

theorem inverse_left {Source : Type u} {Target : Type v}
    (f : Source → Target) (hf : Function.Injective f) (source : Source) :
    inverse f ⟨f source, ⟨source, rfl⟩⟩ = source :=
  hf (inverse_right f ⟨f source, ⟨source, rfl⟩⟩)

theorem inverse_characterization {Source : Type u} {Target : Type v}
    (f : Source → Target) (hf : Function.Injective f)
    (target : Image f) (source : Source) :
    inverse f target = source ↔ f source = target.val := by
  constructor
  · intro h
    rw [← h]
    exact inverse_right f target
  · intro h
    exact hf ((inverse_right f target).trans h.symm)

theorem inverse_exists_unique {Source : Type u} {Target : Type v}
    (f : Source → Target) (hf : Function.Injective f) :
    ∃ g : Image f → Source,
      (∀ source, g ⟨f source, ⟨source, rfl⟩⟩ = source) ∧
      (∀ target, f (g target) = target.val) ∧
      ∀ competing : Image f → Source,
        (∀ target, f (competing target) = target.val) → competing = g := by
  refine ⟨inverse f, inverse_left f hf, inverse_right f, ?_⟩
  intro competing h
  funext target
  exact hf ((h target).trans (inverse_right f target).symm)

theorem empty_source_image_inverse_exists :
    Nonempty (Image (Empty.elim : Empty → Unit) → Empty) :=
  ⟨inverse _⟩

theorem total_inverse_for_empty_source_impossible :
    ¬ Nonempty (Unit → Empty) := by
  intro ⟨f⟩
  exact Empty.elim (f ())

#print axioms inverse_right
#print axioms inverse_left
#print axioms inverse_characterization
#print axioms inverse_exists_unique
#print axioms empty_source_image_inverse_exists
#print axioms total_inverse_for_empty_source_impossible
end LCTR.ImageInverseConstruction
