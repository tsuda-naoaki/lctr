import LCTR.OrderEmbeddingInjectivity

namespace LCTR.OrderEmbedding

universe u v








theorem image_inverse_composition_from_characterization
    {Source : Type u}
    {Target : Type v}
    (embedding : Source → Target)
    (inverseOnImage : Target → Source)
    (hInverseCharacterization :
      ∀ target,
        (∃ source, embedding source = target) →
          ∀ source,
            inverseOnImage target = source ↔ embedding source = target) :
    (∀ source, inverseOnImage (embedding source) = source) ∧
    (∀ target,
      (∃ source, embedding source = target) →
        embedding (inverseOnImage target) = target) := by
  constructor
  · intro source
    have hImage : ∃ candidate, embedding candidate = embedding source :=
      ⟨source, rfl⟩
    exact
      (hInverseCharacterization
        (embedding source) hImage source).2 rfl
  · intro target hImage
    rcases hImage with ⟨source, hSource⟩
    have hInverse : inverseOnImage target = source :=
      (hInverseCharacterization
        target ⟨source, hSource⟩ source).2 hSource
    rw [hInverse]
    exact hSource

end LCTR.OrderEmbedding
