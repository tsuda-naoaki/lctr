namespace LCTR.FunctionalRelation

universe u v








theorem right_unique_relation_has_unique_domain_map
    {Input : Type u}
    {Output : Type v}
    (relation : Input → Output → Prop)
    (hRightUnique :
      ∀ input output₀ output₁,
        relation input output₀ →
        relation input output₁ →
        output₀ = output₁) :
    ∃ outputMap : {input : Input // ∃ output, relation input output} → Output,
      (∀ input output,
        relation input.1 output ↔ output = outputMap input) ∧
      ∀ competingMap,
        (∀ input output,
          relation input.1 output ↔ output = competingMap input) →
        competingMap = outputMap := by
  classical
  let outputMap :
      {input : Input // ∃ output, relation input output} → Output :=
    fun input => Classical.choose input.property
  have hOutputMap :
      ∀ input,
        relation input.1 (outputMap input) := by
    intro input
    exact Classical.choose_spec input.property
  refine ⟨outputMap, ?_, ?_⟩
  · intro input output
    constructor
    · intro hRelation
      exact hRightUnique input.1 output (outputMap input)
        hRelation (hOutputMap input)
    · intro hOutput
      simpa [hOutput] using hOutputMap input
  · intro competingMap hCompetingMap
    funext input
    exact ((hCompetingMap input (outputMap input)).mp
      (hOutputMap input)).symm

end LCTR.FunctionalRelation
