import LCTR.FunctionalRelation

namespace LCTR.CurrentPaperCorrespondence

universe u v









theorem law_candidate_relation_partial_output_map
    {Input : Type u}
    {Output : Type v}
    (relation : Input → Output → Prop)
    (hRightUnique :
      ∀ input output₀ output₁,
        relation input output₀ →
        relation input output₁ →
        output₀ = output₁) :
    ∃ outputMap : {input : Input // ∃ output, relation input output} → Output,
      (∀ pair :
          {input : Input // ∃ output, relation input output} × Output,
        relation pair.1.1 pair.2 ↔ pair.2 = outputMap pair.1) ∧
      ∀ competingMap,
        (∀ pair :
            {input : Input // ∃ output, relation input output} × Output,
          relation pair.1.1 pair.2 ↔ pair.2 = competingMap pair.1) →
        competingMap = outputMap := by
  rcases LCTR.FunctionalRelation.right_unique_relation_has_unique_domain_map
      relation hRightUnique with
    ⟨outputMap, hGraph, hUnique⟩
  refine ⟨outputMap, ?_, ?_⟩
  · intro pair
    exact hGraph pair.1 pair.2
  · intro competingMap hCompeting
    apply hUnique competingMap
    intro input output
    exact hCompeting (input, output)

#print axioms law_candidate_relation_partial_output_map

end LCTR.CurrentPaperCorrespondence
