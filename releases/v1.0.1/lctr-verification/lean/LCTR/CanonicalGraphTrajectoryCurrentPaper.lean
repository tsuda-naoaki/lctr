import LCTR.LawCandidateRelationPartialOutputMapCurrentPaper

namespace LCTR.CurrentPaperCorrespondence

universe u v









theorem canonical_graph_trajectory_existence_and_uniqueness
    {TimeInput : Type u}
    {DynamicsState : Type v}
    (trajectoryRelation : TimeInput → DynamicsState → Prop)
    (hRightUnique :
      ∀ timeInput state₀ state₁,
        trajectoryRelation timeInput state₀ →
        trajectoryRelation timeInput state₁ →
        state₀ = state₁) :
    ∃ trajectoryMap :
        {timeInput : TimeInput //
          ∃ dynamicsState, trajectoryRelation timeInput dynamicsState} →
          DynamicsState,
      (∀ pair :
          {timeInput : TimeInput //
            ∃ dynamicsState, trajectoryRelation timeInput dynamicsState} ×
            DynamicsState,
        trajectoryRelation pair.1.1 pair.2 ↔
          pair.2 = trajectoryMap pair.1) ∧
      ∀ competingMap,
        (∀ pair :
            {timeInput : TimeInput //
              ∃ dynamicsState, trajectoryRelation timeInput dynamicsState} ×
              DynamicsState,
          trajectoryRelation pair.1.1 pair.2 ↔
            pair.2 = competingMap pair.1) →
        competingMap = trajectoryMap := by
  exact law_candidate_relation_partial_output_map
    trajectoryRelation hRightUnique

#print axioms canonical_graph_trajectory_existence_and_uniqueness

end LCTR.CurrentPaperCorrespondence
