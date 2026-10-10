import FactorizationBridge
import OrderEmbeddingBridge

namespace LCTR.FactorizationBridgeV1.PaperFacing

open LCTR.TransitiveIncomparabilityQuotientCore

universe u v w x

abbrev IncTransCondition
    {S : Type u}
    (strict : S → S → Prop) : Prop :=
  ∀ {x y z}, Inc strict x y → Inc strict y z → Inc strict x z

abbrev CanonicalTrajectoryDomain
    {S : Type u}
    (trajectoryDomain : S → Prop) :=
  {time : S // trajectoryDomain time}

def paperRestrictedProjectionRaw
    {S : Type u}
    (strict : S → S → Prop)
    (irreflexive : ∀ time, ¬ strict time time)
    (incTransitive : IncTransCondition strict)
    (trajectoryDomain : S → Prop)
    (time : CanonicalTrajectoryDomain trajectoryDomain) :
    LCTR.OrderEmbeddingBridgeV1.IncQuotient
      strict irreflexive incTransitive :=
  LCTR.OrderEmbeddingBridgeV1.proj
    strict irreflexive incTransitive time.val

theorem quotient_trichotomy_from_order_embedding_bridge
    {S : Type u}
    (strict : S → S → Prop)
    (irreflexive : ∀ time, ¬ strict time time)
    (transitive :
      ∀ {x y z}, strict x y → strict y z → strict x z)
    (incTransitive : IncTransCondition strict) :
    ∀ left right :
        LCTR.OrderEmbeddingBridgeV1.IncQuotient
          strict irreflexive incTransitive,
      left = right ∨
        LCTR.OrderEmbeddingBridgeV1.quotientLt
          strict irreflexive incTransitive left right ∨
        LCTR.OrderEmbeddingBridgeV1.quotientLt
          strict irreflexive incTransitive right left := by
  intro left right
  by_cases hEq : left = right
  · exact Or.inl hEq
  · exact Or.inr
      ((LCTR.OrderEmbeddingBridgeV1.quotient_strict_linear_components
          strict irreflexive transitive incTransitive).2.2 hEq)

theorem canonical_observable_time_factorization_paper_wrapper
    {S : Type u}
    {State : Type v}
    {ObsIdx : Type w}
    {Value : Type x}
    {DynCanTimeTrjCondAll KCanObsDesc : Prop}
    (strict : S → S → Prop)
    (irreflexive : ∀ time, ¬ strict time time)
    (transitive :
      ∀ {x y z}, strict x y → strict y z → strict x z)
    (incTransitive : IncTransCondition strict)
    (trajectoryDomain : S → Prop)
    (trajectory : CanonicalTrajectoryDomain trajectoryDomain → State)
    (observable : ObsIdx → State → Value)
    (premises :
      CanonicalObservablePaperPremises
        DynCanTimeTrjCondAll
        (IncTransCondition strict)
        KCanObsDesc
        (paperRestrictedProjectionRaw
          strict irreflexive incTransitive trajectoryDomain)
        trajectory)
    (rho :
      LCTR.OrderEmbeddingBridgeV1.IncQuotient
        strict irreflexive incTransitive → ℝ)
    (hRhoMember :
      LCTR.CurrentPaperCorrespondence.IsStrictOrderEmbedding
        (LCTR.OrderEmbeddingBridgeV1.quotientLt
          strict irreflexive incTransitive)
        (fun left right : ℝ => left < right)
        rho)
    (ell : ObsIdx) :
    (∀ canonicalTime,
      trajectory canonicalTime =
        selectedOrderTrajectory
          (paperRestrictedProjectionRaw
            strict irreflexive incTransitive trajectoryDomain)
          trajectory premises.trajectoryPremises
          (restrictedProjection
            (paperRestrictedProjectionRaw
              strict irreflexive incTransitive trajectoryDomain)
            canonicalTime)) ∧
    (∀ canonicalTime,
      observable ell (trajectory canonicalTime) =
        orderObservableCurve
          (paperRestrictedProjectionRaw
            strict irreflexive incTransitive trajectoryDomain)
          trajectory premises.trajectoryPremises observable ell
          (restrictedProjection
            (paperRestrictedProjectionRaw
              strict irreflexive incTransitive trajectoryDomain)
            canonicalTime)) ∧
    (∀ canonicalTime,
      orderObservableCurve
          (paperRestrictedProjectionRaw
            strict irreflexive incTransitive trajectoryDomain)
          trajectory premises.trajectoryPremises observable ell
          (restrictedProjection
            (paperRestrictedProjectionRaw
              strict irreflexive incTransitive trajectoryDomain)
            canonicalTime) =
        realObservableCurve
          (paperRestrictedProjectionRaw
            strict irreflexive incTransitive trajectoryDomain)
          trajectory premises.trajectoryPremises observable ell rho
          (restrictedEmbedding
            (paperRestrictedProjectionRaw
              strict irreflexive incTransitive trajectoryDomain)
            rho
            (restrictedProjection
              (paperRestrictedProjectionRaw
                strict irreflexive incTransitive trajectoryDomain)
              canonicalTime))) ∧
    ∀ competing :
        RealTrajectoryDomain
          (paperRestrictedProjectionRaw
            strict irreflexive incTransitive trajectoryDomain)
          rho → Value,
      (∀ orderTime,
        competing
            (restrictedEmbedding
              (paperRestrictedProjectionRaw
                strict irreflexive incTransitive trajectoryDomain)
              rho orderTime) =
          orderObservableCurve
            (paperRestrictedProjectionRaw
              strict irreflexive incTransitive trajectoryDomain)
            trajectory premises.trajectoryPremises observable ell
            orderTime) →
      competing =
        realObservableCurve
          (paperRestrictedProjectionRaw
            strict irreflexive incTransitive trajectoryDomain)
          trajectory premises.trajectoryPremises observable ell rho := by
  exact
    canonical_observable_time_factorization_adapter
      (paperRestrictedProjectionRaw
        strict irreflexive incTransitive trajectoryDomain)
      trajectory
      observable
      premises
      (LCTR.OrderEmbeddingBridgeV1.quotientLt
        strict irreflexive incTransitive)
      (fun _ =>
        quotient_trichotomy_from_order_embedding_bridge
          strict irreflexive transitive incTransitive)
      rho
      hRhoMember
      ell

#print axioms quotient_trichotomy_from_order_embedding_bridge
#print axioms canonical_observable_time_factorization_paper_wrapper

end LCTR.FactorizationBridgeV1.PaperFacing
