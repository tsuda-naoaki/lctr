import LCTR.ObservableFactorization

namespace LCTR.CurrentPaperCorrespondence

universe u v w x y









theorem canonical_observable_time_factorization
    {CanonicalTime : Type u}
    {OrderTime : Type v}
    {RealTimeImage : Type w}
    {State : Type x}
    {Value : Type y}
    (projection : CanonicalTime → OrderTime)
    (canonicalTrajectory : CanonicalTime → State)
    (orderTrajectory : OrderTime → State)
    (observable : State → Value)
    (orderCurve : OrderTime → Value)
    (realCurve : RealTimeImage → Value)
    (embedding : OrderTime → RealTimeImage)
    (imageInverse : RealTimeImage → OrderTime)
    (hTrajectoryFactorization :
      ∀ canonicalTime,
        canonicalTrajectory canonicalTime =
          orderTrajectory (projection canonicalTime))
    (hOrderCurve :
      ∀ orderTime,
        orderCurve orderTime = observable (orderTrajectory orderTime))
    (hRealCurve :
      ∀ realTime,
        realCurve realTime = orderCurve (imageInverse realTime))
    (hInverseLeft :
      ∀ orderTime,
        imageInverse (embedding orderTime) = orderTime)
    (hRestrictedEmbeddingSurjective : Function.Surjective embedding) :
    (∀ canonicalTime,
      observable (canonicalTrajectory canonicalTime) =
        orderCurve (projection canonicalTime) ∧
      orderCurve (projection canonicalTime) =
        realCurve (embedding (projection canonicalTime))) ∧
    ∀ competing : RealTimeImage → Value,
      (∀ orderTime,
        competing (embedding orderTime) = orderCurve orderTime) →
      competing = realCurve := by
  exact LCTR.Trajectory.observable_factorization_through_order_and_real_time_is_unique
    projection
    canonicalTrajectory
    orderTrajectory
    observable
    orderCurve
    realCurve
    embedding
    imageInverse
    hTrajectoryFactorization
    hOrderCurve
    hRealCurve
    hInverseLeft
    hRestrictedEmbeddingSurjective

#print axioms canonical_observable_time_factorization

end LCTR.CurrentPaperCorrespondence
