import LCTR.QuotientFactorization

namespace LCTR.Trajectory

universe u v w x y









theorem observable_factorization_through_order_and_real_time_is_unique
    {CanonicalTime : Type u}
    {OrderTime : Type v}
    {RealTime : Type w}
    {State : Type x}
    {Value : Type y}
    (projection : CanonicalTime → OrderTime)
    (canonicalTrajectory : CanonicalTime → State)
    (orderTrajectory : OrderTime → State)
    (observable : State → Value)
    (orderCurve : OrderTime → Value)
    (realCurve : RealTime → Value)
    (embedding : OrderTime → RealTime)
    (imageInverse : RealTime → OrderTime)
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
      ∀ orderTime, imageInverse (embedding orderTime) = orderTime)
    (hEmbeddingSurjective : Function.Surjective embedding) :
    (∀ canonicalTime,
      observable (canonicalTrajectory canonicalTime) =
        orderCurve (projection canonicalTime) ∧
      orderCurve (projection canonicalTime) =
        realCurve (embedding (projection canonicalTime))) ∧
    ∀ competing : RealTime → Value,
      (∀ orderTime,
        competing (embedding orderTime) = orderCurve orderTime) →
      competing = realCurve := by
  constructor
  · intro canonicalTime
    constructor
    · calc
        observable (canonicalTrajectory canonicalTime) =
            observable (orderTrajectory (projection canonicalTime)) :=
          congrArg observable (hTrajectoryFactorization canonicalTime)
        _ = orderCurve (projection canonicalTime) :=
          (hOrderCurve (projection canonicalTime)).symm
    · calc
        orderCurve (projection canonicalTime) =
            orderCurve (imageInverse (embedding (projection canonicalTime))) :=
          congrArg orderCurve (hInverseLeft (projection canonicalTime)).symm
        _ = realCurve (embedding (projection canonicalTime)) :=
          (hRealCurve (embedding (projection canonicalTime))).symm
  · intro competing hCompeting
    funext realTime
    rcases hEmbeddingSurjective realTime with ⟨orderTime, hOrderTime⟩
    rw [← hOrderTime]
    calc
      competing (embedding orderTime) = orderCurve orderTime :=
        hCompeting orderTime
      _ = orderCurve (imageInverse (embedding orderTime)) :=
        congrArg orderCurve (hInverseLeft orderTime).symm
      _ = realCurve (embedding orderTime) :=
        (hRealCurve (embedding orderTime)).symm

end LCTR.Trajectory
