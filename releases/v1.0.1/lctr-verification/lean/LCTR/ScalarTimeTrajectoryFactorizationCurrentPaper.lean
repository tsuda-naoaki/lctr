import LCTR.QuotientFactorization

namespace LCTR.CurrentPaperCorrespondence

universe u v w

 
def EqualityKernelIncluded
    {Source : Type u}
    {Quotient : Type v}
    {Target : Type w}
    (projection : Source → Quotient)
    (trajectory : Source → Target) : Prop :=
  ∀ left right,
    projection left = projection right →
      trajectory left = trajectory right









theorem scalar_time_trajectory_factorization
    {CanonicalTime : Type u}
    {OrderTime : Type v}
    {State : Type w}
    (projection : CanonicalTime → OrderTime)
    (trajectory : CanonicalTime → State)
    (hProjectionSurjective : Function.Surjective projection)
    (hEqualityKernelIncluded :
      EqualityKernelIncluded projection trajectory) :
    ∃ factor : OrderTime → State,
      (∀ canonicalTime,
        trajectory canonicalTime = factor (projection canonicalTime)) ∧
      ∀ competing : OrderTime → State,
        (∀ canonicalTime,
          trajectory canonicalTime = competing (projection canonicalTime)) →
        competing = factor := by
  exact LCTR.Trajectory.surjective_fiber_invariant_map_factors_uniquely
    projection
    trajectory
    hProjectionSurjective
    hEqualityKernelIncluded

#print axioms scalar_time_trajectory_factorization

end LCTR.CurrentPaperCorrespondence
