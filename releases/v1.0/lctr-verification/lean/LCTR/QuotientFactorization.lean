import LCTR.ImageInverseComposition

namespace LCTR.Trajectory

universe u v w








theorem surjective_fiber_invariant_map_factors_uniquely
    {CanonicalTime : Type u}
    {OrderTime : Type v}
    {State : Type w}
    (projection : CanonicalTime → OrderTime)
    (trajectory : CanonicalTime → State)
    (hSurjective : Function.Surjective projection)
    (hFiberInvariant :
      ∀ left right,
        projection left = projection right →
          trajectory left = trajectory right) :
    ∃ factor : OrderTime → State,
      (∀ canonicalTime,
        trajectory canonicalTime = factor (projection canonicalTime)) ∧
      ∀ competing : OrderTime → State,
        (∀ canonicalTime,
          trajectory canonicalTime = competing (projection canonicalTime)) →
        competing = factor := by
  classical
  let representative : OrderTime → CanonicalTime := fun orderTime =>
    Classical.choose (hSurjective orderTime)
  have hRepresentative :
      ∀ orderTime, projection (representative orderTime) = orderTime := by
    intro orderTime
    exact Classical.choose_spec (hSurjective orderTime)
  let factor : OrderTime → State := fun orderTime =>
    trajectory (representative orderTime)
  have hFactorization :
      ∀ canonicalTime,
        trajectory canonicalTime = factor (projection canonicalTime) := by
    intro canonicalTime
    dsimp [factor]
    exact hFiberInvariant
      canonicalTime
      (representative (projection canonicalTime))
      (hRepresentative (projection canonicalTime)).symm
  refine ⟨factor, hFactorization, ?_⟩
  intro competing hCompeting
  funext orderTime
  rcases hSurjective orderTime with ⟨canonicalTime, hCanonicalTime⟩
  rw [← hCanonicalTime]
  exact (hCompeting canonicalTime).symm.trans
    (hFactorization canonicalTime)

end LCTR.Trajectory
