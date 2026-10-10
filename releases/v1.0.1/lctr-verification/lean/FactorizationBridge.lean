import Mathlib.Data.Real.Basic
import LCTR.ScalarTimeTrajectoryFactorizationCurrentPaper
import LCTR.CanonicalObservableTimeFactorizationCurrentPaper
import LCTR.RealTimeOrderEmbeddingInjectivityCurrentPaper
import LCTR.ImageInverseConstruction

namespace LCTR.FactorizationBridgeV1

universe u v w x y z

abbrev Image {Source : Type u} {Target : Type v} (f : Source → Target) :=
  LCTR.ImageInverseConstruction.Image f



abbrev ProjectedTrajectoryDomain
    {CanonicalTrajectory : Type u}
    {OrderTime : Type v}
    (projection : CanonicalTrajectory → OrderTime) :=
  Image projection



def restrictedProjection
    {CanonicalTrajectory : Type u}
    {OrderTime : Type v}
    (projection : CanonicalTrajectory → OrderTime)
    (canonicalTime : CanonicalTrajectory) :
    ProjectedTrajectoryDomain projection :=
  ⟨projection canonicalTime, ⟨canonicalTime, rfl⟩⟩

 
theorem restrictedProjection_surjective
    {CanonicalTrajectory : Type u}
    {OrderTime : Type v}
    (projection : CanonicalTrajectory → OrderTime) :
    Function.Surjective (restrictedProjection projection) := by
  intro orderTime
  rcases orderTime.property with ⟨canonicalTime, hCanonicalTime⟩
  refine ⟨canonicalTime, ?_⟩
  apply Subtype.ext
  exact hCanonicalTime



def EqualityKernelCondition
    {CanonicalTrajectory : Type u}
    {OrderTime : Type v}
    {State : Type w}
    (projection : CanonicalTrajectory → OrderTime)
    (trajectory : CanonicalTrajectory → State) : Prop :=
  LCTR.CurrentPaperCorrespondence.EqualityKernelIncluded
    (restrictedProjection projection) trajectory







structure ScalarPaperPremises
    {CanonicalTrajectory : Type u}
    {OrderTime : Type v}
    {State : Type w}
    (DynCanTimeTrjCondAll KObsTimeIncTrans : Prop)
    (projection : CanonicalTrajectory → OrderTime)
    (trajectory : CanonicalTrajectory → State) : Prop where
  dynCanTimeTrj : DynCanTimeTrjCondAll
  obsTimeIncTrans : KObsTimeIncTrans
  obsTimeTrjFact : EqualityKernelCondition projection trajectory






theorem scalar_time_trajectory_factorization_adapter
    {CanonicalTrajectory : Type u}
    {OrderTime : Type v}
    {State : Type w}
    {DynCanTimeTrjCondAll KObsTimeIncTrans : Prop}
    (projection : CanonicalTrajectory → OrderTime)
    (trajectory : CanonicalTrajectory → State)
    (premises :
      ScalarPaperPremises
        DynCanTimeTrjCondAll KObsTimeIncTrans projection trajectory) :
    ∃ factor : ProjectedTrajectoryDomain projection → State,
      (∀ canonicalTime,
        trajectory canonicalTime =
          factor (restrictedProjection projection canonicalTime)) ∧
      ∀ competing : ProjectedTrajectoryDomain projection → State,
        (∀ canonicalTime,
          trajectory canonicalTime =
            competing (restrictedProjection projection canonicalTime)) →
        competing = factor := by
  exact
    LCTR.CurrentPaperCorrespondence.scalar_time_trajectory_factorization
      (restrictedProjection projection)
      trajectory
      (restrictedProjection_surjective projection)
      premises.obsTimeTrjFact

noncomputable def selectedOrderTrajectory
    {CanonicalTrajectory : Type u}
    {OrderTime : Type v}
    {State : Type w}
    {DynCanTimeTrjCondAll KObsTimeIncTrans : Prop}
    (projection : CanonicalTrajectory → OrderTime)
    (trajectory : CanonicalTrajectory → State)
    (premises :
      ScalarPaperPremises
        DynCanTimeTrjCondAll KObsTimeIncTrans projection trajectory) :
    ProjectedTrajectoryDomain projection → State :=
  Classical.choose
    (scalar_time_trajectory_factorization_adapter projection trajectory premises)

theorem selectedOrderTrajectory_factorization
    {CanonicalTrajectory : Type u}
    {OrderTime : Type v}
    {State : Type w}
    {DynCanTimeTrjCondAll KObsTimeIncTrans : Prop}
    (projection : CanonicalTrajectory → OrderTime)
    (trajectory : CanonicalTrajectory → State)
    (premises :
      ScalarPaperPremises
        DynCanTimeTrjCondAll KObsTimeIncTrans projection trajectory) :
    ∀ canonicalTime,
      trajectory canonicalTime =
        selectedOrderTrajectory projection trajectory premises
          (restrictedProjection projection canonicalTime) :=
  (Classical.choose_spec
    (scalar_time_trajectory_factorization_adapter
      projection trajectory premises)).1

theorem selectedOrderTrajectory_unique
    {CanonicalTrajectory : Type u}
    {OrderTime : Type v}
    {State : Type w}
    {DynCanTimeTrjCondAll KObsTimeIncTrans : Prop}
    (projection : CanonicalTrajectory → OrderTime)
    (trajectory : CanonicalTrajectory → State)
    (premises :
      ScalarPaperPremises
        DynCanTimeTrjCondAll KObsTimeIncTrans projection trajectory) :
    ∀ competing : ProjectedTrajectoryDomain projection → State,
      (∀ canonicalTime,
        trajectory canonicalTime =
          competing (restrictedProjection projection canonicalTime)) →
      competing = selectedOrderTrajectory projection trajectory premises :=
  (Classical.choose_spec
    (scalar_time_trajectory_factorization_adapter
      projection trajectory premises)).2

 
structure CanonicalObservablePaperPremises
    {CanonicalTrajectory : Type u}
    {OrderTime : Type v}
    {State : Type w}
    (DynCanTimeTrjCondAll KObsTimeIncTrans KCanObsDesc : Prop)
    (projection : CanonicalTrajectory → OrderTime)
    (trajectory : CanonicalTrajectory → State) : Prop where
  trajectoryPremises :
    ScalarPaperPremises
      DynCanTimeTrjCondAll KObsTimeIncTrans projection trajectory
  canObsDesc : KCanObsDesc

 
def restrictedRho
    {CanonicalTrajectory : Type u}
    {OrderTime : Type v}
    (projection : CanonicalTrajectory → OrderTime)
    (rho : OrderTime → ℝ)
    (orderTime : ProjectedTrajectoryDomain projection) : ℝ :=
  rho orderTime.val



abbrev RealTrajectoryDomain
    {CanonicalTrajectory : Type u}
    {OrderTime : Type v}
    (projection : CanonicalTrajectory → OrderTime)
    (rho : OrderTime → ℝ) :=
  Image (restrictedRho projection rho)

 
def restrictedEmbedding
    {CanonicalTrajectory : Type u}
    {OrderTime : Type v}
    (projection : CanonicalTrajectory → OrderTime)
    (rho : OrderTime → ℝ)
    (orderTime : ProjectedTrajectoryDomain projection) :
    RealTrajectoryDomain projection rho :=
  ⟨rho orderTime.val, ⟨orderTime, rfl⟩⟩

 
theorem restrictedEmbedding_surjective
    {CanonicalTrajectory : Type u}
    {OrderTime : Type v}
    (projection : CanonicalTrajectory → OrderTime)
    (rho : OrderTime → ℝ) :
    Function.Surjective (restrictedEmbedding projection rho) := by
  intro realTime
  rcases realTime.property with ⟨orderTime, hOrderTime⟩
  refine ⟨orderTime, ?_⟩
  apply Subtype.ext
  exact hOrderTime







theorem rho_injective_from_ordEmbSet
    {OrderTime : Type v}
    {KObsTimeIncTrans : Prop}
    (orderLt : OrderTime → OrderTime → Prop)
    (hObsTimeIncTrans : KObsTimeIncTrans)
    (hOrderTrichotomyFromIncTrans :
      KObsTimeIncTrans →
        ∀ left right : OrderTime,
          left = right ∨ orderLt left right ∨ orderLt right left)
    (rho : OrderTime → ℝ)
    (hRhoMember :
      LCTR.CurrentPaperCorrespondence.IsStrictOrderEmbedding
        orderLt (fun left right : ℝ => left < right) rho) :
    Function.Injective rho := by
  exact
    LCTR.CurrentPaperCorrespondence.real_time_order_embedding_member_injective
      orderLt
      (fun left right : ℝ => left < right)
      (fun realTime => lt_irrefl realTime)
      (hOrderTrichotomyFromIncTrans hObsTimeIncTrans)
      ⟨rho, hRhoMember⟩
      rho
      hRhoMember

theorem restrictedRho_injective
    {CanonicalTrajectory : Type u}
    {OrderTime : Type v}
    (projection : CanonicalTrajectory → OrderTime)
    (rho : OrderTime → ℝ)
    (hRhoInjective : Function.Injective rho) :
    Function.Injective (restrictedRho projection rho) := by
  intro left right hImage
  apply Subtype.ext
  exact hRhoInjective hImage

theorem restrictedEmbedding_injective
    {CanonicalTrajectory : Type u}
    {OrderTime : Type v}
    (projection : CanonicalTrajectory → OrderTime)
    (rho : OrderTime → ℝ)
    (hRhoInjective : Function.Injective rho) :
    Function.Injective (restrictedEmbedding projection rho) := by
  intro left right hImage
  apply Subtype.ext
  exact hRhoInjective (congrArg Subtype.val hImage)

noncomputable def realImageInverse
    {CanonicalTrajectory : Type u}
    {OrderTime : Type v}
    (projection : CanonicalTrajectory → OrderTime)
    (rho : OrderTime → ℝ) :
    RealTrajectoryDomain projection rho →
      ProjectedTrajectoryDomain projection :=
  LCTR.ImageInverseConstruction.inverse (restrictedRho projection rho)

theorem realImageInverse_left
    {CanonicalTrajectory : Type u}
    {OrderTime : Type v}
    (projection : CanonicalTrajectory → OrderTime)
    (rho : OrderTime → ℝ)
    (hRhoInjective : Function.Injective rho) :
    ∀ orderTime,
      realImageInverse projection rho
          (restrictedEmbedding projection rho orderTime) =
        orderTime := by
  exact
    LCTR.ImageInverseConstruction.inverse_left
      (restrictedRho projection rho)
      (restrictedRho_injective projection rho hRhoInjective)

theorem realImageInverse_right
    {CanonicalTrajectory : Type u}
    {OrderTime : Type v}
    (projection : CanonicalTrajectory → OrderTime)
    (rho : OrderTime → ℝ) :
    ∀ realTime,
      restrictedEmbedding projection rho
          (realImageInverse projection rho realTime) =
        realTime := by
  intro realTime
  apply Subtype.ext
  exact
    LCTR.ImageInverseConstruction.inverse_right
      (restrictedRho projection rho) realTime

noncomputable def orderObservableCurve
    {CanonicalTrajectory : Type u}
    {OrderTime : Type v}
    {State : Type w}
    {ObsIdx : Type x}
    {Value : Type y}
    {DynCanTimeTrjCondAll KObsTimeIncTrans : Prop}
    (projection : CanonicalTrajectory → OrderTime)
    (trajectory : CanonicalTrajectory → State)
    (premises :
      ScalarPaperPremises
        DynCanTimeTrjCondAll KObsTimeIncTrans projection trajectory)
    (observable : ObsIdx → State → Value)
    (ell : ObsIdx)
    (orderTime : ProjectedTrajectoryDomain projection) : Value :=
  observable ell (selectedOrderTrajectory projection trajectory premises orderTime)

noncomputable def realObservableCurve
    {CanonicalTrajectory : Type u}
    {OrderTime : Type v}
    {State : Type w}
    {ObsIdx : Type x}
    {Value : Type y}
    {DynCanTimeTrjCondAll KObsTimeIncTrans : Prop}
    (projection : CanonicalTrajectory → OrderTime)
    (trajectory : CanonicalTrajectory → State)
    (premises :
      ScalarPaperPremises
        DynCanTimeTrjCondAll KObsTimeIncTrans projection trajectory)
    (observable : ObsIdx → State → Value)
    (ell : ObsIdx)
    (rho : OrderTime → ℝ)
    (realTime : RealTrajectoryDomain projection rho) : Value :=
  orderObservableCurve projection trajectory premises observable ell
    (realImageInverse projection rho realTime)













theorem canonical_observable_time_factorization_adapter
    {CanonicalTrajectory : Type u}
    {OrderTime : Type v}
    {State : Type w}
    {ObsIdx : Type x}
    {Value : Type y}
    {DynCanTimeTrjCondAll KObsTimeIncTrans KCanObsDesc : Prop}
    (projection : CanonicalTrajectory → OrderTime)
    (trajectory : CanonicalTrajectory → State)
    (observable : ObsIdx → State → Value)
    (premises :
      CanonicalObservablePaperPremises
        DynCanTimeTrjCondAll KObsTimeIncTrans KCanObsDesc
        projection trajectory)
    (orderLt : OrderTime → OrderTime → Prop)
    (hOrderTrichotomyFromIncTrans :
      KObsTimeIncTrans →
        ∀ left right : OrderTime,
          left = right ∨ orderLt left right ∨ orderLt right left)
    (rho : OrderTime → ℝ)
    (hRhoMember :
      LCTR.CurrentPaperCorrespondence.IsStrictOrderEmbedding
        orderLt (fun left right : ℝ => left < right) rho)
    (ell : ObsIdx) :
    (∀ canonicalTime,
      trajectory canonicalTime =
        selectedOrderTrajectory
          projection trajectory premises.trajectoryPremises
          (restrictedProjection projection canonicalTime)) ∧
    (∀ canonicalTime,
      observable ell (trajectory canonicalTime) =
        orderObservableCurve
          projection trajectory premises.trajectoryPremises observable ell
          (restrictedProjection projection canonicalTime)) ∧
    (∀ canonicalTime,
      orderObservableCurve
          projection trajectory premises.trajectoryPremises observable ell
          (restrictedProjection projection canonicalTime) =
        realObservableCurve
          projection trajectory premises.trajectoryPremises observable ell rho
          (restrictedEmbedding projection rho
            (restrictedProjection projection canonicalTime))) ∧
    ∀ competing : RealTrajectoryDomain projection rho → Value,
      (∀ orderTime,
        competing (restrictedEmbedding projection rho orderTime) =
          orderObservableCurve
            projection trajectory premises.trajectoryPremises observable ell
            orderTime) →
      competing =
        realObservableCurve
          projection trajectory premises.trajectoryPremises observable ell rho := by
  let hRhoInjective : Function.Injective rho :=
    rho_injective_from_ordEmbSet
      orderLt
      premises.trajectoryPremises.obsTimeIncTrans
      hOrderTrichotomyFromIncTrans
      rho
      hRhoMember
  have hInverseLeft :
      ∀ orderTime,
        realImageInverse projection rho
            (restrictedEmbedding projection rho orderTime) =
          orderTime :=
    realImageInverse_left projection rho hRhoInjective
  have core :=
    LCTR.CurrentPaperCorrespondence.canonical_observable_time_factorization
      (restrictedProjection projection)
      trajectory
      (selectedOrderTrajectory
        projection trajectory premises.trajectoryPremises)
      (observable ell)
      (orderObservableCurve
        projection trajectory premises.trajectoryPremises observable ell)
      (realObservableCurve
        projection trajectory premises.trajectoryPremises observable ell rho)
      (restrictedEmbedding projection rho)
      (realImageInverse projection rho)
      (selectedOrderTrajectory_factorization
        projection trajectory premises.trajectoryPremises)
      (fun _ => rfl)
      (fun _ => rfl)
      hInverseLeft
      (restrictedEmbedding_surjective projection rho)
  refine
    ⟨selectedOrderTrajectory_factorization
        projection trajectory premises.trajectoryPremises,
      ?_, ?_, core.2⟩
  · intro canonicalTime
    exact (core.1 canonicalTime).1
  · intro canonicalTime
    exact (core.1 canonicalTime).2





theorem empty_canonical_carrier_supported
    {State : Type w}
    (trajectory : Empty → State) :
    ∃ factor :
        ProjectedTrajectoryDomain (Empty.elim : Empty → Unit) → State,
      (∀ canonicalTime,
        trajectory canonicalTime =
          factor
            (restrictedProjection
              (Empty.elim : Empty → Unit) canonicalTime)) ∧
      ∀ competing :
          ProjectedTrajectoryDomain (Empty.elim : Empty → Unit) → State,
        (∀ canonicalTime,
          trajectory canonicalTime =
            competing
              (restrictedProjection
                (Empty.elim : Empty → Unit) canonicalTime)) →
        competing = factor := by
  let premises :
      ScalarPaperPremises
        True True (Empty.elim : Empty → Unit) trajectory :=
    { dynCanTimeTrj := True.intro
      obsTimeIncTrans := True.intro
      obsTimeTrjFact := by
        intro left
        exact Empty.elim left }
  exact
    scalar_time_trajectory_factorization_adapter
      (Empty.elim : Empty → Unit) trajectory premises

namespace Negative






theorem no_factor_without_equality_kernel :
    ¬ ∃ factor : Unit → Bool,
        ∀ b : Bool, b = factor () := by
  rintro ⟨factor, hFactor⟩
  have hFalse : false = factor () := hFactor false
  have hTrue : true = factor () := hFactor true
  exact Bool.false_ne_true (hFalse.trans hTrue.symm)






theorem no_left_inverse_without_embedding_injectivity :
    ¬ ∃ inverse : Unit → Bool,
        ∀ b : Bool, inverse () = b := by
  rintro ⟨inverse, hInverse⟩
  have hFalse : inverse () = false := hInverse false
  have hTrue : inverse () = true := hInverse true
  exact Bool.false_ne_true (hFalse.symm.trans hTrue)

end Negative

#print axioms restrictedProjection_surjective
#print axioms scalar_time_trajectory_factorization_adapter
#print axioms selectedOrderTrajectory_factorization
#print axioms selectedOrderTrajectory_unique
#print axioms rho_injective_from_ordEmbSet
#print axioms restrictedEmbedding_surjective
#print axioms realImageInverse_left
#print axioms realImageInverse_right
#print axioms canonical_observable_time_factorization_adapter
#print axioms empty_canonical_carrier_supported
#print axioms Negative.no_factor_without_equality_kernel
#print axioms Negative.no_left_inverse_without_embedding_injectivity

end LCTR.FactorizationBridgeV1
