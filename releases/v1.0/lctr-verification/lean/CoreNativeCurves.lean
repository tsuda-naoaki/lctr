import CoreObserverTime
import CoreRepresentationImages
import LCTR.ScalarTimeTrajectoryFactorizationCurrentPaper
import LCTR.CanonicalObservableTimeFactorizationCurrentPaper

namespace LCTR.CoreNativeCurves
set_option autoImplicit false
open LCTR.CoreTrajectoryDescent LCTR.CoreObserverTime LCTR.CoreRepresentationImages
universe u v w z
variable {C : Type u} {D : Type v} {B : Type w} {V : Type z}

abbrev State (d : Input C D B) := Q (genB d.relation d.binding)
def trajectoryRelation (d : Input C D B) : Time d → State d → Prop :=
  imageRelation (genC d.relation d.binding) (genB d.relation d.binding) d.relation
abbrev Domain (d : Input C D B) := {t : Time d // ∃ s, trajectoryRelation d t s}
def Single (d : Input C D B) : Prop :=
  ∀ t s₀ s₁, trajectoryRelation d t s₀ → trajectoryRelation d t s₁ → s₀ = s₁

noncomputable def canonicalTrajectory (d : Input C D B) (s : Single d) : Domain d → State d :=
  Classical.choose (native_graph_trajectory d.relation d.binding s)

theorem canonical_graph_contract (d : Input C D B) (s : Single d) :
    (∀ p : Domain d × State d,
      trajectoryRelation d p.1.val p.2 ↔ p.2 = canonicalTrajectory d s p.1) ∧
    (∀ other : Domain d → State d,
      (∀ p : Domain d × State d, trajectoryRelation d p.1.val p.2 ↔ p.2 = other p.1) →
      other = canonicalTrajectory d s) :=
  Classical.choose_spec (native_graph_trajectory d.relation d.binding s)

def orderValue (d : Input C D B) (h : IncTrans d) (x : Domain d) : OrderTime d h :=
  orderProjection d h x.val
abbrev OrderDomain (d : Input C D B) (h : IncTrans d) := Set.range (orderValue d h)
def restrictedProjection (d : Input C D B) (h : IncTrans d) : Domain d → OrderDomain d h :=
  imageProjection (orderValue d h)

theorem restricted_projection_contract (d : Input C D B) (h : IncTrans d) :
    Function.Surjective (restrictedProjection d h) ∧
    (∀ x y, restrictedProjection d h x = restrictedProjection d h y ↔
      LCTR.TransitiveIncomparabilityQuotientCore.Inc (strict d) x.val y.val) := by
  refine ⟨imageProjection_surjective _, ?_⟩
  intro x y
  exact Subtype.ext_iff.trans ((CoreObserverTime.projection_contract d h).2.1 x.val y.val)

def FiberCondition (d : Input C D B) (h : IncTrans d) (s : Single d) : Prop :=
  LCTR.CurrentPaperCorrespondence.EqualityKernelIncluded
    (restrictedProjection d h) (canonicalTrajectory d s)

theorem scalar_factor_exists_unique (d : Input C D B) (h : IncTrans d) (s : Single d)
    (k : FiberCondition d h s) :
    ∃ f : OrderDomain d h → State d,
      (∀ x, canonicalTrajectory d s x = f (restrictedProjection d h x)) ∧
      ∀ other, (∀ x, canonicalTrajectory d s x = other (restrictedProjection d h x)) → other = f :=
  LCTR.CurrentPaperCorrespondence.scalar_time_trajectory_factorization
    (restrictedProjection d h) (canonicalTrajectory d s) (restricted_projection_contract d h).1 k

noncomputable def scalarTrajectory (d : Input C D B) (h : IncTrans d) (s : Single d)
    (k : FiberCondition d h s) : OrderDomain d h → State d :=
  Classical.choose (scalar_factor_exists_unique d h s k)

theorem scalar_factor_contract (d : Input C D B) (h : IncTrans d) (s : Single d)
    (k : FiberCondition d h s) :
    (∀ x, canonicalTrajectory d s x = scalarTrajectory d h s k (restrictedProjection d h x)) ∧
    (∀ other, (∀ x, canonicalTrajectory d s x = other (restrictedProjection d h x)) →
      other = scalarTrajectory d h s k) :=
  Classical.choose_spec (scalar_factor_exists_unique d h s k)

theorem scalar_factor_requires_fiber (d : Input C D B) (h : IncTrans d) (s : Single d)
    (f : OrderDomain d h → State d)
    (commutes : ∀ x, canonicalTrajectory d s x = f (restrictedProjection d h x)) :
    FiberCondition d h s := by
  intro x y same
  rw [commutes x, commutes y, same]

def realValue (d : Input C D B) (h : IncTrans d) (rho : RealEmbedding d h)
    (q : OrderDomain d h) : ℝ := rho.value q.val
abbrev RealDomain (d : Input C D B) (h : IncTrans d) (rho : RealEmbedding d h) :=
  Set.range (realValue d h rho)
def realEmbedding (d : Input C D B) (h : IncTrans d) (rho : RealEmbedding d h) :
    OrderDomain d h → RealDomain d h rho := imageProjection (realValue d h rho)
noncomputable def realInverse (d : Input C D B) (h : IncTrans d) (rho : RealEmbedding d h) :
    RealDomain d h rho → OrderDomain d h := LCTR.ImageInverseConstruction.inverse (realValue d h rho)

theorem real_image_inverse_contract (d : Input C D B) (h : IncTrans d) (rho : RealEmbedding d h) :
    Function.Surjective (realEmbedding d h rho) ∧
    (∀ q, realInverse d h rho (realEmbedding d h rho q) = q) ∧
    (∀ t, realEmbedding d h rho (realInverse d h rho t) = t) := by
  have injective : Function.Injective (realValue d h rho) := by
    intro x y same
    exact Subtype.ext (embedding_injective d h rho same)
  refine ⟨imageProjection_surjective _, LCTR.ImageInverseConstruction.inverse_left _ injective, ?_⟩
  intro t
  exact Subtype.ext (LCTR.ImageInverseConstruction.inverse_right _ t)

theorem real_domain_composition (d : Input C D B) (h : IncTrans d) (rho : RealEmbedding d h) :
    Set.range (realValue d h rho) =
      Set.range (fun x : Domain d => timeRep d h rho x.val) := by
  ext t
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨x, hx⟩ := (restricted_projection_contract d h).1 q
    exact ⟨x, (congrArg (realValue d h rho) hx).trans hq⟩
  · rintro ⟨x, hx⟩
    exact ⟨restrictedProjection d h x, hx⟩

noncomputable def orderCurve (d : Input C D B) (h : IncTrans d) (s : Single d)
    (k : FiberCondition d h s) (obs : State d → V) : OrderDomain d h → V :=
  obs ∘ scalarTrajectory d h s k
noncomputable def realCurve (d : Input C D B) (h : IncTrans d) (s : Single d)
    (k : FiberCondition d h s) (rho : RealEmbedding d h) (obs : State d → V) :
    RealDomain d h rho → V := orderCurve d h s k obs ∘ realInverse d h rho

theorem observable_factorization (d : Input C D B) (h : IncTrans d) (s : Single d)
    (k : FiberCondition d h s) (rho : RealEmbedding d h) (obs : State d → V) :
    (∀ x, obs (canonicalTrajectory d s x) = orderCurve d h s k obs (restrictedProjection d h x) ∧
      orderCurve d h s k obs (restrictedProjection d h x) =
        realCurve d h s k rho obs (realEmbedding d h rho (restrictedProjection d h x))) ∧
    (∀ other : RealDomain d h rho → V,
      (∀ q, other (realEmbedding d h rho q) = orderCurve d h s k obs q) →
      other = realCurve d h s k rho obs) :=
  LCTR.CurrentPaperCorrespondence.canonical_observable_time_factorization
    (restrictedProjection d h) (canonicalTrajectory d s) (scalarTrajectory d h s k) obs
    (orderCurve d h s k obs) (realCurve d h s k rho obs) (realEmbedding d h rho) (realInverse d h rho)
    (scalar_factor_contract d h s k).1 (fun _ => rfl) (fun _ => rfl)
    (real_image_inverse_contract d h rho).2.1 (real_image_inverse_contract d h rho).1

theorem observable_curve_unique_from_canonical (d : Input C D B) (h : IncTrans d) (s : Single d)
    (k : FiberCondition d h s) (rho : RealEmbedding d h) (obs : State d → V)
    (other : RealDomain d h rho → V)
    (commutes : ∀ x, other (realEmbedding d h rho (restrictedProjection d h x)) =
      obs (canonicalTrajectory d s x)) : other = realCurve d h s k rho obs := by
  apply (observable_factorization d h s k rho obs).2
  intro q
  obtain ⟨x, rfl⟩ := (restricted_projection_contract d h).1 q
  exact (commutes x).trans ((observable_factorization d h s k rho obs).1 x).1

theorem empty_source_domain (d : Input C D B)
    (empty : ∀ c b r, ¬ d.relation c r b) : IsEmpty (Domain d) := by
  constructor
  rintro ⟨t, state, c, b, ⟨r, witness⟩, _, _⟩
  exact empty c b r witness

end LCTR.CoreNativeCurves
