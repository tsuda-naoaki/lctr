import CoreJointLawEvaluation
import CoreContinuumDatum
import CoreDifferentialFailure

namespace LCTR.CoreJointConditionRoutes
set_option autoImplicit false
open LCTR.CoreJointLawEvaluation LCTR.CoreNativeJointRelation LCTR.CoreJointTime
open LCTR.LawFamilyTransport LCTR.DifferentialNativeDomains LCTR.SelectedInputEvaluation
variable {C D B I R A Ω : Type}
variable (c : Context C D B I R) (obs : Observation c) (f : FamilyInput (A := A) c)

theorem joint_descent_route (r : R) (domain : Set (I → B))
    (sat : LCTR.CoreJointDescent.Sat (sourceSame c.objects) domain (c.sourceRelation r))
    (t : RealTime c) (x : I → B)
    (same : sourceProjection c.objects x = jointCurve c.objects c.base (orderInverse c t))
    (v : c.relValue r) :
    (t,v) ∈ realRelation c r ↔ (x,v) ∈ c.sourceRelation r :=
  joint_source_membership c.objects c.base domain (c.sourceRelation r) sat (orderInverse c t) x same v

theorem common_time_route (i : I) :
    Nonempty (LCTR.CoreObserverTime.RealEmbedding (c.objects.data i) (c.objects.inc i)) :=
  (embedding_transfers (c.objects.data i) (c.objects.data c.base)
    (c.objects.inc i) (c.objects.inc c.base)
    (c.objects.common i c.base) (c.objects.source i c.base) c.rho).1

theorem individual_trajectory_route (q : CommonDomain c.objects c.base) (i : I) :
    jointCurve c.objects c.base q i = individualCurve c.objects c.base i ⟨q.val,q.property i⟩ :=
  native_joint_components c.objects c.base q i

open LCTR.CoreTokenGraph LCTR.CoreEvaluation LCTR.CoreContinuumIntegration
open LCTR.CoreContinuumFailure LCTR.CoreContinuumDatum

theorem record_resolution_route (p : Packet) (fm ev co : Token → Bool) (s : Token → State)
    (rec : Recurs Edge fm ev co s)
    (matching : ∀ i, co (approxToken i)=condition p i)
    (ready : Ready fm ev s 2) :
    FA s 2 ↔ p.tolerance 2 < cellWidth p.maps p.cells :=
  width_failure p fm ev co s rec matching ready

theorem object_discernibility_route (p : Packet) (fm ev co : Token → Bool) (s : Token → State)
    (rec : Recurs Edge fm ev co s)
    (matching : ∀ i, co (approxToken i)=condition p i)
    (ready : Ready fm ev s 4) :
    FA s 4 ↔ p.tolerance 4 < scalar p.evaluations 2 := by
  have h := actual_failure p fm ev co s rec matching 4 ready
  simpa [Actual,firstDefect,not_le] using h

theorem joint_law_route :
    LCTR.CoreNativeLawFailure.failure (selected c obs f) () ↔
      ¬ AllConditions (family c obs f) := joint_failure_exact c obs f

theorem joint_law_minimal_route :
    ¬ AllConditions (family c obs f) ↔
      ∃ i, LCTR.CoreNativeLawFailure.minimalClass (selected c obs f) () i :=
  joint_minimal_failure_cover c obs f

abbrev JointFamily := Family (RealTime c) A
  (fun j => SideSpace c (f.law j).selectors 0) (fun j => SideSpace c (f.law j).selectors 1)

variable (diff : MatchingDifferential Unit (JointFamily c f) (Input Ω) (selected c obs f))

theorem selected_joint_law_exact (h : diff.domain ()) :
    (differentialInput diff () h).1=family c obs f := rfl

theorem joint_differential_route (h : diff.domain ()) :
    LCTR.CoreDifferentialFailure.failure diff AllConditions () ↔
      AllConditions (family c obs f) ∧ ¬ complete (diff.structureAt ⟨(),h⟩) := by
  have h' := LCTR.CoreDifferentialFailure.failure_vs_operative diff AllConditions () h
  change _ ↔ AllConditions (family c obs f) ∧
    ¬ (AllConditions (family c obs f) ∧ complete (diff.structureAt ⟨(),h⟩)) at h'
  rw [h']
  tauto

theorem joint_differential_minimal_route :
    LCTR.CoreDifferentialFailure.failure diff AllConditions () ↔
      ∃ i, LCTR.CoreDifferentialFailure.minimalFailure diff AllConditions () i :=
  LCTR.CoreDifferentialFailure.failure_cover diff AllConditions ()

theorem joint_differential_requires_same_law
    (h : LCTR.CoreDifferentialFailure.failure diff AllConditions ()) :
    AllConditions (family c obs f) := by
  obtain ⟨_,hl⟩ := h.1
  exact hl

theorem joint_differential_missing_domain (h : ¬ diff.domain ()) :
    ¬ LCTR.CoreDifferentialFailure.failure diff AllConditions () :=
  (LCTR.CoreDifferentialFailure.outside_selection_no_failure diff AllConditions () h).1

end LCTR.CoreJointConditionRoutes
