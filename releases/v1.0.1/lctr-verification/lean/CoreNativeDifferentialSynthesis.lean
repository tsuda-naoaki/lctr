import CoreThreeLayerSynthesis
import CoreJointCoordinateFlattening

namespace LCTR.CoreNativeDifferentialSynthesis
set_option autoImplicit false
open Set LCTR.CoreObserverTime LCTR.CoreNativeCurves LCTR.CoreDynamicsBundle
open LCTR.CoreLawDifferentialBundle LCTR.CoreNativeDifferentialFamily
open LCTR.CoreLocalCharts LCTR.CoreNativeJointJets LCTR.CoreNativeDifferentialPredicates
open LCTR.CoreNativeAtlasConditions LCTR.CoreNativeTimeConditions
open LCTR.CoreNativeChartOverlaps LCTR.CoreRepresentationImages
variable {C D B U L J V W P N A : Type} {Arr : U → Type}
variable (b : Basis C D B U L J V W P N Arr) (law : LawData (A := A) b)
variable (f : CoreNativeDifferentialFamily.Family (context b) law)

noncomputable abbrev nativeInput := input (context b) law f
def Operative : Prop := LCTR.LawFamilyTransport.AllConditions (candidates b law) ∧
  LCTR.DifferentialNativeDomains.complete (nativeInput b law f)

variable (h : Operative b law f)
noncomputable def regular (rho : Rep (context b)) (j : f.raw.selected) :
    Regular (atlas (context b) law f.raw rho j) (f.raw.order j) :=
  Classical.choice (h.2.1 rho j)
include h in
theorem smooth (rho : Rep (context b)) (j : f.raw.selected) i :
    Diff2 (atlas (context b) law f.raw rho j) i (f.raw.order j) := h.2.2.1 rho j i
noncomputable def localPair (rho : Rep (context b)) (j : f.raw.selected) i
    (theta : NumericDomain (atlas (context b) law f.raw rho j) i) :=
  canonicalPair (atlas (context b) law f.raw rho j) i (f.raw.order j)
    (smooth b law f h rho j i) theta

include f h in
theorem same_law_objects_every_representation :
    ∀ rho : Rep (context b), ∃! x : CoreThreeLayerSynthesis.TransportedCore b law rho,
      CoreThreeLayerSynthesis.TransportedSpec b law rho x ∧
      LCTR.LawFamilyTransport.AllConditions x.2 :=
  CoreThreeLayerSynthesis.law_cores_all_embeddings b law h.1

theorem native_generated_jet_membership (rho : Rep (context b)) (j : f.raw.selected) i
    (theta : NumericDomain (atlas (context b) law f.raw rho j) i) :
    localPair b law f h rho j i theta ∈ f.relation rho j i := by
  have hm := (native_third_condition (context b) law f).mp h.2.2.2.1 rho j i
  exact (diff3_restricts _ _ _ _ (smooth b law f h rho j i)).mp hm theta

theorem native_flat_jet_membership (rho : Rep (context b)) (j : f.raw.selected) i
    (theta : NumericDomain (atlas (context b) law f.raw rho j) i) :
    CoreJointCoordinateFlattening.ambientEquiv (f.raw.dim j) (f.raw.order j)
      (jointRegion (atlas (context b) law f.raw rho j) i)
      (f.raw.time rho j i.1).target (localPair b law f h rho j i theta) ∈
    CoreJointCoordinateFlattening.ambientEquiv (f.raw.dim j) (f.raw.order j)
      (jointRegion (atlas (context b) law f.raw rho j) i)
      (f.raw.time rho j i.1).target '' f.relation rho j i :=
  ⟨localPair b law f h rho j i theta,native_generated_jet_membership b law f h rho j i theta,rfl⟩

theorem native_zeroth_values (rho : Rep (context b)) (j : f.raw.selected) i
    (x : JointDomain (atlas (context b) law f.raw rho j) i) (s : Fin 2) :
    (localPair b law f h rho j i
      (timeCoord (atlas (context b) law f.raw rho j) i x)).2.val 0 s =
    ((f.raw.valChart j s (i.2 s)).coordinates
      ⟨valuesAt (context b) (law.component j.val) rho s x.val,x.property.2 s⟩).val := by
  change (jointJet (atlas (context b) law f.raw rho j) i (f.raw.order j)
    (certifiedData _ _ _ (smooth b law f h rho j i)) (timeCoord _ _ x)).val 0 s = _
  rw [joint_zeroth_is_generated]
  exact congrArg Subtype.val (side_curve_generated (atlas (context b) law f.raw rho j) i x s)

theorem native_value_relation_image (rho : Rep (context b)) (j : f.raw.selected)
    (alpha : f.raw.timeIndex rho j) (beta gamma : (s : Fin 2) → f.raw.valIndex j s) :
    ((regular b law f h rho j).valChange alpha beta gamma).change.map ''
      {p | valueAmbient (atlas (context b) law f.raw rho j) (f.raw.order j)
        alpha beta gamma p ∈ f.relation rho j (alpha,beta)} =
      {p | valueAmbient (atlas (context b) law f.raw rho j) (f.raw.order j)
        alpha gamma beta p ∈ f.relation rho j (alpha,gamma)} := by
  have h4 := (native_fourth_condition (context b) law f).mp h.2.2.2.2.1 rho j
  exact value_relation_restriction_image _ _ _ (regular b law f h rho j)
    ((diff4_restricts _ _ _ (regular b law f h rho j)).mp h4) alpha beta gamma

noncomputable def timeChange (rho sigma : Rep (context b)) (j : f.raw.selected)
    (alpha : f.raw.timeIndex rho j) (delta : f.raw.timeIndex sigma j)
    (beta : (s : Fin 2) → f.raw.valIndex j s) :
    RepChange (f.raw.order j) (productChart (atlas (context b) law f.raw rho j) beta).target
      (between (context b) (law.component j.val) rho sigma)
      (f.raw.time rho j alpha) (f.raw.time sigma j delta) :=
  ((native_fifth_condition (context b) law f).mp h.2.2.2.2.2 rho sigma).2.2 j alpha delta beta |>.choose

theorem native_time_relation_image (rho sigma : Rep (context b)) (j : f.raw.selected)
    (alpha : f.raw.timeIndex rho j) (delta : f.raw.timeIndex sigma j)
    (beta : (s : Fin 2) → f.raw.valIndex j s) :
    (timeChange b law f h rho sigma j alpha delta beta).change.map ''
      {p | sourceAmbient (f.raw.order j) (productChart (atlas (context b) law f.raw rho j) beta).target
        (between (context b) (law.component j.val) rho sigma)
        (f.raw.time rho j alpha) (f.raw.time sigma j delta) p ∈ f.relation rho j (alpha,beta)} =
      {p | targetAmbient (f.raw.order j) (productChart (atlas (context b) law f.raw rho j) beta).target
        (between (context b) (law.component j.val) rho sigma)
        (f.raw.time rho j alpha) (f.raw.time sigma j delta) p ∈ f.relation sigma j (delta,beta)} := by
  exact rep_relation_restriction_image _ _ _ _ _ (timeChange b law f h rho sigma j alpha delta beta)
    _ _ (((native_fifth_condition (context b) law f).mp h.2.2.2.2.2 rho sigma).2.2
      j alpha delta beta).choose_spec

theorem time_change_zeroth_value (rho sigma : Rep (context b)) (j : f.raw.selected)
    (alpha : f.raw.timeIndex rho j) (delta : f.raw.timeIndex sigma j)
    (beta : (s : Fin 2) → f.raw.valIndex j s)
    (p : SourceSpace (f.raw.order j) (productChart (atlas (context b) law f.raw rho j) beta).target
      (between (context b) (law.component j.val) rho sigma)
      (f.raw.time rho j alpha) (f.raw.time sigma j delta)) :
    ((timeChange b law f h rho sigma j alpha delta beta).change.map p).2.val 0 = p.2.val 0 :=
  (timeChange b law f h rho sigma j alpha delta beta).change.preserves_zeroth_value p

theorem time_order_isomorphism_unique (rho sigma : Rep (context b)) :
    ∃! F : Set.range rho.value ≃o Set.range sigma.value,
      ∀ x, F (imageProjection rho.value x) = imageProjection sigma.value x := by
  apply image_order_iso_exists_unique
  · intro x y
    exact (embedding_injective b.data b.inc rho).eq_iff.trans
      (embedding_injective b.data b.inc sigma).eq_iff.symm
  · intro x y
    exact (rho.orderIff x y).symm.trans (sigma.orderIff x y)

theorem native_differential_synthesis :
    (∀ rho : Rep (context b), ∃! x : CoreThreeLayerSynthesis.TransportedCore b law rho,
      CoreThreeLayerSynthesis.TransportedSpec b law rho x ∧
      LCTR.LawFamilyTransport.AllConditions x.2) ∧
    (∀ rho (j : f.raw.selected), Nonempty (Regular (atlas (context b) law f.raw rho j) (f.raw.order j))) ∧
    (∀ rho (j : f.raw.selected) i theta, localPair b law f h rho j i theta ∈ f.relation rho j i) ∧
    (∀ rho (j : f.raw.selected), ValueCov (atlas (context b) law f.raw rho j) (f.raw.order j)
      (regular b law f h rho j) (f.relation rho j)) ∧
    (∀ rho sigma, TimeCondition (context b) law f rho sigma) := by
  refine ⟨same_law_objects_every_representation b law f h,
    fun rho j => ⟨regular b law f h rho j⟩,
    native_generated_jet_membership b law f h,?_,?_⟩
  · intro rho j
    exact (diff4_restricts _ _ _ (regular b law f h rho j)).mp
      ((native_fourth_condition (context b) law f).mp h.2.2.2.2.1 rho j)
  · intro rho sigma
    exact ((native_fifth_condition (context b) law f).mp h.2.2.2.2.2 rho sigma).2.2

end LCTR.CoreNativeDifferentialSynthesis
