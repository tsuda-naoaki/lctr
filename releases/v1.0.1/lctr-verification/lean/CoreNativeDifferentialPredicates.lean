import CoreNativeJointJets

namespace LCTR.CoreNativeDifferentialPredicates
set_option autoImplicit false
open Set Filter LCTR.CoreLocalCharts LCTR.CoreNativeJointJets
open LCTR.CoreTransportedLawCharts LCTR.CoreTransportedNativeJets LCTR.CoreValueJetChanges
open scoped Topology
variable {T U TI : Type} {Val VI : Fin 2 → Type}
variable (a : Atlas T TI Val VI) (i : Index TI VI) (k : ℕ)

noncomputable def totalCurve : ℝ → JointValue a := by
  classical
  exact fun t => if h : t ∈ NumericDomain a i then fun s => (curve a i ⟨t,h⟩ s).val else 0

theorem total_curve_on_domain (theta : NumericDomain a i) :
    totalCurve a i theta.val = fun s => (curve a i theta s).val := by
  simp only [totalCurve,dif_pos theta.property]

def Diff2 : Prop := IsOpen (NumericDomain a i) ∧
  ContDiffOn ℝ k (totalCurve a i) (NumericDomain a i)

noncomputable def certifiedData (h : Diff2 a i k) : ∀ s, AtlasJetData a i s k :=
  fun s => {
    extension := fun t => totalCurve a i t s
    agrees := fun theta => congrFun (total_curve_on_domain a i theta) s
    smooth := fun theta => contDiffAt_pi.mp (h.2.contDiffAt (h.1.mem_nhds theta.property)) s }

theorem diff2_exact : Diff2 a i k ↔
    IsOpen (NumericDomain a i) ∧ ContDiffOn ℝ k (totalCurve a i) (NumericDomain a i) := Iff.rfl

theorem diff2_iff_smooth_realizations : Diff2 a i k ↔
    IsOpen (NumericDomain a i) ∧ Nonempty (∀ s, AtlasJetData a i s k) := by
  constructor
  · intro h
    exact ⟨h.1,⟨certifiedData a i k h⟩⟩
  · rintro ⟨opened,⟨d⟩⟩
    refine ⟨opened,opened.contDiffOn_iff.mpr ?_⟩
    intro t ht
    apply (joint_extension_smooth a i k d ⟨t,ht⟩).congr_of_eventuallyEq
    filter_upwards [opened.mem_nhds ht] with z hz
    exact (total_curve_on_domain a i ⟨z,hz⟩).trans
      (joint_extension_agrees a i k d ⟨z,hz⟩).symm

noncomputable def canonicalPair (h : Diff2 a i k) (theta : NumericDomain a i) : JetSpace a i k :=
  generatedPair a i k (certifiedData a i k h) theta

theorem canonical_pair_from_any_realization (h : Diff2 a i k)
    (d : ∀ s, AtlasJetData a i s k) (theta : NumericDomain a i) :
    canonicalPair a i k h theta = generatedPair a i k d theta := by
  unfold canonicalPair generatedPair
  apply Prod.ext
  · rfl
  · exact joint_jet_independent_of_realizations a i k (certifiedData a i k h) d h.1 theta

def Diff3 (relation : Set (JetSpace a i k)) : Prop :=
  ∃ h : Diff2 a i k, ∀ theta, canonicalPair a i k h theta ∈ relation

theorem diff3_requires_diff2 (relation : Set (JetSpace a i k)) :
    Diff3 a i k relation → Diff2 a i k := fun h => h.choose

theorem diff3_restricts (relation : Set (JetSpace a i k)) (h : Diff2 a i k) :
    Diff3 a i k relation ↔ ∀ theta, canonicalPair a i k h theta ∈ relation := by
  constructor
  · rintro ⟨_,member⟩
    exact member
  · exact fun member => ⟨h,member⟩

theorem diff3_realization_independent (relation : Set (JetSpace a i k))
    (h : Diff2 a i k) (d : ∀ s, AtlasJetData a i s k) :
    Diff3 a i k relation ↔ ∀ theta, generatedPair a i k d theta ∈ relation := by
  rw [diff3_restricts a i k relation h]
  simp only [canonical_pair_from_any_realization a i k h d]

theorem diff3_false_outside (relation : Set (JetSpace a i k)) (h : ¬ Diff2 a i k) :
    ¬ Diff3 a i k relation := fun h3 => h (diff3_requires_diff2 a i k relation h3)

variable (e : T ≃ U)
theorem transported_total_curve : totalCurve (pushAtlas e a) i = totalCurve a i := by
  funext t
  by_cases ht : t ∈ NumericDomain (pushAtlas e a) i
  · have hs : t ∈ NumericDomain a i := by rwa [numeric_domain_preserved e a i] at ht
    rw [total_curve_on_domain (pushAtlas e a) i ⟨t,ht⟩,total_curve_on_domain a i ⟨t,hs⟩]
    funext s
    exact congrArg Subtype.val (curve_at_transported_coordinate e a i ⟨t,ht⟩ s)
  · have hs : t ∉ NumericDomain a i := by rwa [numeric_domain_preserved e a i] at ht
    simp only [totalCurve,dif_neg ht,dif_neg hs]
    rfl

theorem diff2_transport : Diff2 (pushAtlas e a) i k ↔ Diff2 a i k := by
  unfold Diff2
  rw [numeric_domain_preserved,transported_total_curve]
  rfl

theorem canonical_pair_transport (h : Diff2 a i k)
    (ht : Diff2 (pushAtlas e a) i k) (theta : NumericDomain (pushAtlas e a) i) :
    canonicalPair (pushAtlas e a) i k ht theta =
      canonicalPair a i k h (sourceTheta e a i theta) := by
  rw [canonical_pair_from_any_realization (pushAtlas e a) i k ht
    (pushedData a i k (certifiedData a i k h) e)]
  exact pushed_generated_pair a i k (certifiedData a i k h) e theta

theorem diff3_transport (relation : Set (JetSpace a i k)) :
    Diff3 (pushAtlas e a) i k relation ↔ Diff3 a i k relation := by
  constructor
  · rintro ⟨ht,member⟩
    have h := (diff2_transport a i k e).mp ht
    refine ⟨h,?_⟩
    intro theta
    have hb : theta.val ∈ NumericDomain (pushAtlas e a) i := by
      rw [numeric_domain_preserved]
      exact theta.property
    have mem := member ⟨theta.val,hb⟩
    rw [canonical_pair_transport a i k e h ht] at mem
    exact mem
  · rintro ⟨h,member⟩
    have ht := (diff2_transport a i k e).mpr h
    refine ⟨ht,?_⟩
    intro theta
    rw [canonical_pair_transport a i k e h ht]
    exact member _

end LCTR.CoreNativeDifferentialPredicates
