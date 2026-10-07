import CoreTransportedNativeJets
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace LCTR.CoreNativeJointJets
set_option autoImplicit false
open Set Filter LCTR.CoreLocalCharts LCTR.CoreValueJetChanges
open LCTR.CoreTransportedLawCharts LCTR.CoreTransportedNativeJets
open scoped Topology
variable {T U TI : Type} {Val VI : Fin 2 → Type}
variable (a : Atlas T TI Val VI) (i : Index TI VI) (k : ℕ)

abbrev JointValue := (s : Fin 2) → Fin (a.dim s) → ℝ
def jointRegion : Set (JointValue a) := {v | ∀ s, v s ∈ (a.valChart s (i.2 s)).target}
abbrev JetSpace := (a.time i.1).target × Domain k (jointRegion a i)
variable (d : ∀ s, AtlasJetData a i s k)

def jointExtension : ℝ → JointValue a := fun theta s => (d s).extension theta

theorem joint_extension_agrees (theta : NumericDomain a i) :
    jointExtension a i k d theta.val = fun s => (curve a i theta s).val := by
  funext s
  exact (d s).agrees theta

theorem joint_extension_smooth (theta : NumericDomain a i) :
    ContDiffAt ℝ k (jointExtension a i k d) theta.val :=
  contDiffAt_pi.mpr (fun s => (d s).smooth theta)

theorem joint_extension_in_region (theta : NumericDomain a i) :
    jointExtension a i k d theta.val ∈ jointRegion a i := by
  intro s
  exact realization_in_value_chart a i s k (d s) theta

noncomputable def jointJet (theta : NumericDomain a i) : Domain k (jointRegion a i) :=
  jetAt k theta.val (jointExtension a i k d) (jointRegion a i)
    (joint_extension_in_region a i k d theta)

theorem joint_zeroth_is_generated (theta : NumericDomain a i) :
    (jointJet a i k d theta).val 0 = fun s => (curve a i theta s).val := by
  simpa only [jointJet,jetAt,LCTR.CoreFiniteJets.jet,Fin.val_zero,iteratedDeriv_zero]
    using joint_extension_agrees a i k d theta

def fullTime (theta : NumericDomain a i) : (a.time i.1).target :=
  ⟨theta.val,by
    obtain ⟨x,hx⟩ := theta.property
    rw [← hx]
    exact ((a.time i.1).coordinates ⟨x.val,x.property.1⟩).property⟩

noncomputable def generatedPair (theta : NumericDomain a i) : JetSpace a i k :=
  (fullTime a i theta,jointJet a i k d theta)

theorem relation_membership_exact (relation : Set (JetSpace a i k)) :
    Set.range (generatedPair a i k d) ⊆ relation ↔
      ∀ theta, generatedPair a i k d theta ∈ relation := by
  constructor
  · intro h theta
    exact h ⟨theta,rfl⟩
  · intro h p hp
    obtain ⟨theta,rfl⟩ := hp
    exact h theta

theorem joint_realizations_agree_nearby
    (other : ∀ s, AtlasJetData a i s k) (opened : IsOpen (NumericDomain a i))
    (theta : NumericDomain a i) :
    jointExtension a i k d =ᶠ[𝓝 theta.val] jointExtension a i k other := by
  filter_upwards [opened.mem_nhds theta.property] with z hz
  exact (joint_extension_agrees a i k d ⟨z,hz⟩).trans
    (joint_extension_agrees a i k other ⟨z,hz⟩).symm

theorem joint_jet_independent_of_realizations
    (other : ∀ s, AtlasJetData a i s k) (opened : IsOpen (NumericDomain a i))
    (theta : NumericDomain a i) : jointJet a i k d theta = jointJet a i k other theta :=
  jetAt_eventual_eq k theta.val _ _ _ _ _
    (joint_realizations_agree_nearby a i k d other opened theta)

variable (e : T ≃ U)
def pushedData : ∀ s, AtlasJetData (pushAtlas e a) i s k :=
  fun s => pushJetData e a i s k (d s)

theorem pushed_joint_extension :
    jointExtension (pushAtlas e a) i k (pushedData a i k d e) =
      jointExtension a i k d := rfl

theorem pushed_joint_jet (theta : NumericDomain (pushAtlas e a) i) :
    jointJet (pushAtlas e a) i k (pushedData a i k d e) theta =
      jointJet a i k d (sourceTheta e a i theta) := rfl

theorem pushed_generated_pair (theta : NumericDomain (pushAtlas e a) i) :
    generatedPair (pushAtlas e a) i k (pushedData a i k d e) theta =
      generatedPair a i k d (sourceTheta e a i theta) := rfl

theorem pushed_relation_membership (relation : Set (JetSpace a i k))
    (member : ∀ theta, generatedPair a i k d theta ∈ relation) :
    ∀ theta, generatedPair (pushAtlas e a) i k (pushedData a i k d e) theta ∈ relation :=
  fun theta => member (sourceTheta e a i theta)

open LCTR.CoreNativeLawComponents LCTR.CoreLawComponentCharts LCTR.CoreObserverTime
variable {C D B I : Type} {Values : I → Type}
variable (c : Context C D B I Values) (l : ComponentInput c)
variable (native : NativeAtlas c l TI VI)
variable (realizations : ∀ s, LCTR.CoreNativeLawJets.SmoothRealization c l native i s k)

def nativeData : ∀ s, AtlasJetData native.val i s k :=
  fun s => nativeJetData c l native i s k (realizations s)

theorem joint_zeroth_native_values (x : JointDomain native.val i) :
    ∀ s, ∃ hs : nativeValues c l s x.val ∈ (native.val.valChart s (i.2 s)).source,
      (jointJet native.val i k (nativeData i k c l native realizations)
        (timeCoord native.val i x)).val 0 s =
      ((native.val.valChart s (i.2 s)).coordinates ⟨nativeValues c l s x.val,hs⟩).val := by
  intro s
  obtain ⟨hs,h⟩ := native_side_curve c l native i x s
  refine ⟨hs,?_⟩
  rw [joint_zeroth_is_generated]
  exact congrArg Subtype.val h

theorem joint_jets_all_time_embeddings :
    ∀ rho : RealEmbedding c.data c.inc,
      ∀ theta : NumericDomain
        (transportedNativeAtlas c l native (LCTR.CoreNativeLawGeneration.timeChange c rho)) i,
      generatedPair
        (transportedNativeAtlas c l native (LCTR.CoreNativeLawGeneration.timeChange c rho)) i k
        (pushedData native.val i k (nativeData i k c l native realizations)
          (evaluationEquiv (LCTR.CoreNativeLawGeneration.timeChange c rho) (generated c l))) theta =
      generatedPair native.val i k (nativeData i k c l native realizations)
        (sourceTheta
          (evaluationEquiv (LCTR.CoreNativeLawGeneration.timeChange c rho) (generated c l))
          native.val i theta) := fun _ _ => rfl

end LCTR.CoreNativeJointJets
