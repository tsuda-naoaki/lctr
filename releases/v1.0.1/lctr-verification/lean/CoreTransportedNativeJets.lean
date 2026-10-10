import CoreTransportedLawCharts
import CoreNativeLawJets

namespace LCTR.CoreTransportedNativeJets
set_option autoImplicit false
open Set LCTR.CoreLocalCharts LCTR.CoreTransportedLawCharts
open LCTR.CoreValueJetChanges
variable {T U TI : Type} {Val VI : Fin 2 → Type}
variable (e : T ≃ U) (a : Atlas T TI Val VI) (i : Index TI VI)

def sourceTheta (theta : NumericDomain (pushAtlas e a) i) : NumericDomain a i :=
  ⟨theta.val,by rw [← numeric_domain_preserved e a i]; exact theta.property⟩

theorem source_theta_value (theta : NumericDomain (pushAtlas e a) i) :
    (sourceTheta e a i theta).val = theta.val := rfl

theorem curve_at_transported_coordinate (theta : NumericDomain (pushAtlas e a) i) (s : Fin 2) :
    curve (pushAtlas e a) i theta s = curve a i (sourceTheta e a i theta) s := by
  obtain ⟨x,rfl⟩ := (time_coordinate_bijective (pushAtlas e a) i).2 theta
  have h := native_curve_preserved e a i (unliftJoint e a i x) s
  rw [joint_unlift_inverse] at h
  have coordinates : sourceTheta e a i (timeCoord (pushAtlas e a) i x) =
      timeCoord a i (unliftJoint e a i x) := by
    apply Subtype.ext
    have ht := numeric_time_preserved e a i (unliftJoint e a i x)
    rw [joint_unlift_inverse] at ht
    exact ht
  rw [coordinates]
  exact h

structure AtlasJetData (a : Atlas T TI Val VI) (i : Index TI VI) (s : Fin 2) (k : ℕ) where
  extension : ℝ → (Fin (a.dim s) → ℝ)
  agrees : ∀ theta : NumericDomain a i, extension theta.val = (curve a i theta s).val
  smooth : ∀ theta : NumericDomain a i, ContDiffAt ℝ k extension theta.val

variable (s : Fin 2) (k : ℕ) (d : AtlasJetData a i s k)

def pushJetData : AtlasJetData (pushAtlas e a) i s k where
  extension := d.extension
  agrees theta := by
    rw [curve_at_transported_coordinate]
    exact d.agrees (sourceTheta e a i theta)
  smooth theta := d.smooth (sourceTheta e a i theta)

theorem transported_extension_fixed : (pushJetData e a i s k d).extension = d.extension := rfl

theorem transported_regularity (theta : NumericDomain (pushAtlas e a) i) :
    ContDiffAt ℝ k (pushJetData e a i s k d).extension theta.val :=
  (pushJetData e a i s k d).smooth theta

theorem realization_in_value_chart (theta : NumericDomain a i) :
    d.extension theta.val ∈ (a.valChart s (i.2 s)).target := by
  rw [d.agrees theta]
  exact (curve a i theta s).property

noncomputable def atlasJet (theta : NumericDomain a i) :=
  jetAt k theta.val d.extension (a.valChart s (i.2 s)).target
    (realization_in_value_chart a i s k d theta)

theorem transported_jet_equal (theta : NumericDomain (pushAtlas e a) i) :
    atlasJet (pushAtlas e a) i s k (pushJetData e a i s k d) theta =
      atlasJet a i s k d (sourceTheta e a i theta) := rfl

theorem transported_jet_membership
    (relation : Set (NumericDomain a i × Domain k (a.valChart s (i.2 s)).target))
    (member : ∀ theta, (theta,atlasJet a i s k d theta) ∈ relation)
    (theta : NumericDomain (pushAtlas e a) i) :
    (sourceTheta e a i theta,atlasJet (pushAtlas e a) i s k (pushJetData e a i s k d) theta)
      ∈ relation := member (sourceTheta e a i theta)

open LCTR.CoreNativeLawComponents LCTR.CoreLawComponentCharts
variable {C D B I : Type} {Values : I → Type}
variable (context : Context C D B I Values) (component : ComponentInput context)
variable (atlas : NativeAtlas context component TI VI)
variable (j : Index TI VI) (side : Fin 2) (order : ℕ)
variable (native : LCTR.CoreNativeLawJets.SmoothRealization context component atlas j side order)

def nativeJetData : AtlasJetData atlas.val j side order :=
  ⟨native.extension,native.agrees,native.smooth⟩

theorem native_jet_data_exact (theta : NumericDomain atlas.val j) :
    atlasJet atlas.val j side order (nativeJetData context component atlas j side order native) theta =
      LCTR.CoreNativeLawJets.nativeJet context component atlas j side order native theta := rfl

theorem native_law_reindex_jet_exact
    (reindex : LCTR.LawTimeTransport.Reindex (NativeTime context) U)
    (theta : NumericDomain (transportedNativeAtlas context component atlas reindex) j) :
    atlasJet (transportedNativeAtlas context component atlas reindex) j side order
      (pushJetData (evaluationEquiv reindex (generated context component)) atlas.val j side order
        (nativeJetData context component atlas j side order native)) theta =
      LCTR.CoreNativeLawJets.nativeJet context component atlas j side order native
        (sourceTheta (evaluationEquiv reindex (generated context component)) atlas.val j theta) := rfl

end LCTR.CoreTransportedNativeJets
