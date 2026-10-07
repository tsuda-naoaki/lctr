import CoreFiniteJets
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Logic.Equiv.Basic

namespace LCTR.CoreValueJetChanges
set_option autoImplicit false
open Set Filter LCTR.CoreFiniteJets
open scoped Topology
universe u v w
variable {E : Type u} {F : Type v} {G : Type w}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

abbrev Domain (k : ℕ) (V : Set E) := {v : Fin (k+1) → E // v 0 ∈ V}

noncomputable def jetAt (k : ℕ) (a : ℝ) (f : ℝ → E) (V : Set E) (h : f a ∈ V) : Domain k V :=
  ⟨jet k a f,by simpa only [jet,Fin.val_zero,iteratedDeriv_zero] using h⟩

theorem jetAt_eventual_eq (k : ℕ) (a : ℝ) (V : Set E)
    (f g : ℝ → E) (hf : f a ∈ V) (hg : g a ∈ V) (he : f =ᶠ[𝓝 a] g) :
    jetAt k a f V hf = jetAt k a g V hg := by
  apply Subtype.ext
  funext n
  exact he.iteratedDeriv_eq n.val

theorem domain_realization (k : ℕ) (a : ℝ) (V : Set E) (v : Domain k V) :
    ∃ f : ℝ → E, ContDiff ℝ ⊤ f ∧ ∃ h : f a ∈ V, jetAt k a f V h = v := by
  let f := curve k a v.val
  have hf := curve_smooth k a v.val (n:=⊤)
  have h0 : f a = v.val 0 := by
    simpa only [Fin.val_zero,iteratedDeriv_zero] using curve_derivative k a v.val 0
  have hV : f a ∈ V := h0 ▸ v.property
  refine ⟨f,hf,hV,?_⟩
  apply Subtype.ext
  funext n
  exact curve_derivative k a v.val n

def Acts (k : ℕ) (a : ℝ) (V : Set E) (W : Set F) (f : E → F)
    (maps : MapsTo f V W) (J : Domain k V → Domain k W) : Prop :=
  ∀ (c : ℝ → E) (_hc : ContDiffAt ℝ k c a) (hv : c a ∈ V),
    J (jetAt k a c V hv) = jetAt k a (f ∘ c) W (maps hv)

theorem lift_unique (k : ℕ) (a : ℝ) (V : Set E) (W : Set F) (f : E → F)
    (maps : MapsTo f V W) (J K : Domain k V → Domain k W)
    (hj : Acts k a V W f maps J) (hk : Acts k a V W f maps K) : J = K := by
  funext v
  obtain ⟨c,hc,hv,rfl⟩ := domain_realization k a V v
  exact (hj c (hc.of_le le_top).contDiffAt hv).trans (hk c (hc.of_le le_top).contDiffAt hv).symm

theorem lift_identity (k : ℕ) (a : ℝ) (V : Set E)
    (J : Domain k V → Domain k V) (hj : Acts k a V V id (fun _ h => h) J) : J = id := by
  funext v
  obtain ⟨c,hc,hv,rfl⟩ := domain_realization k a V v
  exact hj c (hc.of_le le_top).contDiffAt hv

theorem lift_left_inverse (k : ℕ) (a : ℝ) (V : Set E) (W : Set F)
    (ov : IsOpen V) (f : E → F) (g : F → E)
    (fm : MapsTo f V W) (gm : MapsTo g W V)
    (fs : ContDiffOn ℝ k f V) (inv : ∀ x ∈ V, g (f x) = x)
    (J : Domain k V → Domain k W) (K : Domain k W → Domain k V)
    (hj : Acts k a V W f fm J) (hk : Acts k a W V g gm K) :
    ∀ v, K (J v) = v := by
  intro v
  obtain ⟨c,hc,hv,rfl⟩ := domain_realization k a V v
  have hck : ContDiffAt ℝ k c a := (hc.of_le le_top).contDiffAt
  have hfc : ContDiffAt ℝ k (f ∘ c) a := (fs.contDiffAt (ov.mem_nhds hv)).comp a hck
  rw [hj c hck hv,hk (f ∘ c) hfc (fm hv)]
  apply jetAt_eventual_eq
  have ev : ∀ᶠ x in 𝓝 a, c x ∈ V := hc.continuous.continuousAt (ov.mem_nhds hv)
  filter_upwards [ev] with x hx
  exact inv (c x) hx

def liftedEquiv (k : ℕ) (a : ℝ) (V : Set E) (W : Set F)
    (ov : IsOpen V) (ow : IsOpen W) (f : E → F) (g : F → E)
    (fm : MapsTo f V W) (gm : MapsTo g W V)
    (fs : ContDiffOn ℝ k f V) (gs : ContDiffOn ℝ k g W)
    (left : ∀ x ∈ V, g (f x)=x) (right : ∀ y ∈ W, f (g y)=y)
    (J : Domain k V → Domain k W) (K : Domain k W → Domain k V)
    (hj : Acts k a V W f fm J) (hk : Acts k a W V g gm K) : Domain k V ≃ Domain k W where
  toFun := J
  invFun := K
  left_inv := lift_left_inverse k a V W ov f g fm gm fs left J K hj hk
  right_inv := lift_left_inverse k a W V ow g f gm fm gs right K J hk hj

theorem lift_bijective (k : ℕ) (a : ℝ) (V : Set E) (W : Set F)
    (ov : IsOpen V) (ow : IsOpen W) (f : E → F) (g : F → E)
    (fm : MapsTo f V W) (gm : MapsTo g W V)
    (fs : ContDiffOn ℝ k f V) (gs : ContDiffOn ℝ k g W)
    (left : ∀ x ∈ V, g (f x)=x) (right : ∀ y ∈ W, f (g y)=y)
    (J : Domain k V → Domain k W) (K : Domain k W → Domain k V)
    (hj : Acts k a V W f fm J) (hk : Acts k a W V g gm K) : Function.Bijective J :=
  (liftedEquiv k a V W ov ow f g fm gm fs gs left right J K hj hk).bijective

theorem lift_composition (k : ℕ) (a : ℝ) (V : Set E) (W : Set F) (Z : Set G)
    (ov : IsOpen V) (f : E → F) (g : F → G)
    (fm : MapsTo f V W) (gm : MapsTo g W Z) (fs : ContDiffOn ℝ k f V)
    (J : Domain k V → Domain k W) (K : Domain k W → Domain k Z) (H : Domain k V → Domain k Z)
    (hj : Acts k a V W f fm J) (hk : Acts k a W Z g gm K)
    (hh : Acts k a V Z (g ∘ f) (gm.comp fm) H) : K ∘ J = H := by
  funext v
  obtain ⟨c,hc,hv,rfl⟩ := domain_realization k a V v
  have hck : ContDiffAt ℝ k c a := (hc.of_le le_top).contDiffAt
  have hfc : ContDiffAt ℝ k (f ∘ c) a := (fs.contDiffAt (ov.mem_nhds hv)).comp a hck
  change K (J _) = H _
  rw [hj c hck hv,hk (f ∘ c) hfc (fm hv),hh c hck hv]
  rfl

theorem relation_image (X : Type u) (Y : Type v) (J : X → Y)
    (onto : Function.Surjective J) (A : Set X) (B : Set Y)
    (cov : ∀ x, x ∈ A ↔ J x ∈ B) : J '' A = B := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (cov x).mp hx
  · intro hy
    obtain ⟨x,rfl⟩ := onto y
    exact ⟨x,(cov x).mpr hy,rfl⟩

theorem value_jet_relation_image (k : ℕ) (a : ℝ) (V : Set E) (W : Set F)
    (ov : IsOpen V) (ow : IsOpen W) (f : E → F) (g : F → E)
    (fm : MapsTo f V W) (gm : MapsTo g W V)
    (fs : ContDiffOn ℝ k f V) (gs : ContDiffOn ℝ k g W)
    (left : ∀ x ∈ V, g (f x)=x) (right : ∀ y ∈ W, f (g y)=y)
    (J : Domain k V → Domain k W) (K : Domain k W → Domain k V)
    (hj : Acts k a V W f fm J) (hk : Acts k a W V g gm K)
    (A : Set (Domain k V)) (B : Set (Domain k W))
    (cov : ∀ x, x ∈ A ↔ J x ∈ B) : J '' A = B :=
  relation_image _ _ J (lift_bijective k a V W ov ow f g fm gm fs gs left right J K hj hk).2 A B cov

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem empty_value_chart_control (k : ℕ) : IsEmpty (Domain k (∅ : Set E)) :=
  ⟨fun v => v.property⟩

end LCTR.CoreValueJetChanges
