import CoreValueJetChanges

namespace LCTR.CoreTimeJetChanges
set_option autoImplicit false
open Set Filter LCTR.CoreFiniteJets LCTR.CoreValueJetChanges
open scoped Topology
universe u v w z
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

def Acts (k : ℕ) (a b : ℝ) (V : Set E) (g : ℝ → ℝ) (gb : g b = a)
    (J : Domain k V → Domain k V) : Prop :=
  ∀ (c : ℝ → E) (_hc : ContDiffAt ℝ k c a) (hv : c a ∈ V),
    J (jetAt k a c V hv) = jetAt k b (c ∘ g) V (by simpa only [Function.comp_apply,gb] using hv)

theorem lift_unique (k : ℕ) (a b : ℝ) (V : Set E) (g : ℝ → ℝ) (gb : g b = a)
    (J K : Domain k V → Domain k V) (hj : Acts k a b V g gb J) (hk : Acts k a b V g gb K) : J=K := by
  funext v
  obtain ⟨c,hc,hv,rfl⟩ := domain_realization k a V v
  exact (hj c (hc.of_le le_top).contDiffAt hv).trans (hk c (hc.of_le le_top).contDiffAt hv).symm

theorem lift_identity (k : ℕ) (a : ℝ) (V : Set E)
    (J : Domain k V → Domain k V) (hj : Acts k a a V id rfl J) : J=id := by
  funext v
  obtain ⟨c,hc,hv,rfl⟩ := domain_realization k a V v
  exact hj c (hc.of_le le_top).contDiffAt hv

theorem lift_left_inverse (k : ℕ) (a b : ℝ) (V : Set E) (U : Set ℝ)
    (ou : IsOpen U) (ha : a ∈ U) (f g : ℝ → ℝ) (fa : f a=b) (gb : g b=a)
    (gs : ContDiffAt ℝ k g b) (inv : ∀ x ∈ U, g (f x)=x)
    (J K : Domain k V → Domain k V)
    (hj : Acts k a b V g gb J) (hk : Acts k b a V f fa K) : ∀ v, K (J v)=v := by
  intro v
  obtain ⟨c,hc,hv,rfl⟩ := domain_realization k a V v
  have hck : ContDiffAt ℝ k c a := (hc.of_le le_top).contDiffAt
  have hcb : ContDiffAt ℝ k c (g b) := gb.symm ▸ hck
  have hcg : ContDiffAt ℝ k (c ∘ g) b := hcb.comp b gs
  have hvb : (c ∘ g) b ∈ V := by simpa only [Function.comp_apply,gb] using hv
  rw [hj c hck hv,hk (c ∘ g) hcg hvb]
  apply jetAt_eventual_eq
  filter_upwards [ou.mem_nhds ha] with x hx
  change c (g (f x)) = c x
  rw [inv x hx]

theorem lift_bijective (k : ℕ) (a b : ℝ) (V : Set E) (U W : Set ℝ)
    (ou : IsOpen U) (ow : IsOpen W) (ha : a ∈ U) (hb : b ∈ W)
    (f g : ℝ → ℝ) (fa : f a=b) (gb : g b=a)
    (fs : ContDiffOn ℝ k f U) (gs : ContDiffOn ℝ k g W)
    (left : ∀ x ∈ U, g (f x)=x) (right : ∀ y ∈ W, f (g y)=y)
    (J K : Domain k V → Domain k V)
    (hj : Acts k a b V g gb J) (hk : Acts k b a V f fa K) : Function.Bijective J := by
  let e : Domain k V ≃ Domain k V :=
    { toFun := J
      invFun := K
      left_inv := lift_left_inverse k a b V U ou ha f g fa gb (gs.contDiffAt (ow.mem_nhds hb)) left J K hj hk
      right_inv := lift_left_inverse k b a V W ow hb g f gb fa (fs.contDiffAt (ou.mem_nhds ha)) right K J hk hj }
  exact e.bijective

theorem lift_composition (k : ℕ) (a b d : ℝ) (V : Set E) (g h : ℝ → ℝ)
    (gb : g b=a) (hd : h d=b) (gs : ContDiffAt ℝ k g b)
    (J K H : Domain k V → Domain k V)
    (hj : Acts k a b V g gb J) (hk : Acts k b d V h hd K)
    (hh : Acts k a d V (g ∘ h) ((congrArg g hd).trans gb) H) : K ∘ J=H := by
  funext v
  obtain ⟨c,hc,hv,rfl⟩ := domain_realization k a V v
  have hck : ContDiffAt ℝ k c a := (hc.of_le le_top).contDiffAt
  have hcb : ContDiffAt ℝ k c (g b) := gb.symm ▸ hck
  have hcg : ContDiffAt ℝ k (c ∘ g) b := hcb.comp b gs
  have hvb : (c ∘ g) b ∈ V := by simpa only [Function.comp_apply,gb] using hv
  change K (J _) = H _
  rw [hj c hck hv,hk (c ∘ g) hcg hvb,hh c hck hv]
  rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem base_and_fiber_bijective {X : Type u} {Y : Type v} {Z : Type w} {W : Type z}
    (base : X → Y) (hb : Function.Bijective base) (fiber : X → Z → W)
    (hf : ∀ x, Function.Bijective (fiber x)) :
    Function.Bijective (fun p : X × Z => (base p.1,fiber p.1 p.2)) := by
  constructor
  · rintro ⟨x,z⟩ ⟨y,w⟩ heq
    have hxy : x=y := hb.1 (congrArg Prod.fst heq)
    subst y
    have hzw : z=w := (hf x).1 (congrArg Prod.snd heq)
    subst w
    rfl
  · rintro ⟨y,w⟩
    obtain ⟨x,rfl⟩ := hb.2 y
    obtain ⟨z,rfl⟩ := (hf x).2 w
    exact ⟨(x,z),rfl⟩

theorem time_jet_full_domain_bijective (k : ℕ) (V : Set E) (U W : Set ℝ)
    (ou : IsOpen U) (ow : IsOpen W) (f g : ℝ → ℝ)
    (fm : MapsTo f U W) (gm : MapsTo g W U)
    (fs : ContDiffOn ℝ k f U) (gs : ContDiffOn ℝ k g W)
    (left : ∀ x ∈ U, g (f x)=x) (right : ∀ y ∈ W, f (g y)=y)
    (J K : ℝ → Domain k V → Domain k V)
    (hj : ∀ a (ha : a ∈ U), Acts k a (f a) V g (left a ha) (J a))
    (hk : ∀ a (_ha : a ∈ U), Acts k (f a) a V f rfl (K (f a))) :
    Function.Bijective (fun p : U × Domain k V =>
      ((⟨f p.1.val,fm p.1.property⟩ : W),J p.1.val p.2)) := by
  let e : U ≃ W :=
    { toFun := fun x => ⟨f x.val,fm x.property⟩
      invFun := fun y => ⟨g y.val,gm y.property⟩
      left_inv := fun x => Subtype.ext (left x.val x.property)
      right_inv := fun y => Subtype.ext (right y.val y.property) }
  apply base_and_fiber_bijective (fun x : U => (⟨f x.val,fm x.property⟩ : W)) e.bijective
    (fun x : U => J x.val)
  intro a
  exact lift_bijective k a.val (f a.val) V U W ou ow a.property (fm a.property)
    f g rfl (left a.val a.property) fs gs left right (J a.val) (K (f a.val))
    (hj a.val a.property) (hk a.val a.property)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem full_domain_relation_image {X : Type u} {Y : Type v} {Z : Type w} {W : Type z}
    (base : X → Y) (hb : Function.Bijective base) (fiber : X → Z → W)
    (hf : ∀ x, Function.Bijective (fiber x))
    (A : Set (X × Z)) (B : Set (Y × W))
    (cov : ∀ p, p ∈ A ↔ (base p.1,fiber p.1 p.2) ∈ B) :
    (fun p : X × Z => (base p.1,fiber p.1 p.2)) '' A = B :=
  relation_image _ _ _ (base_and_fiber_bijective base hb fiber hf).2 A B cov

end LCTR.CoreTimeJetChanges
