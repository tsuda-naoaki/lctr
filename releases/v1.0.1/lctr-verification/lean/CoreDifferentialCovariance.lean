import CoreTimeJetChanges
import CoreRepresentationImages

namespace LCTR.CoreDifferentialCovariance
set_option autoImplicit false
open Set LCTR.CoreValueJetChanges LCTR.CoreRepresentationImages
universe u v w z
variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

structure ValueChange (k : ℕ) (U : Set ℝ) (V : Set E) (W : Set F) where
  forward : E → F
  backward : F → E
  source_open : IsOpen V
  target_open : IsOpen W
  forward_maps : MapsTo forward V W
  backward_maps : MapsTo backward W V
  forward_smooth : ContDiffOn ℝ k forward V
  backward_smooth : ContDiffOn ℝ k backward W
  left_inverse : ∀ x ∈ V, backward (forward x) = x
  right_inverse : ∀ y ∈ W, forward (backward y) = y
  lift : ℝ → Domain k V → Domain k W
  inverse_lift : ℝ → Domain k W → Domain k V
  lift_action : ∀ a ∈ U, LCTR.CoreValueJetChanges.Acts k a V W forward forward_maps (lift a)
  inverse_action : ∀ a ∈ U, LCTR.CoreValueJetChanges.Acts k a W V backward backward_maps (inverse_lift a)

namespace ValueChange
variable {k : ℕ} {U : Set ℝ} {V : Set E} {W : Set F}

def map (c : ValueChange k U V W) (p : U × Domain k V) : U × Domain k W :=
  (p.1,c.lift p.1.val p.2)

theorem map_bijective (c : ValueChange k U V W) : Function.Bijective c.map := by
  apply LCTR.CoreTimeJetChanges.base_and_fiber_bijective id Function.bijective_id
    (fun a : U => c.lift a.val)
  intro a
  exact lift_bijective k a.val V W c.source_open c.target_open c.forward c.backward
    c.forward_maps c.backward_maps c.forward_smooth c.backward_smooth
    c.left_inverse c.right_inverse (c.lift a.val) (c.inverse_lift a.val)
    (c.lift_action a.val a.property) (c.inverse_action a.val a.property)

theorem preserves_time_coordinate (c : ValueChange k U V W) (p : U × Domain k V) :
    (c.map p).1 = p.1 := rfl

theorem relation_image (c : ValueChange k U V W)
    (A : Set (U × Domain k V)) (B : Set (U × Domain k W))
    (cov : ∀ p, p ∈ A ↔ c.map p ∈ B) : c.map '' A = B :=
  LCTR.CoreValueJetChanges.relation_image _ _ _ c.map_bijective.2 A B cov

end ValueChange

structure TimeChange (k : ℕ) (V : Set E) (U W : Set ℝ) where
  forward : ℝ → ℝ
  backward : ℝ → ℝ
  source_open : IsOpen U
  target_open : IsOpen W
  forward_maps : MapsTo forward U W
  backward_maps : MapsTo backward W U
  forward_smooth : ContDiffOn ℝ k forward U
  backward_smooth : ContDiffOn ℝ k backward W
  left_inverse : ∀ x ∈ U, backward (forward x) = x
  right_inverse : ∀ y ∈ W, forward (backward y) = y
  lift : ℝ → Domain k V → Domain k V
  inverse_lift : ℝ → Domain k V → Domain k V
  lift_action : ∀ a (ha : a ∈ U), LCTR.CoreTimeJetChanges.Acts k a (forward a) V
    backward (left_inverse a ha) (lift a)
  inverse_action : ∀ a (_ha : a ∈ U), LCTR.CoreTimeJetChanges.Acts k (forward a) a V
    forward rfl (inverse_lift (forward a))

namespace TimeChange
variable {k : ℕ} {V : Set E} {U W : Set ℝ}

def base (c : TimeChange k V U W) (a : U) : W :=
  ⟨c.forward a.val,c.forward_maps a.property⟩

def map (c : TimeChange k V U W) (p : U × Domain k V) : W × Domain k V :=
  (c.base p.1,c.lift p.1.val p.2)

theorem map_bijective (c : TimeChange k V U W) : Function.Bijective c.map :=
  LCTR.CoreTimeJetChanges.time_jet_full_domain_bijective k V U W c.source_open c.target_open
    c.forward c.backward c.forward_maps c.backward_maps c.forward_smooth c.backward_smooth
    c.left_inverse c.right_inverse c.lift c.inverse_lift c.lift_action c.inverse_action

theorem relation_image (c : TimeChange k V U W)
    (A : Set (U × Domain k V)) (B : Set (W × Domain k V))
    (cov : ∀ p, p ∈ A ↔ c.map p ∈ B) : c.map '' A = B :=
  LCTR.CoreValueJetChanges.relation_image _ _ _ c.map_bijective.2 A B cov

theorem preserves_zeroth_value (c : TimeChange k V U W) (p : U × Domain k V) :
    (c.map p).2.val 0 = p.2.val 0 := by
  obtain ⟨f,hf,hv,he⟩ := domain_realization k p.1.val V p.2
  change (c.lift p.1.val p.2).val 0 = p.2.val 0
  rw [← he,c.lift_action p.1.val p.1.property f (hf.of_le le_top).contDiffAt hv]
  simp only [jetAt,LCTR.CoreFiniteJets.jet,Fin.val_zero,iteratedDeriv_zero,
    Function.comp_apply,c.left_inverse p.1.val p.1.property]

end TimeChange

theorem differential_covariance
    {S : Type w} {I J : Type z} (f g : S → ℝ)
    (kernel : ∀ x y, f x = f y ↔ g x = g y)
    (ord : ∀ x y, f x < f y ↔ g x < g y)
    (kv : I → ℕ) (Uv : I → Set ℝ) (Vv : I → Set E) (Wv : I → Set F)
    (vc : ∀ i, ValueChange (kv i) (Uv i) (Vv i) (Wv i))
    (Av : ∀ i, Set (Uv i × Domain (kv i) (Vv i)))
    (Bv : ∀ i, Set (Uv i × Domain (kv i) (Wv i)))
    (value_cov : ∀ i p, p ∈ Av i ↔ (vc i).map p ∈ Bv i)
    (kt : J → ℕ) (Vt : J → Set E) (Ut Wt : J → Set ℝ)
    (tc : ∀ j, TimeChange (kt j) (Vt j) (Ut j) (Wt j))
    (At : ∀ j, Set (Ut j × Domain (kt j) (Vt j)))
    (Bt : ∀ j, Set (Wt j × Domain (kt j) (Vt j)))
    (time_cov : ∀ j p, p ∈ At j ↔ (tc j).map p ∈ Bt j)
    (source_coord : ∀ j, Ut j → range f) (target_coord : ∀ j, Wt j → range g)
    (chart_link : ∀ j a, imageOrderIso f g kernel ord (source_coord j a) =
      target_coord j ((tc j).base a)) :
    ∃! H : range f ≃o range g,
      (∀ x, H (imageProjection f x) = imageProjection g x) ∧
      (∀ i, (vc i).map '' Av i = Bv i) ∧
      (∀ j, (tc j).map '' At j = Bt j) ∧
      (∀ j a, H (source_coord j a) = target_coord j ((tc j).base a)) := by
  refine ⟨imageOrderIso f g kernel ord,?_,?_⟩
  · exact ⟨imageMap_commutes f g (fun x y => (kernel x y).mp),
      fun i => (vc i).relation_image (Av i) (Bv i) (value_cov i),
      fun j => (tc j).relation_image (At j) (Bt j) (time_cov j),chart_link⟩
  · intro H hH
    apply DFunLike.ext
    intro y
    exact congrFun (imageMap_unique f g (fun x y => (kernel x y).mp) H hH.1) y

end LCTR.CoreDifferentialCovariance
