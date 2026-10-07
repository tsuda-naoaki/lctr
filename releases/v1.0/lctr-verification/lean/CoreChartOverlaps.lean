import CoreDifferentialCovariance
import Mathlib.Logic.Equiv.Set

namespace LCTR.CoreChartOverlaps
set_option autoImplicit false
open Set LCTR.CoreRepresentationImages
universe u v
variable {X : Type u} {Y : Type v}

def overlap (h : X ≃ Y) (D : Set X) (E : Set Y) : Set D :=
  {x | h x.val ∈ E}

def overlapEquiv (h : X ≃ Y) (D : Set X) (E : Set Y) :
    overlap h D E ≃ overlap h.symm E D where
  toFun x := ⟨⟨h x.val.val,x.property⟩,by simpa only [overlap,mem_ofPred_eq,h.symm_apply_apply] using x.val.property⟩
  invFun y := ⟨⟨h.symm y.val.val,y.property⟩,by simpa only [overlap,mem_ofPred_eq,h.apply_symm_apply] using y.val.property⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; exact h.symm_apply_apply x.val.val
  right_inv y := by apply Subtype.ext; apply Subtype.ext; exact h.apply_symm_apply y.val.val

def coordinate (D : Set X) (U : Set ℝ) (c : D ≃ U) (x : D) : ℝ := (c x).val

theorem coordinate_injective (D : Set X) (U : Set ℝ) (c : D ≃ U) :
    Function.Injective (coordinate D U c) := by
  intro x y he
  exact c.injective (Subtype.ext he)

def coordinateDomain (h : X ≃ Y) (D : Set X) (E : Set Y) (U : Set ℝ) (c : D ≃ U) : Set ℝ :=
  coordinate D U c '' overlap h D E

noncomputable def coordinateEquiv (h : X ≃ Y) (D : Set X) (E : Set Y) (U : Set ℝ) (c : D ≃ U) :
    overlap h D E ≃ coordinateDomain h D E U c :=
  Equiv.Set.image (coordinate D U c) (overlap h D E) (coordinate_injective D U c)

noncomputable def chartEquiv (h : X ≃ Y) (D : Set X) (E : Set Y) (U V : Set ℝ)
    (c : D ≃ U) (d : E ≃ V) : coordinateDomain h D E U c ≃ coordinateDomain h.symm E D V d :=
  ((coordinateEquiv h D E U c).symm.trans (overlapEquiv h D E)).trans
    (coordinateEquiv h.symm E D V d)

theorem coordinate_domain_formula (h : X ≃ Y) (D : Set X) (E : Set Y) (U : Set ℝ) (c : D ≃ U) :
    coordinateDomain h D E U c =
      {a | ∃ x : D, h x.val ∈ E ∧ (c x).val = a} := by
  rfl

theorem chart_commutes (h : X ≃ Y) (D : Set X) (E : Set Y) (U V : Set ℝ)
    (c : D ≃ U) (d : E ≃ V) (a : coordinateDomain h D E U c) :
    h ((coordinateEquiv h D E U c).symm a).val.val =
      ((coordinateEquiv h.symm E D V d).symm (chartEquiv h D E U V c d a)).val.val := by
  change h _ = ((coordinateEquiv h.symm E D V d).symm
    ((coordinateEquiv h.symm E D V d) ((overlapEquiv h D E) ((coordinateEquiv h D E U c).symm a)))).val.val
  rw [Equiv.symm_apply_apply]
  rfl

theorem chart_forward_formula (h : X ≃ Y) (D : Set X) (E : Set Y) (U V : Set ℝ)
    (c : D ≃ U) (d : E ≃ V) (x : overlap h D E) :
    (chartEquiv h D E U V c d ((coordinateEquiv h D E U c) x)).val =
      (d ⟨h x.val.val,x.property⟩).val := by
  change ((coordinateEquiv h.symm E D V d)
    ((overlapEquiv h D E) ((coordinateEquiv h D E U c).symm ((coordinateEquiv h D E U c) x)))).val = _
  rw [Equiv.symm_apply_apply]
  rfl

noncomputable def realExtension {U V : Set ℝ} (e : U ≃ V) : ℝ → ℝ := by
  classical
  exact fun a => if ha : a ∈ U then (e ⟨a,ha⟩).val else 0

theorem realExtension_on_domain {U V : Set ℝ} (e : U ≃ V) (a : U) :
    realExtension e a.val = (e a).val := by
  simp only [realExtension,dif_pos a.property]

theorem realExtension_maps {U V : Set ℝ} (e : U ≃ V) : MapsTo (realExtension e) U V := by
  intro a ha
  rw [realExtension_on_domain e ⟨a,ha⟩]
  exact (e ⟨a,ha⟩).property

theorem realExtension_inverse {U V : Set ℝ} (e : U ≃ V) :
    ∀ a ∈ U, realExtension e.symm (realExtension e a) = a := by
  intro a ha
  rw [realExtension_on_domain e ⟨a,ha⟩,realExtension_on_domain e.symm (e ⟨a,ha⟩),Equiv.symm_apply_apply]

open LCTR.CoreValueJetChanges LCTR.CoreDifferentialCovariance

noncomputable def timeChangeOfEquiv {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (V : Set E) (U W : Set ℝ) (e : U ≃ W)
    (ou : IsOpen U) (ow : IsOpen W)
    (fs : ContDiffOn ℝ k (realExtension e) U) (gs : ContDiffOn ℝ k (realExtension e.symm) W)
    (J K : ℝ → Domain k V → Domain k V)
    (hj : ∀ a (ha : a ∈ U), LCTR.CoreTimeJetChanges.Acts k a (realExtension e a) V
      (realExtension e.symm) (realExtension_inverse e a ha) (J a))
    (hk : ∀ a (_ha : a ∈ U), LCTR.CoreTimeJetChanges.Acts k (realExtension e a) a V
      (realExtension e) rfl (K (realExtension e a))) : TimeChange k V U W where
  forward := realExtension e
  backward := realExtension e.symm
  source_open := ou
  target_open := ow
  forward_maps := realExtension_maps e
  backward_maps := realExtension_maps e.symm
  forward_smooth := fs
  backward_smooth := gs
  left_inverse := realExtension_inverse e
  right_inverse := realExtension_inverse e.symm
  lift := J
  inverse_lift := K
  lift_action := hj
  inverse_action := hk

theorem base_eq_coordinate_equiv {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} {V : Set E} {U W : Set ℝ} (c : TimeChange k V U W) (e : U ≃ W)
    (he : c.forward = realExtension e) (a : U) : c.base a = e a := by
  apply Subtype.ext
  change c.forward a.val = (e a).val
  rw [he,realExtension_on_domain]

theorem chart_link_for_time_images {S : Type u} (f g : S → ℝ)
    (kernel : ∀ x y, f x = f y ↔ g x = g y) (ord : ∀ x y, f x < f y ↔ g x < g y)
    (D : Set (range f)) (E : Set (range g)) (U V : Set ℝ) (c : D ≃ U) (d : E ≃ V)
    (a : coordinateDomain (imageOrderIso f g kernel ord).toEquiv D E U c) :
    imageOrderIso f g kernel ord
      ((coordinateEquiv (imageOrderIso f g kernel ord).toEquiv D E U c).symm a).val.val =
      ((coordinateEquiv (imageOrderIso f g kernel ord).symm.toEquiv E D V d).symm
        (chartEquiv (imageOrderIso f g kernel ord).toEquiv D E U V c d a)).val.val :=
  chart_commutes (imageOrderIso f g kernel ord).toEquiv D E U V c d a

theorem restricted_relation_image {A : Type u} {B : Type v} (e : A ≃ B)
    (R : Set A) (S : Set B) (cov : ∀ a, a ∈ R ↔ e a ∈ S) : e '' R = S :=
  LCTR.CoreValueJetChanges.relation_image _ _ e e.surjective R S cov

theorem ambient_restriction_image {A : Type u} {B : Type v} (U : Set A) (V : Set B)
    (e : U ≃ V) (R : Set A) (S : Set B)
    (cov : ∀ a : U, a.val ∈ R ↔ (e a).val ∈ S) :
    (fun a : U => (e a).val) '' {a : U | a.val ∈ R} = S ∩ V := by
  ext b
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨(cov a).mp ha,(e a).property⟩
  · rintro ⟨hb,hv⟩
    obtain ⟨a,he⟩ := e.surjective ⟨b,hv⟩
    have he' : (e a).val = b := congrArg Subtype.val he
    refine ⟨a,(cov a).mpr ?_,he'⟩
    rw [he']
    exact hb

end LCTR.CoreChartOverlaps
