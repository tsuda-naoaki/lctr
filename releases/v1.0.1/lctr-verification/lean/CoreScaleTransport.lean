import CoreContinuumBoundary
import Mathlib.Logic.Equiv.Set
import Mathlib.Order.Hom.Basic

namespace LCTR.CoreScaleTransport
set_option autoImplicit false
open Set LCTR.CoreContinuumBoundary
open scoped ENNReal
universe u v w z

theorem image_of_iff {A : Type u} {B : Type v} (c : A ≃ B) (P : Set A) (Q : Set B)
    (h : ∀ a, a ∈ P ↔ c a ∈ Q) : c '' P = Q := by
  ext b
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact (h a).mp ha
  · intro hb
    obtain ⟨a,rfl⟩ := c.surjective b
    exact ⟨a,(h a).mpr hb,rfl⟩

theorem validity_under_data_iso {I : Type u} {J : Type v}
    (c : I ≃ J) (v : ℝ≥0∞ ≃o ℝ≥0∞) (d0 e0 : I → ℝ≥0∞) (d1 e1 : J → ℝ≥0∞)
    (hd : ∀ i, d1 (c i)=v (d0 i)) (he : ∀ i, e1 (c i)=v (e0 i)) :
    Valid d0 e0 ↔ Valid d1 e1 := by
  constructor
  · intro h j
    obtain ⟨i,rfl⟩ := c.surjective j
    rw [hd,he]
    exact v.monotone (h i)
  · intro h i
    have hi := h (c i)
    rw [hd,he] at hi
    exact v.le_iff_le.mp hi

theorem saturation_image {I : Type u} {J : Type v}
    (c : I ≃ J) (v : ℝ≥0∞ ≃o ℝ≥0∞) (d0 e0 : I → ℝ≥0∞) (d1 e1 : J → ℝ≥0∞)
    (hd : ∀ i, d1 (c i)=v (d0 i)) (he : ∀ i, e1 (c i)=v (e0 i)) :
    c '' Saturated d0 e0 = Saturated d1 e1 := by
  apply image_of_iff
  intro i
  simp only [Saturated,mem_ofPred_eq,margin_zero,hd,he,v.injective.eq_iff]

theorem exceeded_image {I : Type u} {J : Type v}
    (c : I ≃ J) (v : ℝ≥0∞ ≃o ℝ≥0∞) (d0 e0 : I → ℝ≥0∞) (d1 e1 : J → ℝ≥0∞)
    (hd : ∀ i, d1 (c i)=v (d0 i)) (he : ∀ i, e1 (c i)=v (e0 i)) :
    c '' Exceeded d0 e0 = Exceeded d1 e1 := by
  apply image_of_iff
  intro i
  simp only [Exceeded,mem_ofPred_eq,excess_positive,hd,he,v.lt_iff_lt]

theorem initial_image {Λ : Type u} {M : Type v} [Preorder Λ] [Preorder M]
    (e : Λ ≃o M) (V : Set Λ) (hv : Initial V) : Initial (e '' V) := by
  rintro x y hxy ⟨a,ha,rfl⟩
  have hxa : e.symm x ≤ a := e.le_iff_le.mp (by simpa only [e.apply_symm_apply] using hxy)
  exact ⟨e.symm x,hv hxa ha,e.apply_symm_apply x⟩

theorem maximal_initial_image {Λ : Type u} {M : Type v} [Preorder Λ] [Preorder M]
    (e : Λ ≃o M) (V : Set Λ) : e '' MaximalInitial V = MaximalInitial (e '' V) := by
  apply Set.Subset.antisymm
  · apply (maximal_initial_greatest (e '' V)).2
    exact ⟨Set.image_mono (maximal_initial_greatest V).1.1,
      initial_image e _ (maximal_initial_greatest V).1.2⟩
  · intro y hy
    have valid : e ⁻¹' MaximalInitial (e '' V) ⊆ V := by
      intro x hx
      obtain ⟨a,ha,he⟩ := (maximal_initial_greatest (e '' V)).1.1 hx
      exact e.injective he ▸ ha
    have init : Initial (e ⁻¹' MaximalInitial (e '' V)) := by
      intro x z hxz hz
      exact (maximal_initial_greatest (e '' V)).1.2 (e.monotone hxz) hz
    have subset := (maximal_initial_greatest V).2 _ ⟨valid,init⟩
    refine ⟨e.symm y,subset ?_,e.apply_symm_apply y⟩
    change e (e.symm y) ∈ MaximalInitial (e '' V)
    simpa only [e.apply_symm_apply] using hy

theorem least_image_iff {Λ : Type u} {M : Type v} [Preorder Λ] [Preorder M]
    (e : Λ ≃o M) (V : Set Λ) (a : Λ) : IsLeast V a ↔ IsLeast (e '' V) (e a) := by
  constructor
  · rintro ⟨ha,hmin⟩
    refine ⟨⟨a,ha,rfl⟩,?_⟩
    rintro _ ⟨x,hx,rfl⟩
    exact e.monotone (hmin hx)
  · rintro ⟨⟨b,hb,he⟩,hmin⟩
    have hba : b=a := e.injective he
    refine ⟨hba ▸ hb,?_⟩
    intro x hx
    exact e.le_iff_le.mp (hmin ⟨x,hx,rfl⟩)

theorem least_exists_iff {Λ : Type u} {M : Type v} [Preorder Λ] [Preorder M]
    (e : Λ ≃o M) (V : Set Λ) : (∃ a, IsLeast V a) ↔ ∃ b, IsLeast (e '' V) b := by
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨e a,(least_image_iff e V a).mp ha⟩
  · rintro ⟨b,hb⟩
    obtain ⟨a,rfl⟩ := e.surjective b
    exact ⟨a,(least_image_iff e V a).mpr hb⟩

theorem scale_domain_and_boundary_transport
    {I : Type u} {J : Type v} {Λ : Type w} {M : Type z} [LinearOrder Λ] [LinearOrder M]
    (c : I ≃ J) (e : Λ ≃o M) (v : ℝ≥0∞ ≃o ℝ≥0∞)
    (d0 : Λ → I → ℝ≥0∞) (d1 : M → J → ℝ≥0∞) (eps0 : I → ℝ≥0∞) (eps1 : J → ℝ≥0∞)
    (hd : ∀ a i, d1 (e a) (c i)=v (d0 a i)) (he : ∀ i, eps1 (c i)=v (eps0 i)) :
    e '' MaximalInitial {a | Valid (d0 a) eps0} = MaximalInitial {b | Valid (d1 b) eps1} ∧
    (∀ a, IsLeast {x | ¬ Valid (d0 x) eps0} a ↔
      IsLeast {y | ¬ Valid (d1 y) eps1} (e a)) ∧
    (∀ a, c '' Exceeded (d0 a) eps0 = Exceeded (d1 (e a)) eps1) := by
  have hv : ∀ a, Valid (d0 a) eps0 ↔ Valid (d1 (e a)) eps1 :=
    fun a => validity_under_data_iso c v (d0 a) eps0 (d1 (e a)) eps1 (hd a) he
  have vd := image_of_iff e.toEquiv {a | Valid (d0 a) eps0} {b | Valid (d1 b) eps1} hv
  have fd := image_of_iff e.toEquiv {a | ¬ Valid (d0 a) eps0} {b | ¬ Valid (d1 b) eps1}
    (fun a => not_congr (hv a))
  refine ⟨?_,?_,fun a => exceeded_image c v (d0 a) eps0 (d1 (e a)) eps1 (hd a) he⟩
  · rw [maximal_initial_image]
    exact congrArg MaximalInitial vd
  · intro a
    rw [← fd]
    exact least_image_iff e _ a

end LCTR.CoreScaleTransport
