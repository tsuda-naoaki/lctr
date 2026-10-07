import CoreNativeDifferentialFamily
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Logic.Equiv.Fin.Basic

namespace LCTR.CoreJointCoordinateFlattening
set_option autoImplicit false
open Set LCTR.CoreValueJetChanges
variable (dim : Fin 2 → ℕ)
abbrev Joint := (s : Fin 2) → Fin (dim s) → ℝ
abbrev Flat := Fin (dim 0 + dim 1) → ℝ

noncomputable def flatten : Joint dim ≃L[ℝ] Flat dim :=
  (ContinuousLinearEquiv.piFinTwo ℝ (fun s : Fin 2 => Fin (dim s) → ℝ)).trans
    ((ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin (dim 0)) (Fin (dim 1))
      (fun _ => ℝ)).symm.trans
      (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (dim 0 + dim 1) => ℝ) finSumFinEquiv))

theorem flatten_inverse (v : Joint dim) : (flatten dim).symm (flatten dim v) = v :=
  (flatten dim).symm_apply_apply v
theorem unflatten_inverse (v : Flat dim) : flatten dim ((flatten dim).symm v) = v :=
  (flatten dim).apply_symm_apply v

theorem smoothness_preserved (k : ℕ) (f : ℝ → Joint dim) (U : Set ℝ) :
    ContDiffOn ℝ k ((flatten dim) ∘ f) U ↔ ContDiffOn ℝ k f U :=
  (flatten dim).comp_contDiffOn_iff

theorem derivatives_preserved (n : ℕ) (f : ℝ → Joint dim) (theta : ℝ) :
    iteratedDeriv n ((flatten dim) ∘ f) theta = flatten dim (iteratedDeriv n f theta) := by
  unfold iteratedDeriv
  rw [(flatten dim).iteratedFDeriv_comp_left]
  rfl

variable (k : ℕ) (V : Set (Joint dim))
def flatRegion : Set (Flat dim) := flatten dim '' V

noncomputable def jetEquiv : Domain k V ≃ Domain k (flatRegion dim V) where
  toFun j := ⟨fun n => flatten dim (j.val n),⟨j.val 0,j.property,rfl⟩⟩
  invFun j := ⟨fun n => (flatten dim).symm (j.val n),by
    obtain ⟨v,hv,hj⟩ := j.property
    change (flatten dim).symm (j.val 0) ∈ V
    rw [← hj,(flatten dim).symm_apply_apply]
    exact hv⟩
  left_inv j := by
    apply Subtype.ext
    funext n
    exact (flatten dim).symm_apply_apply (j.val n)
  right_inv j := by
    apply Subtype.ext
    funext n
    exact (flatten dim).apply_symm_apply (j.val n)

theorem jet_flatten_derivative_order (j : Domain k V) (n : Fin (k+1)) :
    (jetEquiv dim k V j).val n = flatten dim (j.val n) := rfl

theorem flatten_actual_jet (theta : ℝ) (f : ℝ → Joint dim) (h : f theta ∈ V) :
    jetEquiv dim k V (jetAt k theta f V h) =
      jetAt k theta ((flatten dim) ∘ f) (flatRegion dim V) ⟨f theta,h,rfl⟩ := by
  apply Subtype.ext
  funext n
  exact (derivatives_preserved dim n.val f theta).symm

noncomputable def ambientEquiv (U : Set ℝ) :
    (U × Domain k V) ≃ (U × Domain k (flatRegion dim V)) :=
  Equiv.prodCongr (Equiv.refl U) (jetEquiv dim k V)

theorem numeric_time_preserved (U : Set ℝ) (p : U × Domain k V) :
    (ambientEquiv dim k V U p).1 = p.1 := rfl

theorem flattened_relation_membership (U : Set ℝ) (R : Set (U × Domain k V))
    (p : U × Domain k V) :
    ambientEquiv dim k V U p ∈ (ambientEquiv dim k V U '' R) ↔ p ∈ R :=
  (ambientEquiv dim k V U).injective.mem_set_image

theorem flattened_relation_recovered (U : Set ℝ) (R : Set (U × Domain k V)) :
    (ambientEquiv dim k V U).symm '' (ambientEquiv dim k V U '' R) = R := by
  ext p
  simp only [Set.mem_image]
  constructor
  · rintro ⟨q,⟨r,hr,he⟩,hp⟩
    rw [← he,(ambientEquiv dim k V U).symm_apply_apply] at hp
    exact hp ▸ hr
  · intro hp
    exact ⟨ambientEquiv dim k V U p,⟨p,hp,rfl⟩,(ambientEquiv dim k V U).symm_apply_apply p⟩

end LCTR.CoreJointCoordinateFlattening
