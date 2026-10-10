import Mathlib.Data.Real.Basic
import LCTR.TransitiveIncomparabilityQuotientCore
import LCTR.ImageInverseConstruction

namespace LCTR.OrderEmbeddingBridgeV1

open LCTR.TransitiveIncomparabilityQuotientCore

universe u

def incSetoid
    {S : Type u}
    (strict : S → S → Prop)
    (irreflexive : ∀ x, ¬ strict x x)
    (incTransitive :
      ∀ {x y z}, Inc strict x y → Inc strict y z → Inc strict x z) :
    Setoid S where
  r := Inc strict
  iseqv :=
    ⟨(fun x => ⟨irreflexive x, irreflexive x⟩),
      (fun h => inc_symmetric strict h),
      (fun hxy hyz => incTransitive hxy hyz)⟩

abbrev IncQuotient
    {S : Type u}
    (strict : S → S → Prop)
    (irreflexive : ∀ x, ¬ strict x x)
    (incTransitive :
      ∀ {x y z}, Inc strict x y → Inc strict y z → Inc strict x z) :=
  Quotient (incSetoid strict irreflexive incTransitive)

def proj
    {S : Type u}
    (strict : S → S → Prop)
    (irreflexive : ∀ x, ¬ strict x x)
    (incTransitive :
      ∀ {x y z}, Inc strict x y → Inc strict y z → Inc strict x z)
    (x : S) :
    IncQuotient strict irreflexive incTransitive :=
  Quotient.mk _ x

theorem proj_surjective
    {S : Type u}
    (strict : S → S → Prop)
    (irreflexive : ∀ x, ¬ strict x x)
    (incTransitive :
      ∀ {x y z}, Inc strict x y → Inc strict y z → Inc strict x z) :
    Function.Surjective (proj strict irreflexive incTransitive) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  exact ⟨x, rfl⟩

theorem proj_eq_iff_inc
    {S : Type u}
    (strict : S → S → Prop)
    (irreflexive : ∀ x, ¬ strict x x)
    (incTransitive :
      ∀ {x y z}, Inc strict x y → Inc strict y z → Inc strict x z)
    (x y : S) :
    proj strict irreflexive incTransitive x =
        proj strict irreflexive incTransitive y ↔
      Inc strict x y := by
  change Quotient.mk (incSetoid strict irreflexive incTransitive) x =
      Quotient.mk (incSetoid strict irreflexive incTransitive) y ↔
    Inc strict x y
  constructor
  · exact Quotient.exact
  · intro h
    exact Quotient.sound (s := incSetoid strict irreflexive incTransitive) h

def quotientLt
    {S : Type u}
    (strict : S → S → Prop)
    (irreflexive : ∀ x, ¬ strict x x)
    (incTransitive :
      ∀ {x y z}, Inc strict x y → Inc strict y z → Inc strict x z)
    (q0 q1 : IncQuotient strict irreflexive incTransitive) : Prop :=
  ∃ x y : S,
    proj strict irreflexive incTransitive x = q0 ∧
    proj strict irreflexive incTransitive y = q1 ∧
    strict x y

theorem quotientLt_proj_iff
    {S : Type u}
    (strict : S → S → Prop)
    (irreflexive : ∀ x, ¬ strict x x)
    (transitive : ∀ {x y z}, strict x y → strict y z → strict x z)
    (incTransitive :
      ∀ {x y z}, Inc strict x y → Inc strict y z → Inc strict x z)
    (x y : S) :
    quotientLt strict irreflexive incTransitive
        (proj strict irreflexive incTransitive x)
        (proj strict irreflexive incTransitive y) ↔
      strict x y := by
  constructor
  · rintro ⟨x', y', hx', hy', hxy⟩
    have hxx' : Inc strict x' x :=
      (proj_eq_iff_inc strict irreflexive incTransitive x' x).mp hx'
    have hyy' : Inc strict y' y :=
      (proj_eq_iff_inc strict irreflexive incTransitive y' y).mp hy'
    exact
      (representative_invariance strict transitive incTransitive
        hxx' hyy').mp hxy
  · intro hxy
    exact ⟨x, y, rfl, rfl, hxy⟩

theorem quotient_strict_linear_components
    {S : Type u}
    (strict : S → S → Prop)
    (irreflexive : ∀ x, ¬ strict x x)
    (transitive : ∀ {x y z}, strict x y → strict y z → strict x z)
    (incTransitive :
      ∀ {x y z}, Inc strict x y → Inc strict y z → Inc strict x z) :
    (∀ q, ¬ quotientLt strict irreflexive incTransitive q q) ∧
    (∀ {q0 q1 q2},
      quotientLt strict irreflexive incTransitive q0 q1 →
      quotientLt strict irreflexive incTransitive q1 q2 →
      quotientLt strict irreflexive incTransitive q0 q2) ∧
    (∀ {q0 q1},
      q0 ≠ q1 →
      quotientLt strict irreflexive incTransitive q0 q1 ∨
      quotientLt strict irreflexive incTransitive q1 q0) := by
  exact projected_order_is_strict_linear
    strict
    (quotientLt strict irreflexive incTransitive)
    (proj strict irreflexive incTransitive)
    irreflexive
    transitive
    (proj_surjective strict irreflexive incTransitive)
    (proj_eq_iff_inc strict irreflexive incTransitive)
    (quotientLt_proj_iff strict irreflexive transitive incTransitive)

theorem real_order_iff_map_injective
    {S : Type u}
    (strict : S → S → Prop)
    (irreflexive : ∀ x, ¬ strict x x)
    (transitive : ∀ {x y z}, strict x y → strict y z → strict x z)
    (incTransitive :
      ∀ {x y z}, Inc strict x y → Inc strict y z → Inc strict x z)
    (rho : IncQuotient strict irreflexive incTransitive → ℝ)
    (orderIff :
      ∀ q0 q1,
        quotientLt strict irreflexive incTransitive q0 q1 ↔
          rho q0 < rho q1) :
    Function.Injective rho := by
  intro q0 q1 hEq
  by_contra hNe
  have hCmp :=
    (quotient_strict_linear_components
      strict irreflexive transitive incTransitive).2.2 hNe
  cases hCmp with
  | inl h01 =>
      have hlt : rho q0 < rho q1 := (orderIff q0 q1).mp h01
      rw [hEq] at hlt
      exact (lt_irrefl _ hlt)
  | inr h10 =>
      have hlt : rho q1 < rho q0 := (orderIff q1 q0).mp h10
      rw [hEq] at hlt
      exact (lt_irrefl _ hlt)

theorem real_embedding_image_inverse_compositions
    {S : Type u}
    (strict : S → S → Prop)
    (irreflexive : ∀ x, ¬ strict x x)
    (transitive : ∀ {x y z}, strict x y → strict y z → strict x z)
    (incTransitive :
      ∀ {x y z}, Inc strict x y → Inc strict y z → Inc strict x z)
    (rho : IncQuotient strict irreflexive incTransitive → ℝ)
    (orderIff :
      ∀ q0 q1,
        quotientLt strict irreflexive incTransitive q0 q1 ↔
          rho q0 < rho q1) :
    (∀ q,
      LCTR.ImageInverseConstruction.inverse rho ⟨rho q, ⟨q, rfl⟩⟩ = q) ∧
    (∀ t : LCTR.ImageInverseConstruction.Image rho,
      rho (LCTR.ImageInverseConstruction.inverse rho t) = t.val) := by
  have hInjective :=
    real_order_iff_map_injective
      strict irreflexive transitive incTransitive rho orderIff
  exact
    ⟨LCTR.ImageInverseConstruction.inverse_left rho hInjective,
      LCTR.ImageInverseConstruction.inverse_right rho⟩

theorem real_embedding_image_inverse_characterization
    {S : Type u}
    (strict : S → S → Prop)
    (irreflexive : ∀ x, ¬ strict x x)
    (transitive : ∀ {x y z}, strict x y → strict y z → strict x z)
    (incTransitive :
      ∀ {x y z}, Inc strict x y → Inc strict y z → Inc strict x z)
    (rho : IncQuotient strict irreflexive incTransitive → ℝ)
    (orderIff :
      ∀ q0 q1,
        quotientLt strict irreflexive incTransitive q0 q1 ↔
          rho q0 < rho q1)
    (t : LCTR.ImageInverseConstruction.Image rho)
    (q : IncQuotient strict irreflexive incTransitive) :
    LCTR.ImageInverseConstruction.inverse rho t = q ↔ rho q = t.val := by
  exact LCTR.ImageInverseConstruction.inverse_characterization rho
    (real_order_iff_map_injective
      strict irreflexive transitive incTransitive rho orderIff)
    t q

#print axioms incSetoid
#print axioms proj_surjective
#print axioms proj_eq_iff_inc
#print axioms quotientLt_proj_iff
#print axioms quotient_strict_linear_components
#print axioms real_order_iff_map_injective
#print axioms real_embedding_image_inverse_compositions
#print axioms real_embedding_image_inverse_characterization

end LCTR.OrderEmbeddingBridgeV1
