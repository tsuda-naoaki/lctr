namespace LCTR.TransitiveIncomparabilityQuotientCore

universe u v

def Inc {S : Type u} (strict : S → S → Prop) (x y : S) : Prop :=
  ¬ strict x y ∧ ¬ strict y x

theorem inc_symmetric
    {S : Type u}
    (strict : S → S → Prop)
    {x y : S}
    (h : Inc strict x y) :
    Inc strict y x := by
  exact ⟨h.2, h.1⟩

theorem strict_transfer
    {S : Type u}
    (strict : S → S → Prop)
    (transitive : ∀ {x y z}, strict x y → strict y z → strict x z)
    (incTransitive :
      ∀ {x y z}, Inc strict x y → Inc strict y z → Inc strict x z)
    {x x' y y' : S}
    (hxx' : Inc strict x x')
    (hyy' : Inc strict y y')
    (hxy : strict x y) :
    strict x' y' := by
  have hx'y : strict x' y := by
    by_cases hx'y : strict x' y
    · exact hx'y
    · by_cases hyx' : strict y x'
      · exact False.elim (hxx'.1 (transitive hxy hyx'))
      · have hx'yInc : Inc strict x' y := ⟨hx'y, hyx'⟩
        exact False.elim ((incTransitive hxx' hx'yInc).1 hxy)
  by_cases hx'y' : strict x' y'
  · exact hx'y'
  · by_cases hy'x' : strict y' x'
    · exact False.elim (hyy'.2 (transitive hy'x' hx'y))
    · have hx'y'Inc : Inc strict x' y' := ⟨hx'y', hy'x'⟩
      have hy'yInc : Inc strict y' y := inc_symmetric strict hyy'
      exact False.elim ((incTransitive hx'y'Inc hy'yInc).1 hx'y)

theorem representative_invariance
    {S : Type u}
    (strict : S → S → Prop)
    (transitive : ∀ {x y z}, strict x y → strict y z → strict x z)
    (incTransitive :
      ∀ {x y z}, Inc strict x y → Inc strict y z → Inc strict x z)
    {x x' y y' : S}
    (hxx' : Inc strict x x')
    (hyy' : Inc strict y y') :
    strict x y ↔ strict x' y' := by
  constructor
  · exact strict_transfer strict transitive incTransitive hxx' hyy'
  · exact strict_transfer strict transitive incTransitive
      (inc_symmetric strict hxx') (inc_symmetric strict hyy')

theorem projected_order_is_strict_linear
    {S : Type u}
    {Q : Type v}
    (strict : S → S → Prop)
    (qLt : Q → Q → Prop)
    (proj : S → Q)
    (irreflexive : ∀ x, ¬ strict x x)
    (transitive : ∀ {x y z}, strict x y → strict y z → strict x z)
    (surjective : Function.Surjective proj)
    (eqCriterion : ∀ x y, proj x = proj y ↔ Inc strict x y)
    (orderCriterion : ∀ x y, qLt (proj x) (proj y) ↔ strict x y) :
    (∀ q, ¬ qLt q q) ∧
      (∀ {q0 q1 q2}, qLt q0 q1 → qLt q1 q2 → qLt q0 q2) ∧
      (∀ {q0 q1}, q0 ≠ q1 → qLt q0 q1 ∨ qLt q1 q0) := by
  constructor
  · intro q
    obtain ⟨x, rfl⟩ := surjective q
    intro h
    exact irreflexive x ((orderCriterion x x).mp h)
  constructor
  · intro q0 q1 q2 h01 h12
    obtain ⟨x0, rfl⟩ := surjective q0
    obtain ⟨x1, rfl⟩ := surjective q1
    obtain ⟨x2, rfl⟩ := surjective q2
    exact (orderCriterion x0 x2).mpr
      (transitive ((orderCriterion x0 x1).mp h01)
        ((orderCriterion x1 x2).mp h12))
  · intro q0 q1 hNe
    obtain ⟨x0, rfl⟩ := surjective q0
    obtain ⟨x1, rfl⟩ := surjective q1
    by_cases h01 : strict x0 x1
    · exact Or.inl ((orderCriterion x0 x1).mpr h01)
    · by_cases h10 : strict x1 x0
      · exact Or.inr ((orderCriterion x1 x0).mpr h10)
      · exact False.elim (hNe ((eqCriterion x0 x1).mpr ⟨h01, h10⟩))

theorem projection_contract
    {S : Type u}
    {Q : Type v}
    (strict : S → S → Prop)
    (qLt : Q → Q → Prop)
    (proj : S → Q)
    (surjective : Function.Surjective proj)
    (eqCriterion : ∀ x y, proj x = proj y ↔ Inc strict x y)
    (orderCriterion : ∀ x y, qLt (proj x) (proj y) ↔ strict x y) :
    Function.Surjective proj ∧
      (∀ x y, proj x = proj y ↔ Inc strict x y) ∧
      (∀ x y, qLt (proj x) (proj y) ↔ strict x y) := by
  exact ⟨surjective, eqCriterion, orderCriterion⟩

end LCTR.TransitiveIncomparabilityQuotientCore
