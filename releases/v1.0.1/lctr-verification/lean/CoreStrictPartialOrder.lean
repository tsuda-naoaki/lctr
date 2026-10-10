namespace LCTR.CoreStrictPartialOrder

universe u
set_option autoImplicit false

theorem strict_part_contract {S : Sort u} (r : S → S → Prop)
    (partial_order : (∀ x, r x x) ∧
      (∀ {x y z}, r x y → r y z → r x z) ∧
      (∀ {x y}, r x y → r y x → x = y)) :
    (∀ x, ¬ (r x x ∧ x ≠ x)) ∧
    (∀ {x y z}, (r x y ∧ x ≠ y) →
      (r y z ∧ y ≠ z) → (r x z ∧ x ≠ z)) := by
  constructor
  · intro x hx
    exact hx.2 rfl
  · intro x y z hxy hyz
    refine ⟨partial_order.2.1 hxy.1 hyz.1, ?_⟩
    intro hxz
    have hyx : r y x := hxz.symm ▸ hyz.1
    exact hxy.2 (partial_order.2.2 hxy.1 hyx)

#print axioms strict_part_contract
end LCTR.CoreStrictPartialOrder
