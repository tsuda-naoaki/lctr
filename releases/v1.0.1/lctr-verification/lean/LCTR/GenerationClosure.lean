import Std




namespace LCTR.GenerationClosure

abbrev Family (E : Type u) := E → Prop

structure Rule (E : Type u) where
  premises : Family E
  conclusion : E

def Closed (rules : Family (Rule E)) (s : Family E) : Prop :=
  ∀ r, rules r → (∀ x, r.premises x → s x) → s r.conclusion

def Closure (rules : Family (Rule E)) (input : Family E) : Family E :=
  fun y => ∀ s, (∀ x, input x → s x) → Closed rules s → s y

theorem input_mem (rules : Family (Rule E)) (input : Family E)
    {x : E} (hx : input x) : Closure rules input x := by
  intro s hs _
  exact hs x hx

theorem least_closed (rules : Family (Rule E)) (input s : Family E)
    (hi : ∀ x, input x → s x) (hc : Closed rules s) :
    ∀ x, Closure rules input x → s x := by
  intro x hx
  exact hx s hi hc

theorem closure_closed (rules : Family (Rule E)) (input : Family E) :
    Closed rules (Closure rules input) := by
  intro r hr hp s hi hc
  exact hc r hr (fun x hx => hp x hx s hi hc)

theorem inputs_monotone (rules : Family (Rule E)) (input larger : Family E)
    (h : ∀ x, input x → larger x) :
    ∀ x, Closure rules input x → Closure rules larger x := by
  intro x hx s hs hc
  exact hx s (fun y hy => hs y (h y hy)) hc

theorem rules_monotone (rules larger : Family (Rule E)) (input : Family E)
    (h : ∀ r, rules r → larger r) :
    ∀ x, Closure rules input x → Closure larger input x := by
  intro x hx s hi hc
  exact hx s hi (fun r hr hp => hc r (h r hr) hp)

theorem gate_blocks_unsupplied_outputs (rules : Family (Rule E))
    (input outputs : Family E) (gate : E)
    (gate_required : ∀ r, rules r → r.premises gate)
    (gate_absent : ¬ input gate)
    (outputs_absent : ∀ y, outputs y → ¬ input y) :
    ∀ y, outputs y → ¬ Closure rules input y := by
  let s : Family E := fun x => x ≠ gate ∧ ¬ outputs x
  have hi : ∀ x, input x → s x := by
    intro x hx
    constructor
    · intro eq
      subst x
      exact gate_absent hx
    · intro ho
      exact outputs_absent x ho hx
  have hc : Closed rules s := by
    intro r hr hp
    have hg := hp gate (gate_required r hr)
    exact False.elim (hg.1 rfl)
  intro y hy hyc
  exact (hyc s hi hc).2 hy

theorem supplied_input_is_never_blocked (rules : Family (Rule E))
    (input : Family E) {x : E} (hx : input x) :
    ¬ (¬ Closure rules input x) := by
  intro h
  exact h (input_mem rules input hx)




def LayerRules (premises outputs : Fin 4 → Family E) : Family (Rule E) :=
  fun r => ∃ k, r.premises = premises k ∧ outputs k r.conclusion

theorem canonical_four_layer_failure
    (premises outputs : Fin 4 → Family E) (input : Family E) (gate : E)
    (gate_required : ∀ k, premises k gate)
    (gate_absent : ¬ input gate)
    (outputs_absent : ∀ k y, outputs k y → ¬ input y) :
    ∀ k y, outputs k y → ¬ Closure (LayerRules premises outputs) input y := by
  have h := gate_blocks_unsupplied_outputs (LayerRules premises outputs)
    input (fun y => ∃ k, outputs k y) gate
    (by
      intro r hr
      obtain ⟨k, hp, _⟩ := hr
      rw [hp]
      exact gate_required k)
    gate_absent
    (by
      intro y hy
      obtain ⟨k, hk⟩ := hy
      exact outputs_absent k y hk)
  intro k y hy
  exact h y ⟨k, hy⟩

#print axioms input_mem
#print axioms least_closed
#print axioms closure_closed
#print axioms inputs_monotone
#print axioms rules_monotone
#print axioms gate_blocks_unsupplied_outputs
#print axioms supplied_input_is_never_blocked
#print axioms canonical_four_layer_failure

end LCTR.GenerationClosure
