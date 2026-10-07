import LCTR.SelectedInputEvaluation
import Mathlib.Data.Int.Basic

namespace LCTR.CoreEvaluationSMTBridge
open LCTR.SelectedInputEvaluation

def encode : State → Int
  | .unformed => 0
  | .unevaluable => 1
  | .sat => 2
  | .failed => 3

def smtState (f e p c : Bool) : Int :=
  if !(f && p) then 0 else if !e then 1 else if c then 2 else 3
def wrongPriorState (f e c : Bool) : State :=
  if !f then .unformed else if !e then .unevaluable else if c then .sat else .failed
def wrongPriorCode (f e c : Bool) : Int :=
  if !f then 0 else if !e then 1 else if c then 2 else 3
def wrongOrderState (f e p c : Bool) : State :=
  if !e then .unevaluable else if !(f && p) then .unformed else if c then .sat else .failed
def wrongOrderCode (f e p c : Bool) : Int :=
  if !e then 1 else if !(f && p) then 0 else if c then 2 else 3

theorem encode_injective : Function.Injective encode := by
  intro x y h
  cases x <;> cases y <;> simp_all [encode]
theorem encode_eq_iff (x y : State) : encode x = encode y ↔ x = y :=
  encode_injective.eq_iff
theorem encode_image (n : Int) :
    (∃ s : State, encode s = n) ↔ n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by
  constructor
  · rintro ⟨s, rfl⟩
    cases s <;> simp [encode]
  · intro h
    rcases h with rfl | rfl | rfl | rfl
    · exact ⟨.unformed, rfl⟩
    · exact ⟨.unevaluable, rfl⟩
    · exact ⟨.sat, rfl⟩
    · exact ⟨.failed, rfl⟩
theorem state_commutes (f e p c : Bool) : encode (state f e p c) = smtState f e p c := by
  cases f <;> cases e <;> cases p <;> cases c <;> rfl

theorem failed_iff_transfer (f e p c : Bool) :
    ((state f e p c = .failed) ↔ (f = true ∧ e = true ∧ p = true ∧ c = false)) ↔
    ((smtState f e p c = 3) ↔ (f = true ∧ e = true ∧ p = true ∧ c = false)) := by
  cases f <;> cases e <;> cases p <;> cases c <;> decide
theorem sat_iff_transfer (f e p c : Bool) :
    ((state f e p c = .sat) ↔ (f = true ∧ e = true ∧ p = true ∧ c = true)) ↔
    ((smtState f e p c = 2) ↔ (f = true ∧ e = true ∧ p = true ∧ c = true)) := by
  cases f <;> cases e <;> cases p <;> cases c <;> decide
theorem missing_formation_transfer (f e p c : Bool) :
    (f = false → state f e p c = .unformed) ↔ (f = false → smtState f e p c = 0) := by
  cases f <;> cases e <;> cases p <;> cases c <;> decide
theorem upstream_nonsat_transfer (f e p c : Bool) :
    (p = false → state f e p c = .unformed) ↔ (p = false → smtState f e p c = 0) := by
  cases f <;> cases e <;> cases p <;> cases c <;> decide
theorem unevaluable_iff_transfer (f e p c : Bool) :
    ((state f e p c = .unevaluable) ↔ (f = true ∧ p = true ∧ e = false)) ↔
    ((smtState f e p c = 1) ↔ (f = true ∧ p = true ∧ e = false)) := by
  cases f <;> cases e <;> cases p <;> cases c <;> decide
theorem unformed_iff_transfer (f e p c : Bool) :
    ((state f e p c = .unformed) ↔ ¬ (f = true ∧ p = true)) ↔
    ((smtState f e p c = 0) ↔ ¬ (f = true ∧ p = true)) := by
  cases f <;> cases e <;> cases p <;> cases c <;> decide
theorem wrong_prior_transfer (f e p c : Bool) :
    (state f e p c = wrongPriorState f e c) ↔ (smtState f e p c = wrongPriorCode f e c) := by
  cases f <;> cases e <;> cases p <;> cases c <;> decide
theorem wrong_order_transfer (f e p c : Bool) :
    (state f e p c = wrongOrderState f e p c) ↔ (smtState f e p c = wrongOrderCode f e p c) := by
  cases f <;> cases e <;> cases p <;> cases c <;> decide
theorem reject_ignored_predecessor :
    state true true false false ≠ wrongPriorState true true false := by decide
theorem reject_early_evaluation :
    state false false true true ≠ wrongOrderState false false true true := by decide

#print axioms encode_injective
#print axioms encode_eq_iff
#print axioms encode_image
#print axioms state_commutes
#print axioms failed_iff_transfer
#print axioms sat_iff_transfer
#print axioms missing_formation_transfer
#print axioms upstream_nonsat_transfer
#print axioms unevaluable_iff_transfer
#print axioms unformed_iff_transfer
#print axioms wrong_prior_transfer
#print axioms wrong_order_transfer
#print axioms reject_ignored_predecessor
#print axioms reject_early_evaluation
end LCTR.CoreEvaluationSMTBridge
