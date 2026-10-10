import Mathlib.Data.Int.Basic
import Lean.Elab.Tactic.Omega

namespace LCTR.CoreSMTRewriteRules

theorem arith_elim_gt (t s : Int) : (t > s) ↔ ¬ (s ≥ t) := by omega
theorem arith_elim_leq (t s : Int) : (t ≤ s) ↔ (s ≥ t) := by rfl
theorem arith_elim_lt (t s : Int) : (t < s) ↔ ¬ (t ≥ s) := by omega
theorem arith_eq_elim_int (t s : Int) : (t = s) ↔ (t ≥ s ∧ t ≤ s) := by omega
theorem arith_geq_ite_lift (c : Bool) (t s r : Int) :
    ((if c then t else s) ≥ r) ↔ (if c then t ≥ r else s ≥ r) := by
  cases c <;> rfl
theorem arith_geq_norm1_int (t s : Int) : (t ≥ s) ↔ (t - s ≥ 0) := by omega
theorem arith_geq_tighten (t s : Int) : (¬ (t ≥ s)) ↔ (s ≥ t + 1) := by omega
theorem arith_leq_ite_lift (c : Bool) (t s r : Int) :
    ((if c then t else s) ≤ r) ↔ (if c then t ≤ r else s ≤ r) := by
  cases c <;> rfl
theorem arith_leq_norm (t s : Int) : (t ≤ s) ↔ ¬ (t ≥ s + 1) := by omega
theorem bool_double_not_elim (t : Bool) : (!(!t)) = t := by cases t <;> rfl
theorem bool_eq_true (t : Bool) : decide (t = true) = t := by cases t <;> rfl
theorem bool_impl_false1 (t : Bool) : decide (t = true → False) = !t := by cases t <;> rfl
theorem eq_refl {α : Sort u} (t : α) : (t = t) ↔ True := by simp
theorem eq_symm {α : Sort u} (t s : α) : (t = s) ↔ (s = t) := by exact eq_comm
theorem ite_eq {α : Sort u} (c : Bool) (x y : α) :
    (if c then ((if c then x else y) = x) else ((if c then x else y) = y)) ↔ True := by
  cases c <;> simp
theorem ite_not_cond {α : Sort u} (c : Bool) (x y : α) :
    (if !c then x else y) = (if c then y else x) := by
  cases c <;> rfl
theorem ite_then_true (c x : Bool) : (if c then true else x) = (c || x) := by
  cases c <;> rfl

theorem reject_non_strict_tighten : ¬ ((¬ ((0 : Int) ≥ 0)) ↔ ((0 : Int) ≥ 0)) := by decide
theorem reject_swapped_ite_eq :
    ¬ (if true then ((if true then (0 : Int) else 1) = 1)
       else ((if true then (0 : Int) else 1) = 0)) := by decide

#print axioms arith_elim_gt
#print axioms arith_elim_leq
#print axioms arith_elim_lt
#print axioms arith_eq_elim_int
#print axioms arith_geq_ite_lift
#print axioms arith_geq_norm1_int
#print axioms arith_geq_tighten
#print axioms arith_leq_ite_lift
#print axioms arith_leq_norm
#print axioms bool_double_not_elim
#print axioms bool_eq_true
#print axioms bool_impl_false1
#print axioms eq_refl
#print axioms eq_symm
#print axioms ite_eq
#print axioms ite_not_cond
#print axioms ite_then_true
#print axioms reject_non_strict_tighten
#print axioms reject_swapped_ite_eq
end LCTR.CoreSMTRewriteRules
