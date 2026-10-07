import Std
namespace LCTR.CoreSMTBooleanRules
theorem bool_eq_false (t : Bool) : decide (t = false) = !t := by cases t <;> rfl
theorem ite_false_cond {α : Sort u} (x y : α) : (if false then x else y) = y := by rfl
#print axioms bool_eq_false
#print axioms ite_false_cond
end LCTR.CoreSMTBooleanRules
