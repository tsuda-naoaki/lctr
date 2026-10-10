import CoreAffineRealization
namespace LCTR.CoreAffineOrderBridge
open LCTR.CoreAffineRealization
theorem difference_nonnegative_closure
    {K P : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (A : Data K P) (a b : P) :
    (A.lt a b ∨ a = b) ↔ 0 ≤ A.diff b a := by
  rw [le_iff_lt_or_eq, ← A.strict_sign a b]
  exact or_congr Iff.rfl ((difference_zero_iff A a b).symm.trans eq_comm)
#print axioms difference_nonnegative_closure
end LCTR.CoreAffineOrderBridge
