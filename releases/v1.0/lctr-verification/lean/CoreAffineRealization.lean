import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

namespace LCTR.CoreAffineRealization
universe u v w z
set_option autoImplicit false

def orderCondition {S : Type u} {T : Type v} (f : S ↪ T)
    (r : S → S → Prop) (s : T → T → Prop) : Prop :=
  ∀ x y, s (f x) (f y) ↔ r x y

theorem order_embedding_pullback_iff {S : Type u} {T : Type v} (f : S ↪ T)
    (r : S → S → Prop) (s : T → T → Prop) :
    orderCondition f r s ↔ (fun x y => s (f x) (f y)) = r := by
  constructor
  · intro h
    exact funext (fun x => funext (fun y => propext (h x y)))
  · intro h x y
    exact Iff.of_eq (congrFun (congrFun h x) y)

structure Data (K : Type u) (P : Type v) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] where
  act : P → K → P
  diff : P → P → K
  lt : P → P → Prop
  zero_action : ∀ a, act a 0 = a
  add_action : ∀ a x y, act a (x+y) = act (act a x) y
  diff_spec : ∀ a b x, act a x = b ↔ x = diff b a
  strict_sign : ∀ a b, lt a b ↔ 0 < diff b a

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {P : Type v}

theorem action_free (A : Data K P) (a : P) (x y : K)
    (h : A.act a x = A.act a y) : x = y :=
  ((A.diff_spec a (A.act a y) x).mp h).trans
    ((A.diff_spec a (A.act a y) y).mp rfl).symm

theorem action_transitive (A : Data K P) (a b : P) :
    ∃! x : K, A.act a x = b := by
  refine ⟨A.diff b a, (A.diff_spec a b _).mpr rfl, ?_⟩
  intro y hy
  exact (A.diff_spec a b y).mp hy

theorem difference_reflexive (A : Data K P) (a : P) : A.diff a a = 0 :=
  ((A.diff_spec a a 0).mp (A.zero_action a)).symm

theorem difference_zero_iff (A : Data K P) (a b : P) :
    A.diff b a = 0 ↔ a = b := by
  constructor
  · intro h
    exact (A.zero_action a).symm.trans ((A.diff_spec a b 0).mpr h.symm)
  · intro h
    subst b
    exact difference_reflexive A a

theorem difference_cocycle (A : Data K P) (a b c : P) :
    A.diff c a = A.diff b a + A.diff c b := by
  have ab : A.act a (A.diff b a) = b := (A.diff_spec a b _).mpr rfl
  have bc : A.act b (A.diff c b) = c := (A.diff_spec b c _).mpr rfl
  have ac : A.act a (A.diff b a + A.diff c b) = c := by
    rw [A.add_action, ab, bc]
  exact ((A.diff_spec a c _).mp ac).symm

theorem difference_reverse (A : Data K P) (a b : P) :
    A.diff a b = - A.diff b a := by
  have h := difference_cocycle A a b a
  rw [difference_reflexive] at h
  linarith

theorem induced_strict_linear (A : Data K P) :
    (∀ a, ¬ A.lt a a) ∧
    (∀ a b c, A.lt a b → A.lt b c → A.lt a c) ∧
    (∀ a b, a ≠ b → A.lt a b ∨ A.lt b a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a h
    have hpos := (A.strict_sign a a).mp h
    rw [difference_reflexive] at hpos
    exact (lt_irrefl 0) hpos
  · intro a b c hab hbc
    apply (A.strict_sign a c).mpr
    rw [difference_cocycle A a b c]
    exact add_pos ((A.strict_sign a b).mp hab) ((A.strict_sign b c).mp hbc)
  · intro a b hab
    have hn : A.diff b a ≠ 0 := fun h => hab ((difference_zero_iff A a b).mp h)
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · right
      apply (A.strict_sign b a).mpr
      rw [difference_reverse A a b]
      exact neg_pos.mpr hneg
    · exact Or.inl ((A.strict_sign a b).mpr hpos)

def coordinateDifference {X : Type w} {Q : Type z} (A : Data K P)
    (projection : X → Q) (embedding : Q ↪ P) (x1 x0 : X) : K :=
  A.diff (embedding (projection x1)) (embedding (projection x0))

theorem coordinate_difference_sign {X : Type w} {Q : Type z} (A : Data K P)
    (projection : X → Q) (embedding : Q ↪ P) (x0 x1 : X) :
    A.lt (embedding (projection x0)) (embedding (projection x1)) ↔
      0 < coordinateDifference A projection embedding x1 x0 :=
  A.strict_sign _ _

end LCTR.CoreAffineRealization
