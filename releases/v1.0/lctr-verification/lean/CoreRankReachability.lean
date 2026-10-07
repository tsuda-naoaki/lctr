import Mathlib.Order.RelClasses
import Mathlib.Logic.Relation

namespace LCTR.CoreRankReachability
set_option autoImplicit false
universe u v

theorem path_increases {V : Type u} {R : Type v} (E : V → V → Prop)
    (lt : R → R → Prop) [IsStrictOrder R lt] (r : V → R)
    (step : ∀ a b, E a b → lt (r a) (r b)) {a b : V}
    (p : Relation.TransGen E a b) : lt (r a) (r b) := by
  induction p with
  | single h => exact step _ _ h
  | tail _ h ih => exact _root_.trans ih (step _ _ h)

theorem rank_acyclic {V : Type u} {R : Type v} (E : V → V → Prop)
    (lt : R → R → Prop) [IsStrictOrder R lt] (r : V → R)
    (step : ∀ a b, E a b → lt (r a) (r b)) (a : V) :
    ¬ Relation.TransGen E a a := by
  intro p
  exact irrefl (r a) (path_increases E lt r step p)

@[instance_reducible] def rankPartialOrder {V : Type u} {R : Type v} (E : V → V → Prop)
    (lt : R → R → Prop) [IsStrictOrder R lt] (r : V → R)
    (step : ∀ a b, E a b → lt (r a) (r b)) : PartialOrder V where
  le := Relation.ReflTransGen E
  le_refl _ := .refl
  le_trans _ _ _ := Relation.ReflTransGen.trans
  le_antisymm a b ab ba := by
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp ab with he | hp
    · exact he.symm
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp ba with he | hq
    · exact he
    exact False.elim (irrefl (r a)
      (_root_.trans (path_increases E lt r step hp) (path_increases E lt r step hq)))

end LCTR.CoreRankReachability
