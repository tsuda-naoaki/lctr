import CoreDynamicsFactors

namespace LCTR.CoreJointTimeSeed
set_option autoImplicit false
open LCTR.CoreTrajectoryDescent
universe u v w

structure Seed (C : Type u) (D : Type v) (B : Type w) where
  relation : C → D → B → Prop
  binding : C × D × B → C × D × B → Prop
  sourceOrder : C → C → Prop

variable {C : Type u} {D : Type v} {B : Type w}
abbrev Time (d : Seed C D B) := Q (genC d.relation d.binding)
def projection (d : Seed C D B) : C → Time d := prj (genC d.relation d.binding)
def generatedOrder (d : Seed C D B) : Time d → Time d → Prop :=
  LCTR.GeneratedOrderUniversal.Order
    (Relation.EqvGen.setoid (genC d.relation d.binding)) d.sourceOrder
def SameTime (d e : Seed C D B) : Prop :=
  ∀ x y, Relation.EqvGen (genC d.relation d.binding) x y ↔
    Relation.EqvGen (genC e.relation e.binding) x y
theorem SameTime.symm {d e : Seed C D B} (h : SameTime d e) : SameTime e d :=
  fun x y => (h x y).symm

theorem time_setoids_equal (d e : Seed C D B) (h : SameTime d e) :
    Relation.EqvGen.setoid (genC d.relation d.binding) =
      Relation.EqvGen.setoid (genC e.relation e.binding) := Setoid.ext h
theorem time_quotient_types_equal (d e : Seed C D B) (h : SameTime d e) :
    Time d = Time e := congrArg Quotient (time_setoids_equal d e h)
def timeMap (d e : Seed C D B) (h : SameTime d e) : Time d → Time e :=
  Quotient.map id (fun x y hx => (h x y).mp hx)
theorem time_projection_agrees (d e : Seed C D B) (h : SameTime d e) (x : C) :
    timeMap d e h (projection d x) = projection e x := rfl
theorem time_maps_inverse (d e : Seed C D B) (h : SameTime d e) (x : Time d) :
    timeMap e d h.symm (timeMap d e h x) = x := by
  induction x using Quotient.inductionOn with
  | _ x => rfl

theorem time_order_forward (d e : Seed C D B) (h : SameTime d e)
    (source : d.sourceOrder = e.sourceOrder) {x y : Time d}
    (xy : generatedOrder d x y) : generatedOrder e (timeMap d e h x) (timeMap d e h y) := by
  apply LCTR.GeneratedOrderUniversal.least_preorder
    (Relation.EqvGen.setoid (genC d.relation d.binding)) d.sourceOrder
    (fun a b => generatedOrder e (timeMap d e h a) (timeMap d e h b))
    (fun _ => LCTR.GeneratedOrderUniversal.reflexive _ _ _)
    (fun _ _ _ => LCTR.GeneratedOrderUniversal.transitive _ _) ?_ xy
  intro a b hab
  exact LCTR.GeneratedOrderUniversal.source_monotone _ _ (source ▸ hab)

theorem time_order_agrees (d e : Seed C D B) (h : SameTime d e)
    (source : d.sourceOrder = e.sourceOrder) (x y : Time d) :
    generatedOrder e (timeMap d e h x) (timeMap d e h y) ↔ generatedOrder d x y := by
  constructor
  · intro hy
    have hr := time_order_forward e d h.symm source.symm hy
    simpa only [time_maps_inverse] using hr
  · exact time_order_forward d e h source

end LCTR.CoreJointTimeSeed
