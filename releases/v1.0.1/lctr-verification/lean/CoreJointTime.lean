import CoreNativeCurves
import LCTR.JointTimeReadiness

namespace LCTR.CoreJointTime
set_option autoImplicit false
open LCTR.CoreObserverTime LCTR.CoreTrajectoryDescent LCTR.CoreNativeCurves
open LCTR.TransitiveIncomparabilityQuotientCore
universe u v w
variable {C : Type u} {D : Type v} {B : Type w}

def SameTime (d e : Input C D B) : Prop :=
  ∀ x y, Relation.EqvGen (genC d.relation d.binding) x y ↔
    Relation.EqvGen (genC e.relation e.binding) x y
theorem SameTime.symm {d e : Input C D B} (h : SameTime d e) : SameTime e d :=
  fun x y => (h x y).symm

theorem time_setoids_equal (d e : Input C D B) (h : SameTime d e) :
    Relation.EqvGen.setoid (genC d.relation d.binding) =
      Relation.EqvGen.setoid (genC e.relation e.binding) := Setoid.ext h

theorem time_quotient_types_equal (d e : Input C D B) (h : SameTime d e) :
    Time d = Time e := congrArg Quotient (time_setoids_equal d e h)

def timeMap (d e : Input C D B) (h : SameTime d e) : Time d → Time e :=
  Quotient.map id (fun x y hx => (h x y).mp hx)

theorem time_projection_agrees (d e : Input C D B) (h : SameTime d e) (x : C) :
    timeMap d e h (timeProjection d x) = timeProjection e x := rfl

theorem time_maps_inverse (d e : Input C D B) (h : SameTime d e) (x : Time d) :
    timeMap e d h.symm (timeMap d e h x) = x := by
  induction x using Quotient.inductionOn with
  | _ x => rfl

def timeEquiv (d e : Input C D B) (h : SameTime d e) : Time d ≃ Time e where
  toFun := timeMap d e h
  invFun := timeMap e d h.symm
  left_inv := time_maps_inverse d e h
  right_inv := time_maps_inverse e d h.symm

theorem time_order_forward (d e : Input C D B) (h : SameTime d e)
    (source : d.sourceOrder = e.sourceOrder) {x y : Time d} (xy : generatedOrder d x y) :
    generatedOrder e (timeMap d e h x) (timeMap d e h y) := by
  apply LCTR.GeneratedOrderUniversal.least_preorder
    (Relation.EqvGen.setoid (genC d.relation d.binding)) d.sourceOrder
    (fun a b => generatedOrder e (timeMap d e h a) (timeMap d e h b))
    (fun _ => LCTR.GeneratedOrderUniversal.reflexive _ _ _)
    (fun _ _ _ => LCTR.GeneratedOrderUniversal.transitive _ _) ?_ xy
  intro a b hab
  exact LCTR.GeneratedOrderUniversal.source_monotone _ _ (source ▸ hab)

theorem time_order_agrees (d e : Input C D B) (h : SameTime d e)
    (source : d.sourceOrder = e.sourceOrder) (x y : Time d) :
    generatedOrder e (timeMap d e h x) (timeMap d e h y) ↔ generatedOrder d x y := by
  constructor
  · intro hy
    have hr := time_order_forward e d h.symm source.symm hy
    simpa only [time_maps_inverse] using hr
  · exact time_order_forward d e h source

theorem time_strict_agrees (d e : Input C D B) (h : SameTime d e)
    (source : d.sourceOrder = e.sourceOrder) (x y : Time d) :
    strict e (timeMap d e h x) (timeMap d e h y) ↔ strict d x y := by
  constructor
  · rintro ⟨le,ne⟩
    exact ⟨(time_order_agrees d e h source x y).mp le, fun eq => ne (congrArg (timeMap d e h) eq)⟩
  · rintro ⟨le,ne⟩
    exact ⟨(time_order_agrees d e h source x y).mpr le,
      fun eq => ne ((timeEquiv d e h).injective eq)⟩

theorem time_incomparability_agrees (d e : Input C D B) (h : SameTime d e)
    (source : d.sourceOrder = e.sourceOrder) (x y : Time d) :
    Inc (strict e) (timeMap d e h x) (timeMap d e h y) ↔ Inc (strict d) x y := by
  simp only [Inc, time_strict_agrees d e h source]

def orderMap (d e : Input C D B) (hd : IncTrans d) (he : IncTrans e)
    (h : SameTime d e) (source : d.sourceOrder = e.sourceOrder) : OrderTime d hd → OrderTime e he :=
  Quotient.map (timeMap d e h) (fun x y hx => (time_incomparability_agrees d e h source x y).mpr hx)

theorem order_projection_agrees (d e : Input C D B) (hd : IncTrans d) (he : IncTrans e)
    (h : SameTime d e) (source : d.sourceOrder = e.sourceOrder) (x : Time d) :
    orderMap d e hd he h source (orderProjection d hd x) =
      orderProjection e he (timeMap d e h x) := rfl

theorem order_maps_inverse (d e : Input C D B) (hd : IncTrans d) (he : IncTrans e)
    (h : SameTime d e) (source : d.sourceOrder = e.sourceOrder) (q : OrderTime d hd) :
    orderMap e d he hd h.symm source.symm (orderMap d e hd he h source q) = q := by
  obtain ⟨x,rfl⟩ := (projection_contract d hd).1 q
  rw [order_projection_agrees, order_projection_agrees, time_maps_inverse]

def orderEquiv (d e : Input C D B) (hd : IncTrans d) (he : IncTrans e)
    (h : SameTime d e) (source : d.sourceOrder = e.sourceOrder) : OrderTime d hd ≃ OrderTime e he where
  toFun := orderMap d e hd he h source
  invFun := orderMap e d he hd h.symm source.symm
  left_inv := order_maps_inverse d e hd he h source
  right_inv := order_maps_inverse e d he hd h.symm source.symm

theorem order_strict_agrees (d e : Input C D B) (hd : IncTrans d) (he : IncTrans e)
    (h : SameTime d e) (source : d.sourceOrder = e.sourceOrder) (p q : OrderTime d hd) :
    orderLt e he (orderMap d e hd he h source p) (orderMap d e hd he h source q) ↔ orderLt d hd p q := by
  obtain ⟨x,rfl⟩ := (projection_contract d hd).1 p
  obtain ⟨y,rfl⟩ := (projection_contract d hd).1 q
  rw [order_projection_agrees, order_projection_agrees]
  exact ((projection_contract e he).2.2 _ _).trans
    ((time_strict_agrees d e h source x y).trans ((projection_contract d hd).2.2 x y).symm)

theorem order_map_unique (d e : Input C D B) (hd : IncTrans d) (he : IncTrans e)
    (h : SameTime d e) (source : d.sourceOrder = e.sourceOrder)
    (f : OrderTime d hd → OrderTime e he)
    (commutes : ∀ x, f (orderProjection d hd x) = orderProjection e he (timeMap d e h x)) :
    f = orderMap d e hd he h source := by
  funext q
  obtain ⟨x,rfl⟩ := (projection_contract d hd).1 q
  exact commutes x

def transferEmbedding (d e : Input C D B) (hd : IncTrans d) (he : IncTrans e)
    (h : SameTime d e) (source : d.sourceOrder = e.sourceOrder) (rho : RealEmbedding e he) :
    RealEmbedding d hd where
  value := rho.value ∘ orderMap d e hd he h source
  orderIff p q := (order_strict_agrees d e hd he h source p q).symm.trans (rho.orderIff _ _)

theorem embedding_transfers (d e : Input C D B) (hd : IncTrans d) (he : IncTrans e)
    (h : SameTime d e) (source : d.sourceOrder = e.sourceOrder) (rho : RealEmbedding e he) :
    Nonempty (RealEmbedding d hd) ∧
    ∀ q, (transferEmbedding d e hd he h source rho).value q =
      rho.value (orderMap d e hd he h source q) := ⟨⟨transferEmbedding d e hd he h source rho⟩,fun _ => rfl⟩

variable {I : Type}
structure Family (C : Type u) (D : Type v) (B : Type w) (I : Type) where
  data : I → Input C D B
  inc : (i : I) → IncTrans (data i)
  single : (i : I) → Single (data i)
  fiber : (i : I) → FiberCondition (data i) (inc i) (single i)
  common : ∀ i j, SameTime (data i) (data j)
  source : ∀ i j, (data i).sourceOrder = (data j).sourceOrder

def individualDomain (f : Family C D B I) (base i : I) : Set (OrderTime (f.data base) (f.inc base)) :=
  fun q => orderMap (f.data base) (f.data i) (f.inc base) (f.inc i) (f.common base i) (f.source base i) q ∈
    OrderDomain (f.data i) (f.inc i)
abbrev CommonDomain (f : Family C D B I) (base : I) :=
  LCTR.JointTimeReadiness.CommonDomain (individualDomain f base)
noncomputable def individualCurve (f : Family C D B I) (base i : I)
    (q : individualDomain f base i) : State (f.data i) :=
  scalarTrajectory (f.data i) (f.inc i) (f.single i) (f.fiber i)
    ⟨orderMap (f.data base) (f.data i) (f.inc base) (f.inc i) (f.common base i) (f.source base i) q.val,
      q.property⟩
noncomputable def jointCurve (f : Family C D B I) (base : I) (q : CommonDomain f base) :
    (i : I) → State (f.data i) :=
  LCTR.JointTimeReadiness.Joint (individualDomain f base) (individualCurve f base) q

theorem native_joint_components (f : Family C D B I) (base : I) (q : CommonDomain f base) (i : I) :
    jointCurve f base q i = individualCurve f base i ⟨q.val,q.property i⟩ := rfl

theorem native_joint_unique (f : Family C D B I) (base : I)
    (g : CommonDomain f base → (i : I) → State (f.data i))
    (components : ∀ q i, g q i = individualCurve f base i ⟨q.val,q.property i⟩) :
    g = jointCurve f base :=
  LCTR.JointTimeReadiness.joint_unique (individualDomain f base) (individualCurve f base) g components

theorem joint_relation_on_actual_states (f : Family C D B I) (base : I) {V : Type}
    (r : ((i : I) → State (f.data i)) → V → Prop) (q : CommonDomain f base) (v : V) :
    LCTR.JointTimeReadiness.Pullback (individualDomain f base) (individualCurve f base) r q v ↔
      r (jointCurve f base q) v := Iff.rfl

end LCTR.CoreJointTime
