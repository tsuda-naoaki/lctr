import CoreDynamicsFactors
import OrderEmbeddingBridge

namespace LCTR.CoreObserverTime
set_option autoImplicit false
open LCTR.CoreTrajectoryDescent LCTR.CoreDynamicsFactors
open LCTR.OrderEmbeddingBridgeV1 LCTR.TransitiveIncomparabilityQuotientCore
universe u v w

structure Input (C : Type u) (D : Type v) (B : Type w) where
  relation : C → D → B → Prop
  binding : C × D × B → C × D × B → Prop
  sourceOrder : C → C → Prop
  antisymm : ∀ x y,
    LCTR.GeneratedOrderUniversal.Order
      (Relation.EqvGen.setoid (genC relation binding)) sourceOrder x y →
    LCTR.GeneratedOrderUniversal.Order
      (Relation.EqvGen.setoid (genC relation binding)) sourceOrder y x → x = y

variable {C : Type u} {D : Type v} {B : Type w}
abbrev Time (d : Input C D B) := Q (genC d.relation d.binding)
def timeProjection (d : Input C D B) : C → Time d := prj (genC d.relation d.binding)
def generatedOrder (d : Input C D B) : Time d → Time d → Prop :=
  LCTR.GeneratedOrderUniversal.Order
    (Relation.EqvGen.setoid (genC d.relation d.binding)) d.sourceOrder
def strict (d : Input C D B) (x y : Time d) : Prop := generatedOrder d x y ∧ x ≠ y

theorem generated_partial (d : Input C D B) :
    ∃ p : PartialOrder (Time d), p.le = generatedOrder d :=
  native_generated_partial_order _ _ d.antisymm

theorem strict_irrefl (d : Input C D B) (x : Time d) : ¬ strict d x x :=
  fun h => h.2 rfl

theorem strict_trans (d : Input C D B) {x y z : Time d}
    (hxy : strict d x y) (hyz : strict d y z) : strict d x z := by
  refine ⟨LCTR.GeneratedOrderUniversal.transitive _ _ hxy.1 hyz.1, ?_⟩
  intro hxz
  have hyx : generatedOrder d y x := hxz.symm ▸ hyz.1
  exact hxy.2 (d.antisymm x y hxy.1 hyx)

theorem strict_partial (d : Input C D B) :
    (∀ x, ¬ strict d x x) ∧
    (∀ {x y z}, strict d x y → strict d y z → strict d x z) :=
  ⟨strict_irrefl d, strict_trans d⟩

theorem inc_reflexive_symmetric (d : Input C D B) :
    (∀ x, Inc (strict d) x x) ∧
    (∀ {x y}, Inc (strict d) x y → Inc (strict d) y x) :=
  ⟨fun x => ⟨strict_irrefl d x, strict_irrefl d x⟩, inc_symmetric (strict d)⟩

def IncTrans (d : Input C D B) : Prop :=
  ∀ {x y z}, Inc (strict d) x y → Inc (strict d) y z → Inc (strict d) x z

theorem inc_equivalence (d : Input C D B) (h : IncTrans d) :
    Equivalence (Inc (strict d)) :=
  (incSetoid (strict d) (strict_irrefl d) h).iseqv

theorem strict_invariance (d : Input C D B) (h : IncTrans d)
    {x x' y y' : Time d} (hx : Inc (strict d) x x') (hy : Inc (strict d) y y') :
    strict d x y ↔ strict d x' y' :=
  representative_invariance (strict d) (strict_trans d) h hx hy

abbrev OrderTime (d : Input C D B) (h : IncTrans d) :=
  IncQuotient (strict d) (strict_irrefl d) h
def orderProjection (d : Input C D B) (h : IncTrans d) : Time d → OrderTime d h :=
  proj (strict d) (strict_irrefl d) h
def orderLt (d : Input C D B) (h : IncTrans d) : OrderTime d h → OrderTime d h → Prop :=
  quotientLt (strict d) (strict_irrefl d) h

theorem order_quotient_strict_linear (d : Input C D B) (h : IncTrans d) :
    (∀ q, ¬ orderLt d h q q) ∧
    (∀ {x y z}, orderLt d h x y → orderLt d h y z → orderLt d h x z) ∧
    (∀ {x y}, x ≠ y → orderLt d h x y ∨ orderLt d h y x) :=
  quotient_strict_linear_components (strict d) (strict_irrefl d) (strict_trans d) h

theorem projection_contract (d : Input C D B) (h : IncTrans d) :
    Function.Surjective (orderProjection d h) ∧
    (∀ x y, orderProjection d h x = orderProjection d h y ↔ Inc (strict d) x y) ∧
    (∀ x y, orderLt d h (orderProjection d h x) (orderProjection d h y) ↔ strict d x y) :=
  ⟨proj_surjective (strict d) (strict_irrefl d) h,
    proj_eq_iff_inc (strict d) (strict_irrefl d) h,
    quotientLt_proj_iff (strict d) (strict_irrefl d) (strict_trans d) h⟩

structure RealEmbedding (d : Input C D B) (h : IncTrans d) where
  value : OrderTime d h → ℝ
  orderIff : ∀ x y, orderLt d h x y ↔ value x < value y

theorem embedding_injective (d : Input C D B) (h : IncTrans d)
    (rho : RealEmbedding d h) : Function.Injective rho.value :=
  real_order_iff_map_injective (strict d) (strict_irrefl d) (strict_trans d) h
    rho.value rho.orderIff

theorem image_inverse_contract (d : Input C D B) (h : IncTrans d)
    (rho : RealEmbedding d h) :
    (∀ q, LCTR.ImageInverseConstruction.inverse rho.value ⟨rho.value q, ⟨q,rfl⟩⟩ = q) ∧
    (∀ t : LCTR.ImageInverseConstruction.Image rho.value,
      rho.value (LCTR.ImageInverseConstruction.inverse rho.value t) = t.val) :=
  real_embedding_image_inverse_compositions (strict d) (strict_irrefl d) (strict_trans d) h
    rho.value rho.orderIff

def timeRep (d : Input C D B) (h : IncTrans d) (rho : RealEmbedding d h) : Time d → ℝ :=
  rho.value ∘ orderProjection d h

theorem real_representation_contract (d : Input C D B) (h : IncTrans d)
    (rho : RealEmbedding d h) :
    (∀ x y, timeRep d h rho x = timeRep d h rho y ↔ Inc (strict d) x y) ∧
    (∀ x y, timeRep d h rho x < timeRep d h rho y ↔ strict d x y) := by
  constructor
  · intro x y
    exact (embedding_injective d h rho).eq_iff.trans ((projection_contract d h).2.1 x y)
  · intro x y
    exact (rho.orderIff _ _).symm.trans ((projection_contract d h).2.2 x y)

theorem source_time_representation_contract (d : Input C D B) (h : IncTrans d)
    (rho : RealEmbedding d h) :
    (∀ x y, timeProjection d x = timeProjection d y ↔
      Relation.EqvGen (genC d.relation d.binding) x y) ∧
    (∀ x y, timeRep d h rho (timeProjection d x) = timeRep d h rho (timeProjection d y) ↔
      Inc (strict d) (timeProjection d x) (timeProjection d y)) ∧
    (∀ x y, timeRep d h rho (timeProjection d x) < timeRep d h rho (timeProjection d y) ↔
      strict d (timeProjection d x) (timeProjection d y)) :=
  ⟨canonical_projection_class _,
    fun x y => (real_representation_contract d h rho).1 (timeProjection d x) (timeProjection d y),
    fun x y => (real_representation_contract d h rho).2 (timeProjection d x) (timeProjection d y)⟩

end LCTR.CoreObserverTime
