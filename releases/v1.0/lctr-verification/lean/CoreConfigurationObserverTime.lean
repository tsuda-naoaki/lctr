import CoreConfigurationDynamics
import CoreObserverTime

namespace LCTR.CoreConfigurationObserverTime
set_option autoImplicit false
open Set LCTR.CoreOperationalConfiguration LCTR.CoreConfigurationDynamics
open LCTR.CoreTrajectoryDescent LCTR.CoreDynamicsFactors

variable (x : Configuration)
abbrev Clock := Token x.2.schema .clock
abbrev Record := Token x.2.schema .detector
abbrev Body := Token x.2.schema .body

def pack (c : Clock x) (d : Record x) (b : Body x) : SourceTuple x
  | .clock => c
  | .detector => d
  | .body => b

theorem pack_roundtrip (p : SourceTuple x) :
    pack x (p .clock) (p .detector) (p .body) = p := by
  funext r
  cases r <;> rfl

def relation (R : Set (SourceTuple x)) (c : Clock x) (d : Record x) (b : Body x) : Prop :=
  pack x c d b ∈ R

variable (o : x.1.reception.Node) (h : Unique x o)
variable (R : Set (SourceTuple x)) (L : Set (ReceivedTuple x o))
variable (bind : ReceivedTuple x o → ReceivedTuple x o → Prop)

def binding (p q : Clock x × Record x × Body x) : Prop :=
  sourceBinding x o h L bind (pack x p.1 p.2.1 p.2.2) (pack x q.1 q.2.1 q.2.2)

theorem clock_generator_exact :
    genC (relation x R) (binding x o h L bind) = generated x o h R L bind .clock := by
  funext s t
  apply propext
  constructor
  · rintro ⟨d,b,d',b',hp,hq,hb⟩
    exact ⟨pack x s d b,hp,pack x t d' b',hq,hb,rfl,rfl⟩
  · rintro ⟨p,hp,q,hq,hb,hs,ht⟩
    subst s
    subst t
    refine ⟨p .detector,p .body,q .detector,q .body,?_,?_,?_⟩
    · simpa only [relation,pack_roundtrip] using hp
    · simpa only [relation,pack_roundtrip] using hq
    · simpa only [binding,pack_roundtrip] using hb

theorem body_generator_exact :
    genB (relation x R) (binding x o h L bind) = generated x o h R L bind .body := by
  funext s t
  apply propext
  constructor
  · rintro ⟨c,d,c',d',hp,hq,hb⟩
    exact ⟨pack x c d s,hp,pack x c' d' t,hq,hb,rfl,rfl⟩
  · rintro ⟨p,hp,q,hq,hb,hs,ht⟩
    subst s
    subst t
    refine ⟨p .clock,p .detector,q .clock,q .detector,?_,?_,?_⟩
    · simpa only [relation,pack_roundtrip] using hp
    · simpa only [relation,pack_roundtrip] using hq
    · simpa only [binding,pack_roundtrip] using hb

theorem clock_quotient_kernel (s t : Clock x) :
    prj (genC (relation x R) (binding x o h L bind)) s =
      prj (genC (relation x R) (binding x o h L bind)) t ↔
    Relation.EqvGen (generated x o h R L bind .clock) s t := by
  rw [canonical_projection_class,clock_generator_exact]

theorem body_quotient_kernel (s t : Body x) :
    prj (genB (relation x R) (binding x o h L bind)) s =
      prj (genB (relation x R) (binding x o h L bind)) t ↔
    Relation.EqvGen (generated x o h R L bind .body) s t := by
  rw [canonical_projection_class,body_generator_exact]

theorem source_trajectory_exact (c : Clock x) (b : Body x) :
    source (relation x R) c b ↔ ∃ p ∈ R, p .clock=c ∧ p .body=b := by
  constructor
  · rintro ⟨d,hd⟩
    exact ⟨pack x c d b,hd,rfl,rfl⟩
  · rintro ⟨p,hp,hc,hb⟩
    subst c
    subst b
    exact ⟨p .detector,by simpa only [relation,pack_roundtrip] using hp⟩

def Anti : Prop := ∀ s t,
  LCTR.GeneratedOrderUniversal.Order
    (Relation.EqvGen.setoid (genC (relation x R) (binding x o h L bind)))
    (sourceClockOrder x.2.schema).le s t →
  LCTR.GeneratedOrderUniversal.Order
    (Relation.EqvGen.setoid (genC (relation x R) (binding x o h L bind)))
    (sourceClockOrder x.2.schema).le t s → s=t

def input (anti : Anti x o h R L bind) :
    LCTR.CoreObserverTime.Input (Clock x) (Record x) (Body x) where
  relation := relation x R
  binding := binding x o h L bind
  sourceOrder := (sourceClockOrder x.2.schema).le
  antisymm := anti

variable (anti : Anti x o h R L bind)

theorem observer_source_order_step (s t : Clock x)
    (hs : (sourceClockOrder x.2.schema).le s t) :
    LCTR.CoreObserverTime.generatedOrder (input x o h R L bind anti)
      (LCTR.CoreObserverTime.timeProjection (input x o h R L bind anti) s)
      (LCTR.CoreObserverTime.timeProjection (input x o h R L bind anti) t) :=
  canonical_source_order_preserved _ _ s t hs

theorem observer_partial_order :
    ∃ p : PartialOrder (LCTR.CoreObserverTime.Time (input x o h R L bind anti)),
      p.le = LCTR.CoreObserverTime.generatedOrder (input x o h R L bind anti) :=
  LCTR.CoreObserverTime.generated_partial (input x o h R L bind anti)

theorem real_time_source_contract
    (inc : LCTR.CoreObserverTime.IncTrans (input x o h R L bind anti))
    (rho : LCTR.CoreObserverTime.RealEmbedding (input x o h R L bind anti) inc) :
    (∀ s t, LCTR.CoreObserverTime.timeProjection (input x o h R L bind anti) s =
      LCTR.CoreObserverTime.timeProjection (input x o h R L bind anti) t ↔
      Relation.EqvGen (generated x o h R L bind .clock) s t) ∧
    (∀ s t,
      LCTR.CoreObserverTime.timeRep (input x o h R L bind anti) inc rho
        (LCTR.CoreObserverTime.timeProjection (input x o h R L bind anti) s) =
      LCTR.CoreObserverTime.timeRep (input x o h R L bind anti) inc rho
        (LCTR.CoreObserverTime.timeProjection (input x o h R L bind anti) t) ↔
      LCTR.TransitiveIncomparabilityQuotientCore.Inc
        (LCTR.CoreObserverTime.strict (input x o h R L bind anti))
        (LCTR.CoreObserverTime.timeProjection (input x o h R L bind anti) s)
        (LCTR.CoreObserverTime.timeProjection (input x o h R L bind anti) t)) ∧
    (∀ s t,
      LCTR.CoreObserverTime.timeRep (input x o h R L bind anti) inc rho
        (LCTR.CoreObserverTime.timeProjection (input x o h R L bind anti) s) <
      LCTR.CoreObserverTime.timeRep (input x o h R L bind anti) inc rho
        (LCTR.CoreObserverTime.timeProjection (input x o h R L bind anti) t) ↔
      LCTR.CoreObserverTime.strict (input x o h R L bind anti)
        (LCTR.CoreObserverTime.timeProjection (input x o h R L bind anti) s)
        (LCTR.CoreObserverTime.timeProjection (input x o h R L bind anti) t)) := by
  have hc := LCTR.CoreObserverTime.source_time_representation_contract
    (input x o h R L bind anti) inc rho
  exact ⟨clock_quotient_kernel x o h R L bind,hc.2⟩

end LCTR.CoreConfigurationObserverTime
