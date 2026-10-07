import CoreCarrierPatterns
import Chapter03SourceOrderRecovery
import Mathlib.Data.Set.Finite.Basic

namespace LCTR.CoreOperationalConfiguration

open LCTR.Chapter02 LCTR.CoreCarrierPatterns
open LCTR.Chapter03SourceOrderRecovery
universe u

inductive SourceRole where | clock | detector | body
deriving DecidableEq

structure OrderData (X : Type u) where
  le : X → X → Prop
  reflexive : ∀ x, le x x
  transitive : ∀ x y z, le x y → le y z → le x z
  antisymmetric : ∀ x y, le x y → le y x → x = y

structure Reception (a : Input) (p : Physical a) where
  Node : Type u
  node_nonempty : Nonempty Node
  receive : Node → SourceRole → Type u
  receiver : Node → {q : p.Carrier realizationObserver //
    ∃ x : RoleDomain a realizationObserver, p.realize realizationObserver x = q}
  order : (v : Node) → OrderData ((r : SourceRole) × receive v r)

structure Raw where
  abstract : Input
  physical : Physical abstract
  reception : Reception abstract physical

structure SourceSchema (a : Input) where
  ClockSource : Type u
  clock_nonempty : Nonempty ClockSource
  DetectorToken : Type u
  detector_nonempty : Nonempty DetectorToken
  BodyToken : Type u
  body_nonempty : Nonempty BodyToken
  ClockLabel : Type u
  DetectorLabel : Type u
  clockDisplay : CToken ClockSource → ClockLabel
  detectorDisplay : DetectorToken → DetectorLabel
  sequence : DetectorToken → Nat
  bodyPosition : BodyToken → IndexAt a
  cell : DetectorToken → Set DetectorToken
  cell_finite : ∀ x, (cell x).Finite
  cell_self : ∀ x, x ∈ cell x
  cell_class : ∀ x y, y ∈ cell x ↔ cell y = cell x

def Token {a : Input} (s : SourceSchema a) : SourceRole → Type u
  | .clock => CToken s.ClockSource
  | .detector => s.DetectorToken
  | .body => s.BodyToken

def detectorEmbedding {a : Input} (s : SourceSchema a) (x : s.DetectorToken) :
    DToken s.DetectorToken := ⟨x, s.sequence x⟩

def detectorOrder {a : Input} (s : SourceSchema a) (x y : s.DetectorToken) : Prop :=
  DLE (detectorEmbedding s x) (detectorEmbedding s y)

theorem detector_order_exact {a : Input} (s : SourceSchema a) (x y : s.DetectorToken) :
    detectorOrder s x y ↔ x = y ∨ s.sequence x < s.sequence y := by
  constructor
  · rintro (same | lt)
    · exact Or.inl (congrArg DToken.identity same)
    · exact Or.inr lt
  · rintro (same | lt)
    · exact Or.inl (congrArg (detectorEmbedding s) same)
    · exact Or.inr lt

def sourceClockOrder {a : Input} (s : SourceSchema a) : OrderData (CToken s.ClockSource) where
  le := CFamilyLE
  reflexive := ch03_r041_c_family_partial_order.1
  transitive := ch03_r041_c_family_partial_order.2.1
  antisymmetric := ch03_r041_c_family_partial_order.2.2

def sourceDetectorOrder {a : Input} (s : SourceSchema a) : OrderData s.DetectorToken where
  le := detectorOrder s
  reflexive := fun x => ch03_r035_d_partial_order.1 (detectorEmbedding s x)
  transitive := fun x y z hxy hyz => ch03_r035_d_partial_order.2.1
    (detectorEmbedding s x) (detectorEmbedding s y) (detectorEmbedding s z) hxy hyz
  antisymmetric := fun x y hxy hyx => congrArg DToken.identity
    (ch03_r035_d_partial_order.2.2 (detectorEmbedding s x) (detectorEmbedding s y) hxy hyx)

structure SourceData (raw : Raw) where
  schema : SourceSchema raw.abstract
  arrival : (v : raw.reception.Node) → (r : SourceRole) →
    PartialArrival (Token schema r) (raw.reception.receive v r)
  sourceRelation : Set (Token schema .clock × Token schema .detector)
  comparisonRelation : (v : raw.reception.Node) →
    Set (raw.reception.receive v .clock × raw.reception.receive v .detector)
  relationCompatibility : ∀ v x y
    (hx : x ∈ (arrival v .clock).dom) (hy : y ∈ (arrival v .detector).dom),
    (x,y) ∈ sourceRelation ↔
      ((arrival v .clock).val x hx, (arrival v .detector).val y hy) ∈ comparisonRelation v

abbrev Configuration := (raw : Raw) × SourceData raw

def make (raw : Raw) (s : SourceData raw) : Configuration := ⟨raw, s⟩

def roles (x : Configuration) (i : IndexAt x.1.abstract) :=
  roleBundle x.1.abstract.Local x.1.abstract.binding x.1.abstract.abstracted
    x.1.abstract.assign i.val

def body (x : Configuration) (i : IndexAt x.1.abstract) := bodyPair x.1.abstract i

noncomputable def recovery (x : Configuration) (v : x.1.reception.Node) (r : SourceRole)
    (a : {a : x.1.reception.receive v r // UniqueRecoverable (x.2.arrival v r) a}) :
    Token x.2.schema r := (recoverSubtype (x.2.arrival v r) a.val a.property).val

theorem pairing_preserves_components (raw : Raw) (s : SourceData raw) :
    (make raw s).1 = raw ∧ (make raw s).2 = s := ⟨rfl, rfl⟩

theorem pairing_roundtrip (x : Configuration) : make x.1 x.2 = x := by rfl

theorem role_positions_preserved (x : Configuration) (i : IndexAt x.1.abstract) :
    (roles x i).clock.zeta = i.val ∧ (roles x i).detector.zeta = i.val ∧
    (roles x i).body.zeta = i.val ∧ (roles x i).observer.zeta = i.val ∧
    (roles x i).clock.role = .clock ∧ (roles x i).detector.role = .detector ∧
    (roles x i).body.role = .body ∧ (roles x i).observer.role = .observer := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem receiver_is_realized (x : Configuration) (v : x.1.reception.Node) :
    ∃ i : RoleDomain x.1.abstract realizationObserver,
      x.1.physical.realize realizationObserver i = (x.1.reception.receiver v).val :=
  (x.1.reception.receiver v).property

theorem recovery_preserves_arrival (x : Configuration) (v : x.1.reception.Node) (r : SourceRole)
    (a : {a : x.1.reception.receive v r // UniqueRecoverable (x.2.arrival v r) a}) :
    ∃ h : recovery x v r a ∈ (x.2.arrival v r).dom,
      (x.2.arrival v r).val (recovery x v r a) h = a.val := by
  exact ⟨(recoverSubtype (x.2.arrival v r) a.val a.property).property,
    recoverSubtype_spec (x.2.arrival v r) a.val a.property⟩

theorem recovery_returns_original (x : Configuration) (v : x.1.reception.Node) (r : SourceRole)
    (t : Token x.2.schema r) (ht : t ∈ (x.2.arrival v r).dom)
    (hu : UniqueRecoverable (x.2.arrival v r) ((x.2.arrival v r).val t ht)) :
    recovery x v r ⟨(x.2.arrival v r).val t ht, hu⟩ = t :=
  recover_eq_original (x.2.arrival v r) t ht hu

theorem body_recovery_preserves_abstraction_source (x : Configuration) (v : x.1.reception.Node)
    (t : x.2.schema.BodyToken) (ht : t ∈ (x.2.arrival v .body).dom)
    (hu : UniqueRecoverable (x.2.arrival v .body) ((x.2.arrival v .body).val t ht)) :
    body x (x.2.schema.bodyPosition
      (recovery x v .body ⟨(x.2.arrival v .body).val t ht, hu⟩)) =
      body x (x.2.schema.bodyPosition t) := by
  rw [recovery_returns_original x v .body t ht hu]

theorem source_comparison_relation_preserved (x : Configuration) (v : x.1.reception.Node)
    (c : Token x.2.schema .clock) (d : Token x.2.schema .detector)
    (hc : c ∈ (x.2.arrival v .clock).dom) (hd : d ∈ (x.2.arrival v .detector).dom) :
    (c,d) ∈ x.2.sourceRelation ↔
      ((x.2.arrival v .clock).val c hc, (x.2.arrival v .detector).val d hd)
        ∈ x.2.comparisonRelation v := x.2.relationCompatibility v c d hc hd

theorem source_orders_preserved (x : Configuration) :
    (∀ c d, (sourceClockOrder x.2.schema).le c d ↔ c.1 = d.1 ∧ c.2 ≤ d.2) ∧
    (∀ c d, (sourceDetectorOrder x.2.schema).le c d ↔
      c = d ∨ x.2.schema.sequence c < x.2.schema.sequence d) :=
  ⟨fun _ _ => Iff.rfl, detector_order_exact x.2.schema⟩

theorem record_cell_partition_retained (x : Configuration) :
    (∀ t, (x.2.schema.cell t).Finite) ∧
    (∀ t, t ∈ x.2.schema.cell t) ∧
    (∀ a b t, t ∈ x.2.schema.cell a → t ∈ x.2.schema.cell b →
      x.2.schema.cell a = x.2.schema.cell b) := by
  refine ⟨x.2.schema.cell_finite, x.2.schema.cell_self, ?_⟩
  intro a b t ha hb
  exact ((x.2.schema.cell_class a t).mp ha).symm.trans ((x.2.schema.cell_class b t).mp hb)

theorem equal_display_retains_source_incomparability (x : Configuration)
    (c d : Token x.2.schema .clock) (different : c.1 ≠ d.1)
    (_same : x.2.schema.clockDisplay c = x.2.schema.clockDisplay d) :
    ¬ (sourceClockOrder x.2.schema).le c d ∧ ¬ (sourceClockOrder x.2.schema).le d c :=
  ch03_r042_c_distinct_sources_incomparable different

end LCTR.CoreOperationalConfiguration
