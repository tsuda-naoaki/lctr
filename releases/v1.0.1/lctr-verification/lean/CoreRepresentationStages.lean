import CoreExactStructure
import BrokenPremiseNegative

namespace LCTR.CoreRepresentationStages
open Set LCTR.Chapter03SourceOrderRecovery LCTR.CoreSourceMatch
open LCTR.CoreComparisonIntegration LCTR.CorePreorderQuotient LCTR.CoreExactStructure
open LCTR.TransitiveIncomparabilityQuotientCore
universe u v w
set_option autoImplicit false

structure Base (U : Type u) (S : Type v) (V : U → Type w) where
  arrival : ∀ i, PartialArrival S (V i)
  unique : L1 arrival
  transport : ∀ i j, ImageAt arrival i → ImageAt arrival j → Prop
  admissible : U → U → Prop
  transportInjective : TransportPartialInjection arrival transport admissible
  sourceOrder : S → S → Prop
  refl : ReflRel sourceOrder
  trans : TransRel sourceOrder
  anti : AntiRel sourceOrder

variable {U : Type u} {S : Type v} {V : U → Type w}

structure First (p : Base U S V) : Prop where
  descent : OrdDesc
    (LCTR.CoreTypedWords.orbitSetoid
      (comparisonSystem p.arrival p.unique p.transport p.admissible p.transportInjective))
    (Pullback (recover p.arrival p.unique) p.sourceOrder)

def atFirst (p : Base U S V) (h : First p) : Input U S V :=
  ⟨p.arrival,p.unique,p.transport,p.admissible,p.transportInjective,
    p.sourceOrder,p.refl,p.trans,p.anti,h.descent⟩

structure Second (p : Base U S V) : Prop where
  first : First p
  localInc : ∀ i, LocalInc (atFirst p first) i

structure Third (p : Base U S V) : Prop where
  second : Second p
  globalInc : GlobalInc (atFirst p second.first)

theorem condition_hierarchy (p : Base U S V) :
    (Third p → Second p) ∧ (Second p → First p) :=
  ⟨Third.second,Second.first⟩

theorem first_creates_actual_order (p : Base U S V) (h : First p) :
    ReflRel (canonicalOrder (atFirst p h)) ∧ TransRel (canonicalOrder (atFirst p h)) ∧
      AntiRel (canonicalOrder (atFirst p h)) := canonical_partial_order (atFirst p h)

theorem second_creates_actual_charts (p : Base U S V) (h : Second p) (i : U) :
    Function.Surjective (chart (atFirst p h.first) i (h.localInc i)) ∧
    (∀ a b, chart (atFirst p h.first) i (h.localInc i) a =
      chart (atFirst p h.first) i (h.localInc i) b ↔
      Inc (strictData (atFirst p h.first)).lt
        (canonicalProjection (atFirst p h.first) ⟨i,a⟩)
        (canonicalProjection (atFirst p h.first) ⟨i,b⟩)) :=
  ⟨(actual_local_chart_contract (atFirst p h.first) i (h.localInc i)).1,
    (actual_local_chart_contract (atFirst p h.first) i (h.localInc i)).2.1⟩

theorem third_creates_actual_embeddings (p : Base U S V) (h : Third p) (i : U) :
    Function.Injective (localGlobal (atFirst p h.second.first) i (h.second.localInc i) h.globalInc) ∧
    (∀ a, localGlobal (atFirst p h.second.first) i (h.second.localInc i) h.globalInc
      (chart (atFirst p h.second.first) i (h.second.localInc i) a) =
      globalProjection (atFirst p h.second.first) h.globalInc
        (canonicalProjection (atFirst p h.second.first) ⟨i,a⟩)) :=
  ⟨local_global_injective _ _ _ _, local_global_chart_commutes _ _ _ _⟩

def Exact (operative : Prop) (p : Base U S V) := operative ∧ Third p

theorem exact_condition_expansion (operative : Prop) (p : Base U S V) :
    Exact operative p ↔ operative ∧ ∃ h : First p,
      (∀ i, LocalInc (atFirst p h) i) ∧ GlobalInc (atFirst p h) := by
  constructor
  · rintro ⟨hop,h⟩
    exact ⟨hop,h.second.first,h.second.localInc,h.globalInc⟩
  · rintro ⟨hop,h,hl,hg⟩
    exact ⟨hop,⟨⟨h,hl⟩,hg⟩⟩

theorem exact_preserves_comparison_gate (operative : Prop) (p : Base U S V)
    (h : Exact operative p) : operative := h.1

noncomputable def stageOnePayload (p : Base U S V) (h : First p) :=
  (canonicalOrder (atFirst p h), strictData (atFirst p h), localCarrier (atFirst p h))

noncomputable def stageTwoPayload (p : Base U S V) (h : Second p) :=
  (stageOnePayload p h.first,
    (fun i => chart (atFirst p h.first) i (h.localInc i)),
    (fun i j => LCTR.CoreOrderAtlas.overlapChange (strictData (atFirst p h.first))
      (localDomain (atFirst p h.first) i (h.localInc i))
      (localDomain (atFirst p h.first) j (h.localInc j))))

noncomputable def stageThreePayload (p : Base U S V) (h : Third p) :=
  (stageTwoPayload p h.second, globalProjection (atFirst p h.second.first) h.globalInc,
    (fun i => localGlobal (atFirst p h.second.first) i (h.second.localInc i) h.globalInc))

theorem first_payload_retained (p : Base U S V) (h : Second p) :
    (stageTwoPayload p h).1 = stageOnePayload p h.first := rfl

theorem second_payload_retained (p : Base U S V) (h : Third p) :
    (stageThreePayload p h).1 = stageTwoPayload p h.second := rfl

theorem original_payload_retained (p : Base U S V) (h : Third p) :
    (stageThreePayload p h).1.1 = stageOnePayload p h.second.first := rfl

open LCTR.OrderEmbeddingBridgeV1.Negative

def controlStrict : LCTR.CoreOrderAtlas.StrictData (Fin 3) :=
  ⟨brokenStrict, brokenStrict_irreflexive, brokenStrict_transitive⟩

def controlCarrier (i : Bool) : Set (Fin 3) :=
  {x | if i then x.val ≠ 0 else x.val ≠ 2}

theorem control_local_strict_empty (i : Bool) (x y : controlCarrier i) :
    ¬ brokenStrict x.val y.val := by
  cases i with
  | false => exact fun h => y.property h.2
  | true => exact fun h => x.property h.1

def controlDomain (i : Bool) : LCTR.CoreOrderAtlas.Domain controlStrict where
  carrier := controlCarrier i
  incTrans := fun _ _ => ⟨control_local_strict_empty _ _ _,control_local_strict_empty _ _ _⟩

theorem control_domains_cover : ∀ x : Fin 3, ∃ i : Bool, x ∈ controlCarrier i := by
  intro x
  by_cases h : x.val = 2
  · exact ⟨true, by change x.val ≠ 0; omega⟩
  · exact ⟨false,h⟩

theorem control_domains_overlap : ∃ x : Fin 3, x ∈ controlCarrier false ∧ x ∈ controlCarrier true :=
  ⟨1,by change (1 : Fin 3).val ≠ 2; decide,by change (1 : Fin 3).val ≠ 0; decide⟩

theorem local_cover_does_not_force_global_inc :
    (∀ x : Fin 3, ∃ i : Bool, x ∈ (controlDomain i).carrier) ∧
    (∀ i, ∀ {x y z : (controlDomain i).carrier},
      Inc (LCTR.CoreOrderAtlas.restricted controlStrict (controlDomain i)) x y →
      Inc (LCTR.CoreOrderAtlas.restricted controlStrict (controlDomain i)) y z →
      Inc (LCTR.CoreOrderAtlas.restricted controlStrict (controlDomain i)) x z) ∧
    ¬ (∀ {x y z : Fin 3}, Inc brokenStrict x y → Inc brokenStrict y z → Inc brokenStrict x z) :=
  ⟨control_domains_cover, fun i => (controlDomain i).incTrans,
    brokenStrict_incomparability_not_transitive⟩

end LCTR.CoreRepresentationStages
