import CoreOperationalConfiguration

namespace LCTR.CoreDetectorSourceBridge
set_option autoImplicit false
open LCTR.CoreCarrierPatterns LCTR.CoreOperationalConfiguration
open LCTR.Chapter03SourceOrderRecovery
universe u

def RecordIdentity {a : Input.{u}} (s : SourceSchema a) : Prop :=
  Function.Injective (fun t => (s.detectorDisplay t, s.sequence t))

structure ExactSourceData (raw : Raw) extends SourceData raw where
  recordIdentity : RecordIdentity schema

def contentEmbedding {a : Input.{u}} (s : SourceSchema a) (t : s.DetectorToken) :
    DToken s.DetectorLabel := ⟨s.detectorDisplay t, s.sequence t⟩

theorem record_identity_exact {a : Input.{u}} (s : SourceSchema a)
    (h : RecordIdentity s) (x y : s.DetectorToken) :
    x = y ↔ s.detectorDisplay x = s.detectorDisplay y ∧ s.sequence x = s.sequence y := by
  constructor
  · intro e; subst y; exact ⟨rfl,rfl⟩
  · rintro ⟨hc,hs⟩; exact h (Prod.ext hc hs)

theorem content_embedding_injective {a : Input.{u}} (s : SourceSchema a)
    (h : RecordIdentity s) : Function.Injective (contentEmbedding s) := by
  intro x y e
  exact h (Prod.ext (congrArg DToken.identity e) (congrArg DToken.seq e))

theorem content_order_exact {a : Input.{u}} (s : SourceSchema a)
    (h : RecordIdentity s) (x y : s.DetectorToken) :
    DLE (contentEmbedding s x) (contentEmbedding s y) ↔ detectorOrder s x y := by
  rw [detector_order_exact]
  change (contentEmbedding s x = contentEmbedding s y ∨ s.sequence x < s.sequence y) ↔ _
  constructor
  · rintro (e | lt)
    · exact Or.inl (content_embedding_injective s h e)
    · exact Or.inr lt
  · rintro (e | lt)
    · exact Or.inl (congrArg (contentEmbedding s) e)
    · exact Or.inr lt

theorem equal_counter_distinct_content {a : Input.{u}} (s : SourceSchema a)
    (h : RecordIdentity s) (x y : s.DetectorToken)
    (different : x ≠ y) (same : s.sequence x = s.sequence y) :
    s.detectorDisplay x ≠ s.detectorDisplay y := by
  intro hc
  exact different ((record_identity_exact s h x y).mpr ⟨hc,same⟩)

theorem recovery_preserves_record_content (x : Configuration) (v : x.1.reception.Node)
    (t : x.2.schema.DetectorToken) (ht : t ∈ (x.2.arrival v .detector).dom)
    (hu : UniqueRecoverable (x.2.arrival v .detector) ((x.2.arrival v .detector).val t ht)) :
    x.2.schema.detectorDisplay (recovery x v .detector ⟨(x.2.arrival v .detector).val t ht, hu⟩)
      = x.2.schema.detectorDisplay t ∧
    x.2.schema.sequence (recovery x v .detector ⟨(x.2.arrival v .detector).val t ht, hu⟩)
      = x.2.schema.sequence t := by
  rw [recovery_returns_original x v .detector t ht hu]
  exact ⟨rfl,rfl⟩

theorem pairing_retains_identity (raw : Raw) (s : ExactSourceData raw) :
    (make raw s.toSourceData).1 = raw ∧
    (make raw s.toSourceData).2 = s.toSourceData ∧
    RecordIdentity (make raw s.toSourceData).2.schema :=
  ⟨rfl,rfl,s.recordIdentity⟩

theorem missing_identity_control :
    ∃ content : Bool → Unit, ∃ seq : Bool → Nat,
      false ≠ true ∧ content false = content true ∧ seq false = seq true := by
  exact ⟨fun _ => (),fun _ => 0,Bool.false_ne_true,rfl,rfl⟩

end LCTR.CoreDetectorSourceBridge
