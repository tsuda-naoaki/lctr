import CoreEngineeringEvidence
import Mathlib.Data.Set.SymmDiff

namespace LCTR.CoreRecordBurden
set_option autoImplicit false
open Set LCTR.CoreTokenGraph LCTR.CoreStructuralBurden LCTR.CoreEngineeringEvidence
universe u w z

inductive RecordTag where
  | view | configuration | invasiveness | countStep | stability | cellWidth
  | discernibility | communication | coupling
  deriving DecidableEq

def bulkTags : Set RecordTag :=
  {.view,.configuration,.invasiveness,.countStep,.stability,.cellWidth,.discernibility}
def followingTags : Set RecordTag := bulkTags ∪ {.communication,.coupling}
def allowed (a : Fin 2) : Set RecordTag := if a=0 then bulkTags else followingTags

structure Configuration (Ref : Type u) (Value : Type w) (Cert : Type z) where
  tag : Ref → RecordTag
  targetInput : Fin 2 → Input Ref RecordTag Value Cert
  sameTags : ∀ k r, (targetInput k).tag r=tag r

variable {Ref : Type u} {Value : Type w} {Cert : Type z}

abbrev IndexedEvidence (d : Configuration Ref Value Cert) :=
  (k : Fin 2) × Verified (d.targetInput k)

def hasBurdenRef (a : Fin 2) (d : Configuration Ref Value Cert)
    (e : IndexedEvidence d) : Prop :=
  ∃ r ∈ e.2.val.refs, d.tag r ∈ allowed a

noncomputable def tokens (a : Fin 2) (d : Configuration Ref Value Cert) : Set Token :=
  (fun e : IndexedEvidence d => e.2.val.target) ''
    {e | hasBurdenRef a d e ∧ state (d.targetInput e.1) e.2=.fail}

noncomputable def recordBurden (a : Fin 2) (d : Configuration Ref Value Cert) : Set StructTok :=
  nativeBurden (tokens a d)

theorem tag_domains : bulkTags ⊆ followingTags := Set.subset_union_left

theorem bulk_omits_communication : RecordTag.communication ∉ bulkTags := by
  simp [bulkTags]

theorem following_includes_communication : RecordTag.communication ∈ followingTags := by
  simp [followingTags]

theorem token_witness (a : Fin 2) (d : Configuration Ref Value Cert) (t : Token) :
    t ∈ tokens a d ↔ ∃ k, ∃ e : Verified (d.targetInput k),
      (∃ r ∈ e.val.refs, d.tag r ∈ allowed a) ∧
      state (d.targetInput k) e=.fail ∧ e.val.target=t := by
  constructor
  · rintro ⟨⟨k,e⟩,⟨hr,hs⟩,ht⟩
    exact ⟨k,e,hr,hs,ht⟩
  · rintro ⟨k,e,hr,hs,ht⟩
    exact ⟨⟨k,e⟩,⟨hr,hs⟩,ht⟩

theorem witness_measurement_typed (a : Fin 2) (d : Configuration Ref Value Cert)
    (e : IndexedEvidence d) (h : hasBurdenRef a d e) :
    ∃ r ∈ e.2.val.refs, d.tag r ∈ allowed a ∧
      (d.targetInput e.1).measure r ∈ (d.targetInput e.1).valueType (d.tag r) := by
  obtain ⟨r,hr,ht⟩ := h
  refine ⟨r,hr,ht,?_⟩
  rw [← d.sameTags e.1 r]
  exact measurements_typed _ e.2 r hr

theorem token_target_locality (a : Fin 2) (d : Configuration Ref Value Cert) :
    tokens a d ⊆ ⋃ k : Fin 2, failTokens (d.targetInput k) := by
  intro t ht
  obtain ⟨k,e,_,hs,he⟩ := (token_witness a d t).mp ht
  exact Set.mem_iUnion.mpr ⟨k,e,hs,he⟩

theorem burden_equal_iff_delta_empty (d : Fin 2 → Configuration Ref Value Cert) :
    recordBurden 0 (d 0)=recordBurden 1 (d 1) ↔
      symmDiff (recordBurden 0 (d 0)) (recordBurden 1 (d 1))=∅ :=
  Set.symmDiff_eq_empty.symm

theorem singleton_burden_included (a : Fin 2) (d : Configuration Ref Value Cert)
    {t : Token} (ht : t ∈ tokens a d) :
    nativeBurden {t} ⊆ recordBurden a d :=
  root_burden_subset (Relation.ReflTransGen Edge) structOf ht

theorem one_sided_separation (a b : Fin 2) (d e : Configuration Ref Value Cert)
    {t : Token} (ht : t ∈ tokens a d)
    (hs : ¬ nativeBurden {t} ⊆ recordBurden b e) :
    (recordBurden a d \ recordBurden b e).Nonempty :=
  burden_separation (Relation.ReflTransGen Edge) structOf ht hs

theorem two_sided_incomparability (d : Fin 2 → Configuration Ref Value Cert)
    (h0 : ∃ t ∈ tokens 0 (d 0), ¬ nativeBurden {t} ⊆ recordBurden 1 (d 1))
    (h1 : ∃ t ∈ tokens 1 (d 1), ¬ nativeBurden {t} ⊆ recordBurden 0 (d 0)) :
    ¬ recordBurden 0 (d 0) ⊆ recordBurden 1 (d 1) ∧
    ¬ recordBurden 1 (d 1) ⊆ recordBurden 0 (d 0) := by
  obtain ⟨t0,ht0,hs0⟩ := h0
  obtain ⟨t1,ht1,hs1⟩ := h1
  obtain ⟨x,hx,hnx⟩ := one_sided_separation 0 1 (d 0) (d 1) ht0 hs0
  obtain ⟨y,hy,hny⟩ := one_sided_separation 1 0 (d 1) (d 0) ht1 hs1
  exact ⟨fun h => hnx (h hx),fun h => hny (h hy)⟩

theorem no_failed_evidence_no_tokens (a : Fin 2) (d : Configuration Ref Value Cert)
    (h : ∀ k (e : Verified (d.targetInput k)), state (d.targetInput k) e ≠ .fail) :
    tokens a d=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro t ht
  obtain ⟨k,e,_,hs,_⟩ := (token_witness a d t).mp ht
  exact h k e hs

theorem no_failed_evidence_no_burden (a : Fin 2) (d : Configuration Ref Value Cert)
    (h : ∀ k (e : Verified (d.targetInput k)), state (d.targetInput k) e ≠ .fail) :
    recordBurden a d=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro s ⟨t,ht,_,_,_⟩
  rw [no_failed_evidence_no_tokens a d h] at ht
  exact ht

theorem tag_difference_alone_not_burden_difference (d : Fin 2 → Configuration Ref Value Cert)
    (h : ∀ a k (e : Verified ((d a).targetInput k)), state ((d a).targetInput k) e ≠ .fail) :
    recordBurden 0 (d 0)=recordBurden 1 (d 1) := by
  rw [no_failed_evidence_no_burden 0 (d 0) (h 0),
    no_failed_evidence_no_burden 1 (d 1) (h 1)]

end LCTR.CoreRecordBurden
