import CoreAuditGroups
import CoreStructuralBurden

namespace LCTR.CoreEngineeringEvidence
set_option autoImplicit false
open Set LCTR.CoreTokenGraph LCTR.CoreAuditStateTransport LCTR.CoreAuditGroups
open LCTR.CoreFiniteAudit LCTR.CoreStructuralBurden LCTR.SelectedInputEvaluation
universe u v w z

structure Input (Ref : Type u) (Tag : Type v) (Value : Type w) (Cert : Type z) where
  tag : Ref → Tag
  measure : Ref → Value
  valueType : Tag → Set Value
  ConditionEvidence : Token → Type
  evidence : (t : Token) → ConditionEvidence t
  certificate : Cert
  necessary : (t : Token) → ConditionEvidence t → Prop
  corresponds : Set Ref → (t : Token) → ConditionEvidence t → Cert → Prop
  formed : Token → Bool
  evaluated : Token → Bool
  condition : Token → Bool

structure Evidence {Ref : Type u} {Tag : Type v} {Value : Type w} {Cert : Type z}
    (d : Input Ref Tag Value Cert) where
  target : Token
  refs : Set Ref
  refs_nonempty : refs.Nonempty

variable {Ref : Type u} {Tag : Type v} {Value : Type w} {Cert : Type z}

def valid (d : Input Ref Tag Value Cert) (e : Evidence d) : Prop :=
  (∀ r ∈ e.refs, d.measure r ∈ d.valueType (d.tag r)) ∧
  d.necessary e.target (d.evidence e.target) ∧
  d.corresponds e.refs e.target (d.evidence e.target) d.certificate

abbrev Verified (d : Input Ref Tag Value Cert) := {e : Evidence d // valid d e}

noncomputable def state (d : Input Ref Tag Value Cert) (e : Verified d) : AuditStatus :=
  auditOutput d.formed d.evaluated d.condition e.val.target

noncomputable def failedEvidence (d : Input Ref Tag Value Cert) : Set (Verified d) :=
  {e | state d e=.fail}

noncomputable def failTokens (d : Input Ref Tag Value Cert) : Set Token :=
  (fun e : Verified d => e.val.target) '' failedEvidence d

theorem references_nonempty (d : Input Ref Tag Value Cert) (e : Verified d) :
    e.val.refs.Nonempty := e.val.refs_nonempty

theorem measurements_typed (d : Input Ref Tag Value Cert) (e : Verified d) :
    ∀ r ∈ e.val.refs, d.measure r ∈ d.valueType (d.tag r) := e.property.1

theorem condition_evidence_required (d : Input Ref Tag Value Cert) (e : Verified d) :
    d.necessary e.val.target (d.evidence e.val.target) := e.property.2.1

theorem certificate_correspondence (d : Input Ref Tag Value Cert) (e : Verified d) :
    d.corresponds e.val.refs e.val.target (d.evidence e.val.target) d.certificate :=
  e.property.2.2

theorem state_is_target_state (d : Input Ref Tag Value Cert) (e : Verified d) :
    state d e=auditOutput d.formed d.evaluated d.condition e.val.target := rfl

theorem fail_iff_native_failed (d : Input Ref Tag Value Cert) (e : Verified d) :
    state d e=.fail ↔ run d.formed d.evaluated d.condition 40 e.val.target=.failed :=
  Set.ext_iff.mp (native_failed_fiber d.formed d.evaluated d.condition) e.val.target

theorem target_image_exact (d : Input Ref Tag Value Cert) (t : Token) :
    t ∈ failTokens d ↔ ∃ e : Verified d, state d e=.fail ∧ e.val.target=t := Iff.rfl

theorem failure_image_localized (d : Input Ref Tag Value Cert) :
    failTokens d ⊆ {t | auditOutput d.formed d.evaluated d.condition t=.fail} := by
  rintro t ⟨e,he,rfl⟩
  exact he

theorem six_series_locality (d : Input Ref Tag Value Cert) :
    failTokens d ⊆ ⋃ i : Fin 6, {t : Token | t.1=i} := by
  intro t _
  exact Set.mem_iUnion.mpr ⟨t.1,rfl⟩

theorem shared_reference_targets (d : Input Ref Tag Value Cert) (r : Ref)
    (es : Fin 2 → Verified d)
    (h : ∀ j, r ∈ (es j).val.refs ∧ state d (es j)=.fail) :
    Set.range (fun j => (es j).val.target) ⊆ failTokens d := by
  rintro t ⟨j,rfl⟩
  exact ⟨es j,(h j).2,rfl⟩

theorem relative_burden_unique (d : Input Ref Tag Value Cert) (e : Verified d) :
    ∃! p : Set Ref × Set StructTok,
      p.1=e.val.refs ∧ p.2=nativeBurden {e.val.target} := by
  refine ⟨⟨e.val.refs,nativeBurden {e.val.target}⟩,⟨rfl,rfl⟩,?_⟩
  intro p hp
  exact Prod.ext hp.1 hp.2

theorem satisfied_target_is_not_failed (d : Input Ref Tag Value Cert) (e : Verified d)
    (h : run d.formed d.evaluated d.condition 40 e.val.target=.sat) :
    state d e=.pass ∧ e ∉ failedEvidence d := by
  have hp : state d e=.pass :=
    (native_pass_iff d.formed d.evaluated d.condition e.val.target).mpr h
  refine ⟨hp,?_⟩
  change state d e ≠ .fail
  rw [hp]
  decide

end LCTR.CoreEngineeringEvidence
