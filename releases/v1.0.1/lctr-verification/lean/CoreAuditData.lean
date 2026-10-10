import CoreAuditReport

namespace LCTR.CoreAuditData
set_option autoImplicit false
open LCTR.CoreTokenGraph LCTR.CoreFiniteAudit LCTR.CoreAuditReport
universe u v

structure Schema where
  ContractID : Type u
  Configuration : Type u
  Evaluation : Type u
  BranchType : Fin 3 → Type u
  InputReason : Type u
  Scale : Type u
  ScaleData : Type u
  EvidenceType : Token → Type u
  InputID : Type u
  EvidenceID : Type u
  ContentHash : Type u
  TransformTrace : Type u
  EvidenceLocation : Type u

def inputSeries (b : Fin 3) : Fin 6 := ⟨b.val+3,by omega⟩

theorem input_series_exact (i : Fin 6) :
    (∃ b, inputSeries b=i) ↔ i=3 ∨ i=4 ∨ i=5 := by
  constructor
  · rintro ⟨b,rfl⟩
    exact (show ∀ b : Fin 3, inputSeries b=3 ∨ inputSeries b=4 ∨ inputSeries b=5 from by decide) b
  · rintro (rfl|rfl|rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩

abbrev Branch (S : Schema.{u}) (b : Fin 3) := S.BranchType b ⊕ S.InputReason

def branchFormed {S : Schema.{u}} {b : Fin 3} : Branch S b → Bool
  | .inl _ => true
  | .inr _ => false

theorem formed_branch_exact {S : Schema.{u}} {b : Fin 3} (x : Branch S b) :
    branchFormed x=true ↔ ∃ y, x=.inl y := by
  cases x <;> simp [branchFormed]

theorem unformed_branch_exact {S : Schema.{u}} {b : Fin 3} (x : Branch S b) :
    branchFormed x=false ↔ ∃ reason, x=.inr reason := by
  cases x <;> simp [branchFormed]

structure Input (S : Schema.{u}) where
  configuration : S.Configuration
  evaluation : S.Evaluation
  branches : (b : Fin 3) → Branch S b

structure Evidence (S : Schema.{u}) where
  strict : (t : {t : Token // t.1≠3}) → S.EvidenceType t.val
  approximation : (scale : S.Scale) → (i : Fin (count 3)) → S.EvidenceType ⟨3,i⟩

def evidenceAt {S : Schema.{u}} (ev : Evidence S) (scale : S.Scale)
    (t : Token) : S.EvidenceType t := by
  rcases t with ⟨s,i⟩
  by_cases h : s=3
  · subst s
    exact ev.approximation scale i
  · exact ev.strict ⟨⟨s,i⟩,h⟩

theorem approximation_evidence_selected {S : Schema.{u}} (ev : Evidence S)
    (scale : S.Scale) (i : Fin (count 3)) :
    evidenceAt ev scale ⟨3,i⟩=ev.approximation scale i := by
  simp [evidenceAt]

theorem strict_evidence_scale_independent {S : Schema.{u}} (ev : Evidence S)
    (a b : S.Scale) (t : Token) (ht : t.1≠3) :
    evidenceAt ev a t=evidenceAt ev b t := by
  rcases t with ⟨s,i⟩
  simp only [evidenceAt,dif_neg ht]

structure Core (S : Schema.{u}) where
  contract : S.ContractID
  input : Input S
  evidence : Evidence S
  scaleData : S.ScaleData

structure Certificate (S : Schema.{u}) where
  inputID : S.InputID
  evidenceID : S.EvidenceID
  contentHash : S.ContentHash
  transformTrace : S.TransformTrace
  evidenceLocation : S.EvidenceLocation

structure Data (S : Schema.{u}) where
  core : Core S
  certificate : Certificate S

structure EvaluationContract (S : Schema.{u}) (B : Type v) where
  formed : Core S → S.Scale → Token → Bool
  evaluable : Core S → S.Scale → Token → Bool
  condition : Core S → S.Scale → Token → Bool
  boundary : Core S → B
  boundaryRoots : Core S → Option (Set Token)

noncomputable def readout {S : Schema.{u}} {B : Type v}
    (contract : EvaluationContract S B) (data : Data S) (scale : S.Scale) : Report (Data S) B :=
  nativeReport data (contract.formed data.core scale) (contract.evaluable data.core scale)
    (contract.condition data.core scale) (contract.boundary data.core) (contract.boundaryRoots data.core)

theorem readout_data_exact {S : Schema.{u}} {B : Type v}
    (contract : EvaluationContract S B) (data : Data S) (scale : S.Scale) :
    (readout contract data scale).data=data := rfl

theorem readout_certificate_exact {S : Schema.{u}} {B : Type v}
    (contract : EvaluationContract S B) (data : Data S) (scale : S.Scale) :
    (readout contract data scale).data.certificate=data.certificate := rfl

theorem certificate_fields_retained {S : Schema.{u}} {B : Type v}
    (contract : EvaluationContract S B) (data : Data S) (scale : S.Scale) :
    let result := (readout contract data scale).data.certificate
    result.inputID=data.certificate.inputID ∧ result.evidenceID=data.certificate.evidenceID ∧
    result.contentHash=data.certificate.contentHash ∧ result.transformTrace=data.certificate.transformTrace ∧
    result.evidenceLocation=data.certificate.evidenceLocation := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem certificate_does_not_change_computation {S : Schema.{u}} {B : Type v}
    (contract : EvaluationContract S B) (core : Core S)
    (a b : Certificate S) (scale : S.Scale) :
    (readout contract ⟨core,a⟩ scale).states=(readout contract ⟨core,b⟩ scale).states ∧
    (readout contract ⟨core,a⟩ scale).diagnostics=(readout contract ⟨core,b⟩ scale).diagnostics := ⟨rfl,rfl⟩

theorem different_certificates_remain_distinct {S : Schema.{u}} {B : Type v}
    (contract : EvaluationContract S B) (core : Core S)
    (a b : Certificate S) (hne : a≠b) (scale : S.Scale) :
    readout contract ⟨core,a⟩ scale ≠ readout contract ⟨core,b⟩ scale := by
  intro h
  exact hne (congrArg (fun r : Report (Data S) B => r.data.certificate) h)

theorem typed_report_unique {S : Schema.{u}} {B : Type v}
    (contract : EvaluationContract S B) (data : Data S) (scale : S.Scale) :
    ∃! r : Report (Data S) B,
      Generated data (contract.formed data.core scale) (contract.evaluable data.core scale)
        (contract.condition data.core scale) (contract.boundary data.core) (contract.boundaryRoots data.core) r :=
  native_report_unique _ _ _ _ _ _

end LCTR.CoreAuditData
