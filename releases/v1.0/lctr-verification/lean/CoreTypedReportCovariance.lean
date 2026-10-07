import CoreAuditData
import CoreReportCovariance

namespace LCTR.CoreTypedReportCovariance
set_option autoImplicit false
open LCTR.CoreTokenGraph LCTR.CoreStructuralBurden LCTR.CoreAuditReport
open LCTR.CoreAuditData LCTR.CoreReportCovariance
universe u v w z

structure CertificateMaps (S : Schema.{u}) (T : Schema.{v}) where
  inputID : S.InputID ≃ T.InputID
  evidenceID : S.EvidenceID ≃ T.EvidenceID
  contentHash : S.ContentHash ≃ T.ContentHash
  transformTrace : S.TransformTrace ≃ T.TransformTrace
  evidenceLocation : S.EvidenceLocation ≃ T.EvidenceLocation

def certificateEquiv {S : Schema.{u}} {T : Schema.{v}} (m : CertificateMaps S T) :
    Certificate S ≃ Certificate T where
  toFun p := ⟨m.inputID p.inputID,m.evidenceID p.evidenceID,m.contentHash p.contentHash,
    m.transformTrace p.transformTrace,m.evidenceLocation p.evidenceLocation⟩
  invFun p := ⟨m.inputID.symm p.inputID,m.evidenceID.symm p.evidenceID,m.contentHash.symm p.contentHash,
    m.transformTrace.symm p.transformTrace,m.evidenceLocation.symm p.evidenceLocation⟩
  left_inv p := by cases p; simp only [Equiv.symm_apply_apply]
  right_inv p := by cases p; simp only [Equiv.apply_symm_apply]

structure CoreMaps (S : Schema.{u}) (T : Schema.{v}) where
  contract : S.ContractID ≃ T.ContractID
  input : Input S ≃ Input T
  evidence : Evidence S ≃ Evidence T
  scaleData : S.ScaleData ≃ T.ScaleData

def coreEquiv {S : Schema.{u}} {T : Schema.{v}} (m : CoreMaps S T) : Core S ≃ Core T where
  toFun p := ⟨m.contract p.contract,m.input p.input,m.evidence p.evidence,m.scaleData p.scaleData⟩
  invFun p := ⟨m.contract.symm p.contract,m.input.symm p.input,m.evidence.symm p.evidence,m.scaleData.symm p.scaleData⟩
  left_inv p := by cases p; simp only [Equiv.symm_apply_apply]
  right_inv p := by cases p; simp only [Equiv.apply_symm_apply]

def dataEquiv {S : Schema.{u}} {T : Schema.{v}} (m : CoreMaps S T) (p : CertificateMaps S T) :
    Data S ≃ Data T where
  toFun a := ⟨coreEquiv m a.core,certificateEquiv p a.certificate⟩
  invFun a := ⟨(coreEquiv m).symm a.core,(certificateEquiv p).symm a.certificate⟩
  left_inv a := by cases a; simp only [Equiv.symm_apply_apply]
  right_inv a := by cases a; simp only [Equiv.apply_symm_apply]

theorem certificate_correspondence_exact {S : Schema.{u}} {T : Schema.{v}}
    (m : CoreMaps S T) (p : CertificateMaps S T) (a : Data S) :
    (dataEquiv m p a).certificate=certificateEquiv p a.certificate := rfl

theorem data_equivalence_injective {S : Schema.{u}} {T : Schema.{v}}
    (m : CoreMaps S T) (p : CertificateMaps S T) : Function.Injective (dataEquiv m p) :=
  (dataEquiv m p).injective

structure Correspondence {S : Schema.{u}} {T : Schema.{v}} {B : Type w} {C : Type z}
    (m : CoreMaps S T) (left : EvaluationContract S B) (right : EvaluationContract T C) where
  scale : S.Scale ≃ T.Scale
  tokens : Token ≃ Token
  structures : StructTok ≃ StructTok
  boundaries : B ≃ C
  series : ∀ a, (tokens a).1=a.1
  edges : ∀ a b, Edge a b ↔ Edge (tokens a) (tokens b)
  targets : ∀ a, structures (structOf a)=structOf (tokens a)
  formed : ∀ core ell a, right.formed (coreEquiv m core) (scale ell) (tokens a)=left.formed core ell a
  evaluable : ∀ core ell a, right.evaluable (coreEquiv m core) (scale ell) (tokens a)=left.evaluable core ell a
  condition : ∀ core ell a, right.condition (coreEquiv m core) (scale ell) (tokens a)=left.condition core ell a
  boundary : ∀ core, right.boundary (coreEquiv m core)=boundaries (left.boundary core)
  boundaryRoots : ∀ core, right.boundaryRoots (coreEquiv m core)=
    (left.boundaryRoots core).map (fun F => tokens '' F)

theorem typed_readout_covariance {S : Schema.{u}} {T : Schema.{v}} {B : Type w} {C : Type z}
    (m : CoreMaps S T) (p : CertificateMaps S T)
    (left : EvaluationContract S B) (right : EvaluationContract T C)
    (h : Correspondence m left right) (a : Data S) (scale : S.Scale) :
    reportEquiv (dataEquiv m p) h.tokens h.structures h.boundaries (readout left a scale)=
      readout right (dataEquiv m p a) (h.scale scale) := by
  have result := native_report_covariance (dataEquiv m p) h.tokens h.structures h.boundaries
    h.series h.edges h.targets (left.formed a.core scale) (left.evaluable a.core scale)
    (left.condition a.core scale) (right.formed (coreEquiv m a.core) (h.scale scale))
    (right.evaluable (coreEquiv m a.core) (h.scale scale))
    (right.condition (coreEquiv m a.core) (h.scale scale))
    (h.formed a.core scale) (h.evaluable a.core scale) (h.condition a.core scale)
    a (left.boundary a.core) (left.boundaryRoots a.core)
  rw [← h.boundary a.core,← h.boundaryRoots a.core] at result
  exact result

theorem report_equivalence_unique_with_component_maps
    {S : Schema.{u}} {T : Schema.{v}} {B : Type w} {C : Type z}
    (m : CoreMaps S T) (p : CertificateMaps S T)
    (left : EvaluationContract S B) (right : EvaluationContract T C)
    (h : Correspondence m left right)
    (e : Report (Data S) B ≃ Report (Data T) C)
    (hd : ∀ r, (e r).data=dataEquiv m p r.data)
    (hs : ∀ r, (e r).states=stateEquiv h.tokens r.states)
    (hg : ∀ r, (e r).diagnostics=diagnosticEquiv h.tokens h.structures h.boundaries r.diagnostics) :
    e=reportEquiv (dataEquiv m p) h.tokens h.structures h.boundaries :=
  induced_report_equiv_unique _ _ _ _ e hd hs hg

theorem transformed_certificate_fields {S : Schema.{u}} {T : Schema.{v}} {B : Type w} {C : Type z}
    (m : CoreMaps S T) (p : CertificateMaps S T)
    (left : EvaluationContract S B) (right : EvaluationContract T C)
    (h : Correspondence m left right) (a : Data S) (scale : S.Scale) :
    let cert := (readout right (dataEquiv m p a) (h.scale scale)).data.certificate
    cert.inputID=p.inputID a.certificate.inputID ∧ cert.evidenceID=p.evidenceID a.certificate.evidenceID ∧
    cert.contentHash=p.contentHash a.certificate.contentHash ∧
    cert.transformTrace=p.transformTrace a.certificate.transformTrace ∧
    cert.evidenceLocation=p.evidenceLocation a.certificate.evidenceLocation := ⟨rfl,rfl,rfl,rfl,rfl⟩

end LCTR.CoreTypedReportCovariance
