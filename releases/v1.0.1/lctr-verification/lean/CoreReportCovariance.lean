import CoreAuditReport

namespace LCTR.CoreReportCovariance
set_option autoImplicit false
open Set LCTR.CoreTokenGraph LCTR.CoreAuditStateTransport LCTR.CoreAuditTags
open LCTR.CoreAuditGroups LCTR.CoreFiniteAudit LCTR.CoreEvaluation LCTR.CoreStructuralBurden
open LCTR.CoreAuditReport
universe u v w z

def setEquiv {A : Type u} {B : Type v} (e : A ≃ B) : Set A ≃ Set B where
  toFun S := e '' S
  invFun S := e.symm '' S
  left_inv := e.symm_image_image
  right_inv := e.symm.symm_image_image

theorem function_transport {Y : Type u} (c : Token ≃ Token)
    (s t : Token → Y) (hs : ∀ a, t (c a)=s a) :
    c.arrowCongr (Equiv.refl Y) s=t := by
  funext a
  exact (hs (c.symm a)).symm.trans (congrArg t (c.apply_symm_apply a))

def stateEquiv (c : Token ≃ Token) : StateReport ≃ StateReport where
  toFun r := ⟨r.groups,c.arrowCongr (Equiv.refl _) r.conditions,
    setEquiv c r.indeterminate,c.arrowCongr (Equiv.refl _) r.indeterminateSignature,
    setEquiv (reasonEquiv c) r.undefinedReasons⟩
  invFun r := ⟨r.groups,(c.arrowCongr (Equiv.refl _)).symm r.conditions,
    (setEquiv c).symm r.indeterminate,(c.arrowCongr (Equiv.refl _)).symm r.indeterminateSignature,
    (setEquiv (reasonEquiv c)).symm r.undefinedReasons⟩
  left_inv r := by cases r; simp only [Equiv.symm_apply_apply]
  right_inv r := by cases r; simp only [Equiv.apply_symm_apply]

theorem state_report_transport (c : Token ≃ Token) (series : ∀ a, (c a).1=a.1)
    (s t : Token → AuditStatus) (hs : ∀ a, t (c a)=s a) :
    stateEquiv c (stateReport s)=stateReport t := by
  change StateReport.mk _ _ _ _ _ = StateReport.mk _ _ _ _ _
  congr 1
  · funext i
    exact (group_status_covariance c (Equiv.refl _) series s t hs i).symm
  · exact function_transport c s t hs
  · exact audit_fiber_image c s t hs .indeterminate
  · exact function_transport c _ _ (indeterminate_signature_covariance c s t hs)
  · exact reasons_transport c s t hs

def diagnosticEquiv {B : Type u} {C : Type v}
    (c : Token ≃ Token) (d : StructTok ≃ StructTok) (b : B ≃ C) :
    DiagnosticReport B ≃ DiagnosticReport C where
  toFun r := ⟨taggedEquiv (setEquiv c) c r.failedPosition,
    taggedEquiv (c.arrowCongr (Equiv.refl Bool)) c r.failureSignature,
    taggedEquiv b c r.approximationBoundary,
    taggedEquiv ((setEquiv d).prodCongr (setEquiv d)) c r.structuralBurden⟩
  invFun r := ⟨(taggedEquiv (setEquiv c) c).symm r.failedPosition,
    (taggedEquiv (c.arrowCongr (Equiv.refl Bool)) c).symm r.failureSignature,
    (taggedEquiv b c).symm r.approximationBoundary,
    (taggedEquiv ((setEquiv d).prodCongr (setEquiv d)) c).symm r.structuralBurden⟩
  left_inv r := by cases r; simp only [Equiv.symm_apply_apply]
  right_inv r := by cases r; simp only [Equiv.apply_symm_apply]

theorem approximation_group_image (c : Token ≃ Token) (series : ∀ a, (c a).1=a.1) :
    c '' approxGroup=approxGroup := by
  ext t
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact (series a).trans ha
  · intro ht
    obtain ⟨a,rfl⟩ := c.surjective t
    exact ⟨a,(series a).symm.trans ht,rfl⟩

theorem burden_report_transport (c : Token ≃ Token) (d : StructTok ≃ StructTok)
    (edges : ∀ a b, Edge a b ↔ Edge (c a) (c b))
    (targets : ∀ a, d (structOf a)=structOf (c a))
    (s t : Token → AuditStatus) (hs : ∀ a, t (c a)=s a)
    (roots : Option (Set Token)) :
    (setEquiv d).prodCongr (setEquiv d) (LCTR.CoreStructuralBurden.report (failed s) roots)=
      LCTR.CoreStructuralBurden.report (failed t) (roots.map (fun F => c '' F)) := by
  apply Prod.ext
  · exact native_failed_burden_covariance c d edges targets s t hs
  · exact boundary_burden_covariance c d edges targets roots

theorem diagnostic_report_transport {B : Type u} {C : Type v}
    (c : Token ≃ Token) (d : StructTok ≃ StructTok) (b : B ≃ C)
    (series : ∀ a, (c a).1=a.1) (edges : ∀ a z, Edge a z ↔ Edge (c a) (c z))
    (targets : ∀ a, d (structOf a)=structOf (c a))
    (s t : Token → AuditStatus) (hs : ∀ a, t (c a)=s a)
    (boundary : B) (roots : Option (Set Token)) :
    diagnosticEquiv c d b (diagnostics s boundary roots)=
      diagnostics t (b boundary) (roots.map (fun F => c '' F)) := by
  change DiagnosticReport.mk _ _ _ _ = DiagnosticReport.mk _ _ _ _
  congr 1
  · exact generated_tagged_transport (setEquiv c) c (failed s) (failed t)
      (audit_fiber_image c s t hs .fail) s t hs
  · apply generated_tagged_transport _ c _ _ _ s t hs
    apply function_transport c
    intro a
    simp only [failureSignature,hs]
  · change taggedEquiv b c (tagged boundary (groupReasons s approxGroup)) = _
    rw [tagged_transport,group_reasons_transport c s t hs,approximation_group_image c series]
  · exact generated_tagged_transport _ c _ _ (burden_report_transport c d edges targets s t hs roots) s t hs

def reportEquiv {D : Type u} {E : Type v} {B : Type w} {C : Type z}
    (data : D ≃ E) (c : Token ≃ Token) (d : StructTok ≃ StructTok) (b : B ≃ C) :
    Report D B ≃ Report E C where
  toFun r := ⟨data r.data,stateEquiv c r.states,diagnosticEquiv c d b r.diagnostics⟩
  invFun r := ⟨data.symm r.data,(stateEquiv c).symm r.states,(diagnosticEquiv c d b).symm r.diagnostics⟩
  left_inv r := by cases r; simp only [Equiv.symm_apply_apply]
  right_inv r := by cases r; simp only [Equiv.apply_symm_apply]

theorem assembled_report_transport {D : Type u} {E : Type v} {B : Type w} {C : Type z}
    (data : D ≃ E) (c : Token ≃ Token) (d : StructTok ≃ StructTok) (b : B ≃ C)
    (series : ∀ a, (c a).1=a.1) (edges : ∀ a z, Edge a z ↔ Edge (c a) (c z))
    (targets : ∀ a, d (structOf a)=structOf (c a))
    (s t : Token → AuditStatus) (hs : ∀ a, t (c a)=s a)
    (input : D) (boundary : B) (roots : Option (Set Token)) :
    reportEquiv data c d b (assemble input s boundary roots)=
      assemble (data input) t (b boundary) (roots.map (fun F => c '' F)) := by
  change Report.mk _ _ _ = Report.mk _ _ _
  dsimp only [assemble]
  rw [state_report_transport c series s t hs,
    diagnostic_report_transport c d b series edges targets s t hs boundary roots]

theorem native_output_transport (c : Token ≃ Token)
    (edges : ∀ a b, Edge a b ↔ Edge (c a) (c b))
    (f0 e0 q0 f1 e1 q1 : Token → Bool)
    (forms : ∀ a, f1 (c a)=f0 a) (evals : ∀ a, e1 (c a)=e0 a)
    (conditions : ∀ a, q1 (c a)=q0 a) :
    ∀ a, auditOutput f1 e1 q1 (c a)=auditOutput f0 e0 q0 a := by
  have hs := state_covariance c Edge Edge
    (LCTR.CoreDagRecursion.finite_acyclic_wellFounded Edge acyclic) edges
    f0 e0 q0 f1 e1 q1 forms evals conditions _ _
    (finite_run_solves f0 e0 q0) (finite_run_solves f1 e1 q1)
  intro a
  rw [audit_output_eq_native,audit_output_eq_native]
  exact auditAt_covariance c Edge Edge edges _ _ hs a

theorem native_report_covariance {D : Type u} {E : Type v} {B : Type w} {C : Type z}
    (data : D ≃ E) (c : Token ≃ Token) (d : StructTok ≃ StructTok) (b : B ≃ C)
    (series : ∀ a, (c a).1=a.1) (edges : ∀ a z, Edge a z ↔ Edge (c a) (c z))
    (targets : ∀ a, d (structOf a)=structOf (c a))
    (f0 e0 q0 f1 e1 q1 : Token → Bool)
    (forms : ∀ a, f1 (c a)=f0 a) (evals : ∀ a, e1 (c a)=e0 a)
    (conditions : ∀ a, q1 (c a)=q0 a)
    (input : D) (boundary : B) (roots : Option (Set Token)) :
    reportEquiv data c d b (nativeReport input f0 e0 q0 boundary roots)=
      nativeReport (data input) f1 e1 q1 (b boundary) (roots.map (fun F => c '' F)) :=
  assembled_report_transport data c d b series edges targets _ _
    (native_output_transport c edges f0 e0 q0 f1 e1 q1 forms evals conditions) input boundary roots

theorem induced_report_equiv_unique {D : Type u} {E : Type v} {B : Type w} {C : Type z}
    (data : D ≃ E) (c : Token ≃ Token) (d : StructTok ≃ StructTok) (b : B ≃ C)
    (e : Report D B ≃ Report E C)
    (hd : ∀ r, (e r).data=data r.data)
    (hs : ∀ r, (e r).states=stateEquiv c r.states)
    (hg : ∀ r, (e r).diagnostics=diagnosticEquiv c d b r.diagnostics) :
    e=reportEquiv data c d b := by
  apply Equiv.ext
  intro r
  have hdata := hd r
  have hstate := hs r
  have hdiag := hg r
  change e r=Report.mk _ _ _
  generalize e r = result at *
  cases result
  simp_all only

end LCTR.CoreReportCovariance
