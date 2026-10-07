import CoreAuditGroups
import CoreStructuralBurden

namespace LCTR.CoreAuditReport
set_option autoImplicit false
open Set LCTR.CoreTokenGraph LCTR.CoreAuditStateTransport LCTR.CoreAuditTags
open LCTR.CoreAuditGroups LCTR.CoreFiniteAudit LCTR.CoreEvaluation LCTR.SelectedInputEvaluation
open LCTR.CoreStructuralBurden
universe u v

structure StateReport where
  groups : Fin 6 → AuditStatus
  conditions : Token → AuditStatus
  indeterminate : Set Token
  indeterminateSignature : Token → Bool
  undefinedReasons : Set (Reason Token)

structure DiagnosticReport (B : Type u) where
  failedPosition : Tagged (Set Token) Token
  failureSignature : Tagged (Token → Bool) Token
  approximationBoundary : Tagged B Token
  structuralBurden : Tagged (Set StructTok × Set StructTok) Token

structure Report (D : Type u) (B : Type v) where
  data : D
  states : StateReport
  diagnostics : DiagnosticReport B

def failed (s : Token → AuditStatus) : Set Token := {t | s t=.fail}
def failureSignature (s : Token → AuditStatus) (t : Token) : Bool := decide (s t=.fail)
def approxGroup : Set Token := {t | t.1=3}

def stateReport (s : Token → AuditStatus) : StateReport where
  groups := groupStatus s
  conditions := s
  indeterminate := {t | s t=.indeterminate}
  indeterminateSignature := fun t => decide (s t=.indeterminate)
  undefinedReasons := reasons s

noncomputable def diagnostics {B : Type u} (s : Token → AuditStatus)
    (boundary : B) (boundaryRoots : Option (Set Token)) : DiagnosticReport B where
  failedPosition := tagged (failed s) (reasons s)
  failureSignature := tagged (failureSignature s) (reasons s)
  approximationBoundary := tagged boundary (groupReasons s approxGroup)
  structuralBurden := tagged (LCTR.CoreStructuralBurden.report (failed s) boundaryRoots) (reasons s)

noncomputable def assemble {D : Type u} {B : Type v} (data : D) (s : Token → AuditStatus)
    (boundary : B) (boundaryRoots : Option (Set Token)) : Report D B :=
  ⟨data,stateReport s,diagnostics s boundary boundaryRoots⟩

noncomputable def nativeReport {D : Type u} {B : Type v} (data : D)
    (f e c : Token → Bool) (boundary : B) (boundaryRoots : Option (Set Token)) : Report D B :=
  assemble data (auditOutput f e c) boundary boundaryRoots

theorem union_group_reasons (s : Token → AuditStatus) :
    (⋃ i : Fin 6, groupReasons s {t | t.1=i})=reasons s := by
  ext p
  simp only [Set.mem_iUnion,groupReasons,reasons,Set.mem_ofPred_eq]
  exact ⟨fun ⟨_,_,h⟩ => h,fun h => ⟨p.1.1,rfl,h⟩⟩

theorem approximation_reasons_subset (s : Token → AuditStatus) :
    groupReasons s approxGroup ⊆ reasons s := fun _ h => h.2

theorem report_preserves_data {D : Type u} {B : Type v} (data : D)
    (f e c : Token → Bool) (boundary : B) (boundaryRoots : Option (Set Token)) :
    (nativeReport data f e c boundary boundaryRoots).data=data := rfl

theorem native_report_matches {D : Type u} {B : Type v} (data : D)
    (f e c : Token → Bool) (boundary : B) (boundaryRoots : Option (Set Token))
    (s : Token → State) (hs : Recurs Edge f e c s) :
    assemble data (auditAt Edge s) boundary boundaryRoots = nativeReport data f e c boundary boundaryRoots := by
  have h : auditAt Edge s=auditOutput f e c :=
    (funext (finite_audit_output_unique f e c s hs)).symm
  rw [h]
  rfl

theorem report_independent_of_solution {D : Type u} {B : Type v} (data : D)
    (f e c : Token → Bool) (boundary : B) (boundaryRoots : Option (Set Token))
    (s t : Token → State) (hs : Recurs Edge f e c s) (ht : Recurs Edge f e c t) :
    assemble data (auditAt Edge s) boundary boundaryRoots =
      assemble data (auditAt Edge t) boundary boundaryRoots :=
  (native_report_matches data f e c boundary boundaryRoots s hs).trans
    (native_report_matches data f e c boundary boundaryRoots t ht).symm

def Generated {D : Type u} {B : Type v} (data : D) (f e c : Token → Bool)
    (boundary : B) (boundaryRoots : Option (Set Token)) (r : Report D B) : Prop :=
  ∃ s : Token → State, Recurs Edge f e c s ∧ r=assemble data (auditAt Edge s) boundary boundaryRoots

theorem native_report_unique {D : Type u} {B : Type v} (data : D)
    (f e c : Token → Bool) (boundary : B) (boundaryRoots : Option (Set Token)) :
    ∃! r : Report D B, Generated data f e c boundary boundaryRoots r := by
  refine ⟨nativeReport data f e c boundary boundaryRoots,?_,?_⟩
  · refine ⟨run f e c 40,finite_run_solves f e c,?_⟩
    exact (native_report_matches data f e c boundary boundaryRoots _ (finite_run_solves f e c)).symm
  · rintro r ⟨s,hs,hr⟩
    exact hr.trans (native_report_matches data f e c boundary boundaryRoots s hs)

theorem native_group_maximum {D : Type u} {B : Type v} (data : D)
    (f e c : Token → Bool) (boundary : B) (boundaryRoots : Option (Set Token)) (i : Fin 6) :
    ∀ t ∈ groupTokens i, priority ((nativeReport data f e c boundary boundaryRoots).states.conditions t) ≤
      priority ((nativeReport data f e c boundary boundaryRoots).states.groups i) :=
  group_maximum (auditOutput f e c) i

theorem native_failure_signature (f e c : Token → Bool) (t : Token) :
    failureSignature (auditOutput f e c) t=true ↔ run f e c 40 t=.failed := by
  change decide (auditOutput f e c t=.fail)=true ↔ _
  rw [decide_eq_true_eq]
  exact Set.ext_iff.mp (native_failed_fiber f e c) t

theorem native_indeterminate_signature {D : Type u} {B : Type v} (data : D)
    (f e c : Token → Bool) (boundary : B) (boundaryRoots : Option (Set Token)) (t : Token) :
    (nativeReport data f e c boundary boundaryRoots).states.indeterminateSignature t=true ↔
      t ∈ (nativeReport data f e c boundary boundaryRoots).states.indeterminate := by
  change decide (auditOutput f e c t=.indeterminate)=true ↔ auditOutput f e c t=.indeterminate
  simp only [decide_eq_true_eq]

theorem approximation_boundary_uses_local_reasons {B : Type u} (s : Token → AuditStatus)
    (boundary : B) (boundaryRoots : Option (Set Token)) (h : groupReasons s approxGroup=∅) :
    (diagnostics s boundary boundaryRoots).approximationBoundary=.inl boundary := by
  change tagged boundary (groupReasons s approxGroup)=_
  rw [h,empty_reasons_preserve_payload]

theorem failed_position_uses_global_reasons {B : Type u} (s : Token → AuditStatus)
    (boundary : B) (boundaryRoots : Option (Set Token)) (h : (reasons s).Nonempty) :
    (diagnostics s boundary boundaryRoots).failedPosition=.inr ⟨reasons s,h⟩ := by
  classical
  change tagged (failed s) (reasons s)=_
  simp only [tagged,dif_neg h.ne_empty]

theorem diagnostic_values_when_defined {B : Type u} (s : Token → AuditStatus)
    (boundary : B) (boundaryRoots : Option (Set Token)) (h : reasons s=∅) :
    diagnostics s boundary boundaryRoots =
      ⟨.inl (failed s),.inl (failureSignature s),.inl boundary,
        .inl (LCTR.CoreStructuralBurden.report (failed s) boundaryRoots)⟩ := by
  have ha : groupReasons s approxGroup=∅ := Set.eq_empty_iff_forall_notMem.mpr (by
    intro p hp
    have hr := approximation_reasons_subset s hp
    rw [h] at hr
    exact hr)
  unfold diagnostics
  rw [h,ha]
  simp only [empty_reasons_preserve_payload]

end LCTR.CoreAuditReport
