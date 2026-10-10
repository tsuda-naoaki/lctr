import CoreLawReadinessBridge
import CoreStageBoundaries

namespace LCTR.CoreLawDatumSemantics
set_option autoImplicit false
open LCTR.LawFamilyTransport LCTR.CoreLawConditionGraph
variable {E J : Type}

structure Candidate where
  Time : Type
  Index : Type
  InputValue : Index → Type
  OutputValue : Index → Type
  family : Family Time Index InputValue OutputValue

def pack {T A : Type} {X Y : A → Type} (d : Family T A X Y) : Candidate :=
  ⟨T,A,X,Y,d⟩

structure Datum (E J : Type) where
  evalSpec : E ⊕ J
  candidate : Candidate

def lawOperative (dyn : E → Prop) (jointReady : J → Prop) (d : Datum E J) : Prop :=
  d.evalSpec ∈ LCTR.CoreLawReadinessBridge.readySet dyn jointReady ∧
    AllConditions d.candidate.family

structure Selection (E J : Type) (dyn : E → Prop) where
  domain : E → Prop
  datum : {e // domain e} → Datum E J
  domain_ready : ∀ e, domain e → dyn e
  same_spec : ∀ x, (datum x).evalSpec = Sum.inl x.val

def totalCondition {dyn : E → Prop} (s : Selection E J dyn) (e : E) (i : Node) : Prop :=
  ∃ h : s.domain e, condition (s.datum ⟨e,h⟩).candidate.family i

def failure {dyn : E → Prop} (s : Selection E J dyn) (e : E) : Prop :=
  s.domain e ∧ ¬ ∀ i, totalCondition s e i

def localFamily (d : Datum E J) :
    LCTR.CoreNativeLawFailure.Selection (E:=Unit) (T:=d.candidate.Time)
      (A:=d.candidate.Index) (X:=d.candidate.InputValue) (Y:=d.candidate.OutputValue) :=
  { domain := fun _ => True, datum := fun _ => d.candidate.family }

theorem selected_condition_exact {dyn : E → Prop} (s : Selection E J dyn)
    (e : E) (h : s.domain e) (i : Node) :
    totalCondition s e i ↔ condition (s.datum ⟨e,h⟩).candidate.family i := by
  constructor
  · rintro ⟨_,hi⟩
    exact hi
  · exact fun hi => ⟨h,hi⟩

theorem selected_all_conditions_exact {dyn : E → Prop} (s : Selection E J dyn)
    (e : E) (h : s.domain e) :
    (∀ i, totalCondition s e i) ↔ AllConditions (s.datum ⟨e,h⟩).candidate.family :=
  (forall_congr' (selected_condition_exact s e h)).trans (all_conditions_exact _)

theorem selected_datum_ready {dyn : E → Prop} (s : Selection E J dyn)
    (jointReady : J → Prop) (e : E) (h : s.domain e) :
    (s.datum ⟨e,h⟩).evalSpec ∈ LCTR.CoreLawReadinessBridge.readySet dyn jointReady := by
  rw [s.same_spec]
  exact (LCTR.CoreLawReadinessBridge.single_ready_exact dyn jointReady e).mpr
    (s.domain_ready e h)

theorem law_operative_on_selected_datum {dyn : E → Prop} (s : Selection E J dyn)
    (jointReady : J → Prop) (e : E) (h : s.domain e) :
    lawOperative dyn jointReady (s.datum ⟨e,h⟩) ↔
      AllConditions (s.datum ⟨e,h⟩).candidate.family := by
  simp only [lawOperative,selected_datum_ready s jointReady e h,true_and]

theorem failure_on_selected_datum {dyn : E → Prop} (s : Selection E J dyn)
    (e : E) (h : s.domain e) :
    failure s e ↔ ¬ AllConditions (s.datum ⟨e,h⟩).candidate.family := by
  simp only [failure,h,true_and,selected_all_conditions_exact s e h]

theorem failure_matches_native_family {dyn : E → Prop} (s : Selection E J dyn)
    (e : E) (h : s.domain e) :
    failure s e ↔ LCTR.CoreNativeLawFailure.failure (localFamily (s.datum ⟨e,h⟩)) () :=
  (failure_on_selected_datum s e h).trans
    (LCTR.CoreNativeLawFailure.failure_on_selected_datum
      (localFamily (s.datum ⟨e,h⟩)) () True.intro).symm

theorem failure_vs_operative {dyn : E → Prop} (s : Selection E J dyn)
    (jointReady : J → Prop) (e : E) (h : s.domain e) :
    failure s e ↔ dyn e ∧ ¬ lawOperative dyn jointReady (s.datum ⟨e,h⟩) := by
  simpa only [law_operative_on_selected_datum s jointReady e h,
    s.domain_ready e h,true_and] using failure_on_selected_datum s e h

theorem outside_selection_not_failure {dyn : E → Prop} (s : Selection E J dyn)
    (e : E) (outside : ¬ s.domain e) :
    (∀ i, ¬ totalCondition s e i) ∧ ¬ failure s e := by
  exact ⟨fun _ h => outside h.1,fun h => outside h.1⟩

theorem law_failure_requires_dynamics {dyn : E → Prop} (s : Selection E J dyn)
    (e : E) (hf : failure s e) : dyn e :=
  s.domain_ready e hf.1

theorem dynamics_law_failures_disjoint
    (exactInput : E → Prop) (K : E → Fin 8 → Prop)
    (law : Selection E J (LCTR.CoreStageBoundaries.DynOperative exactInput K))
    (ev : E) (f e c : LCTR.CoreTokenGraph.Token → Bool)
    (s : LCTR.CoreTokenGraph.Token → LCTR.SelectedInputEvaluation.State)
    (rec : LCTR.CoreEvaluation.Recurs LCTR.CoreTokenGraph.Edge f e c s)
    (assignment : ∀ i, c (LCTR.CoreDynamicsTokens.token i) = true ↔ K ev i) :
    ¬ ((∃ i, s (LCTR.CoreDynamicsTokens.token i) = .failed) ∧ failure law ev) := by
  rintro ⟨hd,hl⟩
  exact LCTR.CoreStageBoundaries.dynamics_failure_not_operative
    exactInput K ev f e c s rec assignment hd (law_failure_requires_dynamics law ev hl)

def fromFixed {T A : Type} {X Y : A → Type}
    (d : LCTR.CoreLawReadinessBridge.LawDatum E J T A X Y) : Datum E J :=
  ⟨d.evalSpec,pack d.family⟩

theorem fixed_carrier_operative_exact {T A : Type} {X Y : A → Type}
    (dyn : E → Prop) (jointReady : J → Prop)
    (d : LCTR.CoreLawReadinessBridge.LawDatum E J T A X Y) :
    lawOperative dyn jointReady (fromFixed d) ↔
      LCTR.CoreLawReadinessBridge.lawOperative dyn jointReady d := Iff.rfl

theorem candidate_condition_vector (d : Datum E J) :
    condition d.candidate.family 0 = K1 d.candidate.family ∧
    condition d.candidate.family 1 = K2 d.candidate.family ∧
    condition d.candidate.family 2 = K3 d.candidate.family ∧
    condition d.candidate.family 3 = K4 d.candidate.family ∧
    condition d.candidate.family 4 = K5 d.candidate.family :=
  condition_vector_exact _

end LCTR.CoreLawDatumSemantics
