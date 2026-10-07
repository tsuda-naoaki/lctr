import CoreNativeLawFailure

namespace LCTR.CoreLawReadinessBridge
set_option autoImplicit false
open Set LCTR.LawFamilyTransport LCTR.SelectedInputEvaluation
variable {E J T A : Type} {X Y : A → Type}

def readySet (dyn : E → Prop) (jointReady : J → Prop) : Set (E ⊕ J) :=
  Sum.inl '' {e | dyn e} ∪ Sum.inr '' {j | jointReady j}

theorem single_ready_exact (dyn : E → Prop) (jointReady : J → Prop) (e : E) :
    Sum.inl e ∈ readySet dyn jointReady ↔ dyn e := by
  simp [readySet]

structure LawDatum (E J T A : Type) (X Y : A → Type) where
  evalSpec : E ⊕ J
  family : Family T A X Y

def lawOperative (dyn : E → Prop) (jointReady : J → Prop)
    (d : LawDatum E J T A X Y) : Prop :=
  d.evalSpec ∈ readySet dyn jointReady ∧ AllConditions d.family

structure ReadySelection (dyn : E → Prop) where
  selected : Selected E (LawDatum E J T A X Y)
  domain_ready : ∀ e, selected.domain e → dyn e
  same_spec : ∀ x, (selected.datum x).evalSpec = Sum.inl x.val

def familySelection {dyn : E → Prop} (s : ReadySelection (J:=J) (T:=T) (A:=A) (X:=X) (Y:=Y) dyn) :
    LCTR.CoreNativeLawFailure.Selection (E:=E) (T:=T) (A:=A) (X:=X) (Y:=Y) :=
  { domain := s.selected.domain, datum := fun x => (s.selected.datum x).family }

theorem selected_datum_ready {dyn : E → Prop}
    (s : ReadySelection (J:=J) (T:=T) (A:=A) (X:=X) (Y:=Y) dyn)
    (jointReady : J → Prop) (e : E) (h : s.selected.domain e) :
    (s.selected.datum ⟨e,h⟩).evalSpec ∈ readySet dyn jointReady := by
  rw [s.same_spec]
  exact (single_ready_exact dyn jointReady e).mpr (s.domain_ready e h)

theorem law_operative_on_selected_datum {dyn : E → Prop}
    (s : ReadySelection (J:=J) (T:=T) (A:=A) (X:=X) (Y:=Y) dyn)
    (jointReady : J → Prop) (e : E) (h : s.selected.domain e) :
    lawOperative dyn jointReady (s.selected.datum ⟨e,h⟩) ↔
      AllConditions (s.selected.datum ⟨e,h⟩).family := by
  simp only [lawOperative,selected_datum_ready s jointReady e h,true_and]

theorem law_failure_requires_dynamics {dyn : E → Prop}
    (s : ReadySelection (J:=J) (T:=T) (A:=A) (X:=X) (Y:=Y) dyn) (e : E)
    (h : LCTR.CoreNativeLawFailure.failure (familySelection s) e) : dyn e :=
  s.domain_ready e h.1

theorem failure_vs_operative {dyn : E → Prop}
    (s : ReadySelection (J:=J) (T:=T) (A:=A) (X:=X) (Y:=Y) dyn)
    (jointReady : J → Prop) (e : E) (h : s.selected.domain e) :
    LCTR.CoreNativeLawFailure.failure (familySelection s) e ↔
      dyn e ∧ ¬ lawOperative dyn jointReady (s.selected.datum ⟨e,h⟩) := by
  have failure := LCTR.CoreNativeLawFailure.failure_on_selected_datum (familySelection s) e h
  simpa only [familySelection,law_operative_on_selected_datum s jointReady e h,
    s.domain_ready e h,true_and] using failure

theorem no_failure_outside_selected_domain {dyn : E → Prop}
    (s : ReadySelection (J:=J) (T:=T) (A:=A) (X:=X) (Y:=Y) dyn)
    (e : E) (h : ¬ s.selected.domain e) :
    ¬ LCTR.CoreNativeLawFailure.failure (familySelection s) e :=
  (LCTR.CoreNativeLawFailure.outside_selection_not_failure (familySelection s) e h).2.1

theorem proper_subdomain_permitted :
    ∃ (selected dyn : Bool → Prop),
      (∀ e, selected e → dyn e) ∧ ¬ (∀ e, selected e ↔ dyn e) := by
  refine ⟨(fun e => e=false),(fun _ => True),fun _ _ => True.intro,?_⟩
  intro h
  have bad := (h true).mpr True.intro
  cases bad

end LCTR.CoreLawReadinessBridge
