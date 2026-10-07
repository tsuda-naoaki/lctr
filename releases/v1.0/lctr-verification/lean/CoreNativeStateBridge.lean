import CoreNativeSpecification

namespace LCTR.CoreNativeStateBridge
set_option autoImplicit false
open Set LCTR.CoreTokenGraph LCTR.SelectedInputEvaluation
universe u v

def res {E : Type u} {L : Type v} (x y : Token) (h : Edge y x) :
    LCTR.CoreNativeSpecification.Spec E L (LCTR.CoreNativeSpecification.kind x) → LCTR.CoreNativeSpecification.Spec E L (LCTR.CoreNativeSpecification.kind y) :=
  LCTR.CoreNativeSpecification.restriction (LCTR.CoreNativeSpecification.kind y) (LCTR.CoreNativeSpecification.kind x) (LCTR.CoreNativeSpecification.edge_kind y x h)

theorem canonical_recursion_unique {E : Type u} {L : Type v}
    (f e c : LCTR.CoreNativeSpecification.EvalArg E L → Bool) :
    ∃! s, LCTR.CoreEvaluation.Recurs (LCTR.CoreEvaluation.argEdge Edge (fun t => LCTR.CoreNativeSpecification.Spec E L (LCTR.CoreNativeSpecification.kind t)) res) f e c s :=
  concrete_argument_unique _ res f e c

theorem gate_and_state_cases (f e p c : Bool) :
    ((f && e) = true ↔ f = true ∧ e = true) ∧
    ((f && p) = true ↔ f = true ∧ p = true) ∧
    ((p && (f && e)) = true ↔ p = true ∧ f = true ∧ e = true) ∧
    (state f e p c = .unformed ↔ (f && p) = false) ∧
    (state f e p c = .unevaluable ↔ (f && p) = true ∧ e = false) ∧
    (state f e p c = .sat ↔ (p && (f && e)) = true ∧ c = true) ∧
    (state f e p c = .failed ↔ (p && (f && e)) = true ∧ c = false) := by
  cases f <;> cases e <;> cases p <;> cases c <;> decide

theorem state_section_recursion {E : Type u} {L : Type v}
    (f e c : LCTR.CoreNativeSpecification.EvalArg E L → Bool) (s : LCTR.CoreNativeSpecification.EvalArg E L → State)
    (h : LCTR.CoreEvaluation.Recurs (LCTR.CoreEvaluation.argEdge Edge (fun t => LCTR.CoreNativeSpecification.Spec E L (LCTR.CoreNativeSpecification.kind t)) res) f e c s)
    (ev : E) (l : L) :
    LCTR.CoreEvaluation.Recurs Edge (fun t => f (LCTR.CoreNativeSpecification.argAt ev l t)) (fun t => e (LCTR.CoreNativeSpecification.argAt ev l t))
      (fun t => c (LCTR.CoreNativeSpecification.argAt ev l t)) (fun t => s (LCTR.CoreNativeSpecification.argAt ev l t)) := by
  apply LCTR.CoreEvaluation.coherent_section_recursion Edge (fun t => LCTR.CoreNativeSpecification.Spec E L (LCTR.CoreNativeSpecification.kind t)) res
    (fun t => LCTR.CoreNativeSpecification.specAt (LCTR.CoreNativeSpecification.kind t) ev l) _ f e c s h
  intro x y hy
  exact LCTR.CoreNativeSpecification.restriction_coherent _ _ _ ev l

def strictArg {E : Type u} {L : Type v} (ev : E) (t : Token)
    (h : LCTR.CoreNativeSpecification.kind t = false) : LCTR.CoreNativeSpecification.EvalArg E L :=
  ⟨t, h.symm ▸ (ULift.up ev : LCTR.CoreNativeSpecification.Spec E L false)⟩

theorem strict_argument_recovery {E : Type u} {L : Type v}
    (ev : E) (l : L) (t : Token) (h : LCTR.CoreNativeSpecification.kind t = false) :
    LCTR.CoreNativeSpecification.argAt ev l t = strictArg ev t h := by
  have aux : ∀ (b : Bool) (hb : b = false),
      LCTR.CoreNativeSpecification.specAt b ev l =
      hb.symm ▸ (ULift.up ev : LCTR.CoreNativeSpecification.Spec E L false) := by
    intro b hb
    cases b
    · rfl
    · cases hb
  exact congrArg (Sigma.mk t) (aux _ h)

theorem strict_state_scale_independent {E : Type u} {L : Type v}
    (s : LCTR.CoreNativeSpecification.EvalArg E L → State) (ev : E) (l m : L) (t : Token)
    (h : LCTR.CoreNativeSpecification.kind t = false) : s (LCTR.CoreNativeSpecification.argAt ev l t) = s (LCTR.CoreNativeSpecification.argAt ev m t) := by
  rw [strict_argument_recovery ev l t h,strict_argument_recovery ev m t h]

def strictFailed {E : Type u} {L : Type v} (s : LCTR.CoreNativeSpecification.EvalArg E L → State) (ev : E) : Set Token :=
  {t | ∃ h : LCTR.CoreNativeSpecification.kind t = false, s (strictArg ev t h) = .failed}

theorem strict_failed_typed {E : Type u} {L : Type v}
    (s : LCTR.CoreNativeSpecification.EvalArg E L → State) (ev : E) :
    strictFailed s ev ⊆ {t | LCTR.CoreNativeSpecification.kind t = false} := by
  rintro t ⟨ht,_⟩; exact ht

theorem strict_failed_recovery {E : Type u} {L : Type v}
    (s : LCTR.CoreNativeSpecification.EvalArg E L → State) (ev : E) (l : L) :
    strictFailed s ev = {t | s (LCTR.CoreNativeSpecification.argAt ev l t) = .failed} ∩ {t | LCTR.CoreNativeSpecification.kind t = false} := by
  ext t
  constructor
  · rintro ⟨ht,hs⟩
    exact ⟨by simpa [strict_argument_recovery ev l t ht] using hs,ht⟩
  · rintro ⟨hs,ht⟩
    exact ⟨ht,by simpa [strict_argument_recovery ev l t ht] using hs⟩

theorem strict_failed_scale_independent {E : Type u} {L : Type v}
    (s : LCTR.CoreNativeSpecification.EvalArg E L → State) (ev : E) (l m : L) :
    {t | s (LCTR.CoreNativeSpecification.argAt ev l t) = .failed} ∩ {t | LCTR.CoreNativeSpecification.kind t = false} =
    {t | s (LCTR.CoreNativeSpecification.argAt ev m t) = .failed} ∩ {t | LCTR.CoreNativeSpecification.kind t = false} := by
  rw [← strict_failed_recovery,← strict_failed_recovery]

theorem missing_input_unformed (e p c : Bool) : state false e p c = .unformed :=
  LCTR.SelectedInputEvaluation.missing_input_unformed e p c

theorem off_domain_not_failed {A : Type u} (edge : A → A → Prop)
    (f e c : A → Bool) (s : A → State) (h : LCTR.CoreEvaluation.Recurs edge f e c s)
    (D : A → Prop)
    (typed : ∀ x, f x = true → e x = true →
      (∀ y : {y : A // edge y x}, s y.val = .sat) → D x)
    (x : A) (outside : ¬ D x) : s x ≠ .failed := by
  intro hf
  exact outside (LCTR.CoreEvaluation.failed_requires_native_domain edge f e c s h D typed hf)

end LCTR.CoreNativeStateBridge
