import CoreEvaluation
import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Finset.Lattice.Fold

namespace LCTR.CoreAuditStateTransport
set_option autoImplicit false
open Set LCTR.SelectedInputEvaluation LCTR.CoreEvaluation
universe u v

theorem predecessors_pass_iff {A : Type u} {B : Type v}
    (c : A ≃ B) (E : A → A → Prop) (F : B → B → Prop)
    (edges : ∀ a b, E a b ↔ F (c a) (c b)) (s : B → State) (x : A) :
    (∀ y : {y : B // F y (c x)}, s y.val = .sat) ↔
      (∀ a : {a : A // E a x}, s (c a.val) = .sat) := by
  constructor
  · intro h a
    exact h ⟨c a.val,(edges a.val x).mp a.property⟩
  · intro h y
    obtain ⟨a,ha⟩ := c.surjective y.val
    have ae : E a x := (edges a x).mpr (ha.symm ▸ y.property)
    simpa only [ha] using h ⟨a,ae⟩

theorem recursion_pullback {A : Type u} {B : Type v}
    (c : A ≃ B) (E : A → A → Prop) (F : B → B → Prop)
    (edges : ∀ a b, E a b ↔ F (c a) (c b))
    (f0 e0 q0 : A → Bool) (f1 e1 q1 : B → Bool)
    (forms : ∀ a, f1 (c a)=f0 a) (evals : ∀ a, e1 (c a)=e0 a)
    (conditions : ∀ a, q1 (c a)=q0 a)
    (s : B → State) (hs : Recurs F f1 e1 q1 s) :
    Recurs E f0 e0 q0 (s ∘ c) := by
  classical
  intro x
  change s (c x) = _
  rw [hs (c x)]
  simp only [update,forms,evals,conditions,Function.comp_apply,
    propext (predecessors_pass_iff c E F edges s x)]

theorem state_covariance {A : Type u} {B : Type v}
    (c : A ≃ B) (E : A → A → Prop) (F : B → B → Prop)
    (wf : WellFounded E) (edges : ∀ a b, E a b ↔ F (c a) (c b))
    (f0 e0 q0 : A → Bool) (f1 e1 q1 : B → Bool)
    (forms : ∀ a, f1 (c a)=f0 a) (evals : ∀ a, e1 (c a)=e0 a)
    (conditions : ∀ a, q1 (c a)=q0 a)
    (s0 : A → State) (s1 : B → State)
    (h0 : Recurs E f0 e0 q0 s0) (h1 : Recurs F f1 e1 q1 s1) :
    ∀ a, s1 (c a) = s0 a := by
  obtain ⟨s,_,unique⟩ := unique_state_recursion E wf f0 e0 q0
  have h := (unique _ (recursion_pullback c E F edges f0 e0 q0 f1 e1 q1
    forms evals conditions s1 h1)).trans (unique _ h0).symm
  exact congrFun h

inductive AuditStatus where
  | pass | indeterminate | unformed | blocked | fail
  deriving DecidableEq

def lift : Bool → State → AuditStatus
  | false,_ => .blocked
  | true,.unformed => .unformed
  | true,.unevaluable => .indeterminate
  | true,.sat => .pass
  | true,.failed => .fail

def priority : AuditStatus → ℕ
  | .pass => 0
  | .indeterminate => 1
  | .unformed => 2
  | .blocked => 3
  | .fail => 4

theorem priority_injective : Function.Injective priority := by
  intro a b
  cases a <;> cases b <;> simp [priority]

noncomputable def auditAt {A : Type u} (E : A → A → Prop) (s : A → State) (x : A) : AuditStatus := by
  classical
  exact lift (decide (∀ y : {y : A // E y x}, s y.val = .sat)) (s x)

theorem auditAt_covariance {A : Type u} {B : Type v}
    (c : A ≃ B) (E : A → A → Prop) (F : B → B → Prop)
    (edges : ∀ a b, E a b ↔ F (c a) (c b))
    (s0 : A → State) (s1 : B → State) (hs : ∀ a, s1 (c a)=s0 a) :
    ∀ a, auditAt F s1 (c a) = auditAt E s0 a := by
  classical
  intro a
  unfold auditAt
  simp only [propext (predecessors_pass_iff c E F edges s1 a),hs]

theorem audit_fiber_image {A : Type u} {B : Type v}
    (c : A ≃ B) (s : A → AuditStatus) (t : B → AuditStatus)
    (ht : ∀ a, t (c a)=s a) (q : AuditStatus) :
    c '' {a | s a=q} = {b | t b=q} := by
  ext b
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact (ht a).trans ha
  · intro hb
    obtain ⟨a,rfl⟩ := c.surjective b
    exact ⟨a,(ht a).symm.trans hb,rfl⟩

theorem group_priority_covariance {A : Type u} {B : Type v} [DecidableEq B]
    (c : A ≃ B) (s : A → AuditStatus) (t : B → AuditStatus)
    (ht : ∀ a, t (c a)=s a) (G : Finset A) :
    (G.image c).sup (fun b => priority (t b)) = G.sup (fun a => priority (s a)) := by
  simp only [Finset.sup_image,Function.comp_def,ht]

theorem indeterminate_signature_covariance {A : Type u} {B : Type v}
    (c : A ≃ B) (s : A → AuditStatus) (t : B → AuditStatus)
    (ht : ∀ a, t (c a)=s a) (a : A) :
    (decide (t (c a)=.indeterminate) : Bool) = decide (s a=.indeterminate) := by
  rw [ht]

theorem blocked_and_unformed_distinct : lift false .unformed ≠ lift true .unformed := by decide

theorem audit_failure_exact (f e p q : Bool) :
    lift p (state f e p q) = .fail ↔
      f=true ∧ e=true ∧ p=true ∧ q=false := by
  cases f <;> cases e <;> cases p <;> cases q <;> decide

theorem missing_formation_not_failure (e p q : Bool) :
    lift p (state false e p q) ≠ .fail := by
  cases e <;> cases p <;> cases q <;> decide

theorem audit_state_transport {A : Type u} {B : Type v}
    (c : A ≃ B) (E : A → A → Prop) (F : B → B → Prop)
    (wf : WellFounded E) (edges : ∀ a b, E a b ↔ F (c a) (c b))
    (f0 e0 q0 : A → Bool) (f1 e1 q1 : B → Bool)
    (forms : ∀ a, f1 (c a)=f0 a) (evals : ∀ a, e1 (c a)=e0 a)
    (conditions : ∀ a, q1 (c a)=q0 a)
    (s0 : A → State) (s1 : B → State)
    (h0 : Recurs E f0 e0 q0 s0) (h1 : Recurs F f1 e1 q1 s1) :
    (∀ a, auditAt F s1 (c a) = auditAt E s0 a) ∧
    (∀ q, c '' {a | auditAt E s0 a=q} = {b | auditAt F s1 b=q}) := by
  have hs := state_covariance c E F wf edges f0 e0 q0 f1 e1 q1 forms evals conditions s0 s1 h0 h1
  have ha := auditAt_covariance c E F edges s0 s1 hs
  exact ⟨ha,fun q => audit_fiber_image c (auditAt E s0) (auditAt F s1) ha q⟩

end LCTR.CoreAuditStateTransport
