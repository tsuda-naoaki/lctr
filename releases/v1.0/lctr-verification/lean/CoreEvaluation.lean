import CoreDagRecursion
import LCTR.SelectedInputEvaluation

namespace LCTR.CoreEvaluation
set_option autoImplicit false
open LCTR.SelectedInputEvaluation
universe u v

noncomputable def update {A : Type u} (E : A → A → Prop)
    (formed evaluated condition : A → Bool) (x : A)
    (incoming : {y : A // E y x} → State) : State := by
  classical
  exact state (formed x) (evaluated x) (decide (∀ y, incoming y = .sat)) (condition x)

def Recurs {A : Type u} (E : A → A → Prop)
    (formed evaluated condition : A → Bool) (s : A → State) : Prop :=
  LCTR.CoreDagRecursion.Solves E (update E formed evaluated condition) s

theorem unique_state_recursion {A : Type u} (E : A → A → Prop)
    (wf : WellFounded E) (formed evaluated condition : A → Bool) :
    ∃! s : A → State, Recurs E formed evaluated condition s :=
  LCTR.CoreDagRecursion.wellFounded_unique E wf _

def argEdge {V : Type u} (E : V → V → Prop) (Spec : V → Type v)
    (res : (x y : V) → E y x → Spec x → Spec y)
    (a b : (x : V) × Spec x) : Prop :=
  ∃ y, ∃ h : E y b.1, a = ⟨y, res b.1 y h b.2⟩

theorem argEdge_wellFounded {V : Type u} (E : V → V → Prop)
    (wf : WellFounded E) (Spec : V → Type v)
    (res : (x y : V) → E y x → Spec x → Spec y) :
    WellFounded (argEdge E Spec res) := by
  have h := InvImage.wf (fun a : (x : V) × Spec x => a.1) wf
  apply Subrelation.wf (r := InvImage E (fun a : (x : V) × Spec x => a.1)) ?_ h
  rintro a b ⟨y, hy, rfl⟩
  exact hy

theorem typed_argument_unique {V : Type u} [Finite V]
    (E : V → V → Prop) (acyclic : ∀ x, ¬ Relation.TransGen E x x)
    (Spec : V → Type v) (res : (x y : V) → E y x → Spec x → Spec y)
    (formed evaluated condition : ((x : V) × Spec x) → Bool) :
    ∃! s, Recurs (argEdge E Spec res) formed evaluated condition s :=
  unique_state_recursion _ (argEdge_wellFounded E
    (LCTR.CoreDagRecursion.finite_acyclic_wellFounded E acyclic) Spec res) _ _ _

theorem state_failed_iff (f e p c : Bool) :
    state f e p c = .failed ↔ f = true ∧ e = true ∧ p = true ∧ c = false := by
  cases f <;> cases e <;> cases p <;> cases c <;> decide

theorem state_sat_iff (f e p c : Bool) :
    state f e p c = .sat ↔ f = true ∧ e = true ∧ p = true ∧ c = true := by
  cases f <;> cases e <;> cases p <;> cases c <;> decide

theorem update_failed_iff {A : Type u} (E : A → A → Prop)
    (f e c : A → Bool) (x : A) (incoming : {y : A // E y x} → State) :
    update E f e c x incoming = .failed ↔
    f x = true ∧ e x = true ∧ (∀ y, incoming y = .sat) ∧ c x = false := by
  classical
  simp only [update, state_failed_iff, decide_eq_true_eq]

theorem direct_nonsat_unformed {A : Type u} (E : A → A → Prop)
    (f e c : A → Bool) (s : A → State) (h : Recurs E f e c s)
    {a b : A} (edge : E a b) (not_sat : s a ≠ .sat) : s b = .unformed := by
  classical
  have np : ¬ ∀ y : {y : A // E y b}, s y.val = .sat := by
    intro hp
    exact not_sat (hp ⟨a, edge⟩)
  rw [h b]
  have dp : decide (∀ y : {y : A // E y b}, s y.val = .sat) = false := by
    simp only [decide_eq_false_iff_not]
    exact np
  change state (f b) (e b) (decide (∀ y : {y : A // E y b}, s y.val = .sat)) (c b) = .unformed
  rw [dp]
  simp [state]

theorem path_nonsat_unformed {A : Type u} (E : A → A → Prop)
    (f e c : A → Bool) (s : A → State) (h : Recurs E f e c s)
    {a b : A} (path : Relation.TransGen E a b) (not_sat : s a ≠ .sat) :
    s b = .unformed := by
  induction path with
  | single edge => exact direct_nonsat_unformed E f e c s h edge not_sat
  | tail _ edge ih =>
    exact direct_nonsat_unformed E f e c s h edge (by rw [ih]; decide)

theorem failed_antichain {A : Type u} (E : A → A → Prop)
    (f e c : A → Bool) (s : A → State) (h : Recurs E f e c s)
    {a b : A} (ha : s a = .failed) (hb : s b = .failed) :
    ¬ Relation.TransGen E a b := by
  intro path
  have bad := path_nonsat_unformed E f e c s h path (by rw [ha]; decide)
  rw [hb] at bad
  cases bad

theorem failed_minimal {A : Type u} (E : A → A → Prop)
    (f e c : A → Bool) (s : A → State) (h : Recurs E f e c s)
    {a b : A} (ha : s a = .failed) (hb : s b = .failed)
    (le : Relation.ReflTransGen E a b) : a = b := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp le with eq | path
  · exact eq.symm
  · exact False.elim (failed_antichain E f e c s h ha hb path)

theorem failed_set_finite {A : Type u} [Finite A] (s : A → State) :
    Set.Finite {x | s x = .failed} := Set.toFinite _

inductive FailureCase where
  | absent | unique | parallel
  deriving DecidableEq

def failureCase (n : Nat) : FailureCase :=
  if n = 0 then .absent else if n = 1 then .unique else .parallel

theorem case_exact (n : Nat) :
    (failureCase n = .absent ↔ n = 0) ∧
    (failureCase n = .unique ↔ n = 1) ∧
    (failureCase n = .parallel ↔ 2 ≤ n) := by
  unfold failureCase
  split_ifs <;> simp_all
  all_goals omega

theorem coherent_section_edge {V : Type u} (E : V → V → Prop)
    (Spec : V → Type v) (res : (x y : V) → E y x → Spec x → Spec y)
    (selected : (x : V) → Spec x)
    (coherent : ∀ x y (h : E y x), res x y h (selected x) = selected y)
    {a b : V} (edge : E a b) :
    argEdge E Spec res ⟨a, selected a⟩ ⟨b, selected b⟩ := by
  refine ⟨a, edge, ?_⟩
  rw [coherent b a edge]

theorem coherent_section_recursion {V : Type u} (E : V → V → Prop)
    (Spec : V → Type v) (res : (x y : V) → E y x → Spec x → Spec y)
    (selected : (x : V) → Spec x)
    (coherent : ∀ x y (h : E y x), res x y h (selected x) = selected y)
    (f e c : ((x : V) × Spec x) → Bool) (s : ((x : V) × Spec x) → State)
    (h : Recurs (argEdge E Spec res) f e c s) :
    Recurs E (fun x => f ⟨x, selected x⟩) (fun x => e ⟨x, selected x⟩)
      (fun x => c ⟨x, selected x⟩) (fun x => s ⟨x, selected x⟩) := by
  classical
  intro x
  have same :
      (∀ a : {a : (y : V) × Spec y // argEdge E Spec res a ⟨x, selected x⟩}, s a.val = .sat) ↔
      (∀ y : {y : V // E y x}, s ⟨y.val, selected y.val⟩ = .sat) := by
    constructor
    · intro hs y
      exact hs ⟨⟨y.val, selected y.val⟩, coherent_section_edge E Spec res selected coherent y.property⟩
    · rintro hs ⟨a, y, hy, rfl⟩
      simp only [coherent]
      exact hs ⟨y, hy⟩
  change s ⟨x, selected x⟩ = _
  rw [h ⟨x, selected x⟩]
  simp only [update, propext same]

theorem failed_requires_native_domain {A : Type u} (E : A → A → Prop)
    (f e c : A → Bool) (s : A → State) (h : Recurs E f e c s)
    (D : A → Prop)
    (typed : ∀ x, f x = true → e x = true →
      (∀ y : {y : A // E y x}, s y.val = .sat) → D x)
    {x : A} (failed : s x = .failed) : D x := by
  rw [h x, update_failed_iff] at failed
  exact typed x failed.1 failed.2.1 failed.2.2.1

theorem fibres_cover {A : Type u} (s : A → State) (R : Set A) :
    ⋃ q : State, {x ∈ R | s x = q} = R := by
  ext x
  simp

theorem fibres_disjoint {A : Type u} (s : A → State) (R : Set A)
    {q r : State} (ne : q ≠ r) :
    Disjoint {x ∈ R | s x = q} {x ∈ R | s x = r} := by
  apply Set.disjoint_left.mpr
  rintro x ⟨_, hq⟩ ⟨_, hr⟩
  exact ne (hq.symm.trans hr)

theorem failed_partition {A : Type u} (s : A → State) (strict approx : Set A)
    (cover : strict ∪ approx = Set.univ) (disj : Disjoint strict approx) :
    {x | s x = .failed} = ({x | s x = .failed} ∩ strict) ∪
      ({x | s x = .failed} ∩ approx) ∧
    Disjoint ({x | s x = .failed} ∩ strict) ({x | s x = .failed} ∩ approx) := by
  constructor
  · rw [← Set.inter_union_distrib_left, cover, Set.inter_univ]
  · exact disj.mono Set.inter_subset_right Set.inter_subset_right

#print axioms typed_argument_unique
#print axioms path_nonsat_unformed
#print axioms failed_antichain
#print axioms coherent_section_edge
#print axioms fibres_cover
#print axioms fibres_disjoint
#print axioms failed_partition
#print axioms failed_minimal
#print axioms failed_set_finite
#print axioms case_exact
#print axioms coherent_section_recursion
#print axioms failed_requires_native_domain
end LCTR.CoreEvaluation
