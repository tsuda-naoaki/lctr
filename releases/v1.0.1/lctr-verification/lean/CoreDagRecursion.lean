import Mathlib.Order.WellFoundedSet
import Mathlib.Logic.Relation

namespace LCTR.CoreDagRecursion
set_option autoImplicit false
universe u v

def Solves {V : Type u} {S : Type v} (E : V → V → Prop)
    (phi : (x : V) → ({y : V // E y x} → S) → S) (s : V → S) : Prop :=
  ∀ x, s x = phi x (fun y => s y.val)

theorem wellFounded_unique {V : Type u} {S : Type v} (E : V → V → Prop)
    (wf : WellFounded E)
    (phi : (x : V) → ({y : V // E y x} → S) → S) :
    ∃! s : V → S, Solves E phi s := by
  let step : (x : V) → ((y : V) → E y x → S) → S :=
    fun x h => phi x (fun y => h y.val y.property)
  let s : V → S := wf.fix step
  have hs : Solves E phi s := by
    intro x
    exact wf.fix_eq step x
  refine ⟨s, hs, ?_⟩
  intro t ht
  funext x
  apply wf.induction x
  intro x ih
  rw [ht x, hs x]
  congr 1
  funext y
  exact ih y.val y.property

theorem finite_acyclic_wellFounded {V : Type u} [Finite V]
    (E : V → V → Prop) (acyclic : ∀ x, ¬ Relation.TransGen E x x) :
    WellFounded E := by
  let : IsStrictOrder V (Relation.TransGen E) :=
    { irrefl := acyclic, trans := fun _ _ _ a b => a.trans b }
  have hw : WellFounded (Relation.TransGen E) :=
    Set.wellFoundedOn_univ.mp (Set.toFinite (Set.univ : Set V)).wellFoundedOn
  exact Subrelation.wf (fun h => Relation.TransGen.single h) hw

theorem finite_dag_deterministic_state_fold {V : Type u} {S : Type v} [Finite V]
    (E : V → V → Prop) (acyclic : ∀ x, ¬ Relation.TransGen E x x)
    (phi : (x : V) → ({y : V // E y x} → S) → S) :
    ∃! s : V → S, Solves E phi s :=
  wellFounded_unique E (finite_acyclic_wellFounded E acyclic) phi

theorem empty_vertices_allow_empty_states :
    ∃! s : Empty → Empty, Solves (fun _ _ : Empty => False)
      (fun x _ => nomatch x) s := by
  exact finite_dag_deterministic_state_fold _ (fun x => nomatch x) _

theorem cyclic_update_can_have_no_solution :
    ¬ ∃ s : Unit → Bool, ∀ x, s x = !(s x) := by
  intro ⟨s,h⟩
  have bad := h ()
  cases hval : s () <;> simp [hval] at bad

theorem cyclic_update_can_have_multiple_solutions :
    ∃ f g : Unit → Bool, f ≠ g ∧
      (∀ x, f x = f x) ∧ (∀ x, g x = g x) := by
  refine ⟨fun _ => false, fun _ => true, ?_, fun _ => rfl, fun _ => rfl⟩
  intro h
  have bad := congrFun h ()
  cases bad

theorem edge_orientation_control :
    Solves (fun a b : Bool => a = false ∧ b = true)
      (fun x incoming => if h : x = true then !(incoming ⟨false, rfl, h⟩) else false)
      (fun x => x) := by
  intro x
  cases x <;> simp

#print axioms finite_dag_deterministic_state_fold
#print axioms empty_vertices_allow_empty_states
#print axioms cyclic_update_can_have_no_solution
#print axioms cyclic_update_can_have_multiple_solutions
#print axioms edge_orientation_control
end LCTR.CoreDagRecursion
