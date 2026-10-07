import CoreNativeLawComponents
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace LCTR.CoreLawConditionGraph
set_option autoImplicit false
open LCTR.LawFamilyTransport

abbrev Node := Fin 5
def Edge (i j : Node) : Prop := (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 4)
def Ancestor (i j : Node) : Prop := Edge i j ∨ (i = 0 ∧ j = 4)
instance (i j : Node) : Decidable (Edge i j) := by unfold Edge; infer_instance
instance (i j : Node) : Decidable (Ancestor i j) := by unfold Ancestor; infer_instance
def rank (i : Node) : Nat := if i = 2 then 1 else if i = 4 then 2 else 0

theorem edge_rank : ∀ i j : Node, Edge i j → rank i < rank j := by decide
theorem ancestor_irreflexive : ∀ i : Node, ¬ Ancestor i i := by decide
theorem ancestor_transitive : ∀ i j k : Node, Ancestor i j → Ancestor j k → Ancestor i k := by decide

theorem ancestors_exact (i j : Node) : Relation.TransGen Edge i j ↔ Ancestor i j := by
  constructor
  · intro path
    induction path with
    | single h => exact Or.inl h
    | tail _ h ih => exact ancestor_transitive _ _ _ ih (Or.inl h)
  · intro h
    rcases h with edge | ⟨hi,hj⟩
    · exact Relation.TransGen.single edge
    · subst i; subst j
      exact Relation.TransGen.tail (Relation.TransGen.single (show Edge 0 2 by decide))
        (show Edge 2 4 by decide)

theorem acyclic (i : Node) : ¬ Relation.TransGen Edge i i :=
  fun h => ancestor_irreflexive i ((ancestors_exact i i).mp h)

theorem roots_exact : ∀ j : Node, (¬ ∃ i, Edge i j) ↔ j = 0 ∨ j = 1 ∨ j = 3 := by decide

theorem ancestor_sets :
    (∀ i : Node, ¬ Ancestor i 0 ∧ ¬ Ancestor i 1 ∧ ¬ Ancestor i 3) ∧
    (∀ i : Node, Ancestor i 2 ↔ i = 0) ∧
    (∀ i : Node, Ancestor i 4 ↔ i = 0 ∨ i = 2) := by decide

def condition {T A : Type} {X Y : A → Type} (d : Family T A X Y) (i : Node) : Prop :=
  if i = 0 then K1 d else if i = 1 then K2 d else if i = 2 then K3 d else if i = 3 then K4 d else K5 d

theorem condition_vector_exact {T A : Type} {X Y : A → Type} (d : Family T A X Y) :
    condition d 0 = K1 d ∧ condition d 1 = K2 d ∧ condition d 2 = K3 d ∧
    condition d 3 = K4 d ∧ condition d 4 = K5 d := by simp [condition]

theorem all_conditions_exact {T A : Type} {X Y : A → Type} (d : Family T A X Y) :
    (∀ i : Node, condition d i) ↔ AllConditions d := by
  constructor
  · intro h
    exact ⟨by simpa [condition] using h 0, by simpa [condition] using h 1,
      by simpa [condition] using h 2, by simpa [condition] using h 3,
      by simpa [condition] using h 4⟩
  · rintro ⟨h1,h2,h3,h4,h5⟩ i
    fin_cases i <;> simp_all [condition]

theorem condition_dependency {T A : Type} {X Y : A → Type} (d : Family T A X Y)
    (i j : Node) (edge : Edge i j) (holds : condition d j) : condition d i := by
  rcases edge with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have h3 : K3 d := by simpa [condition] using holds
    simpa [condition] using h3.1
  · have h5 : K5 d := by simpa [condition] using holds
    simpa [condition] using h5.1

theorem ancestor_conditions_hold {T A : Type} {X Y : A → Type} (d : Family T A X Y)
    (i j : Node) (ancestor : Relation.TransGen Edge i j) (holds : condition d j) : condition d i := by
  induction ancestor with
  | single h => exact condition_dependency d _ _ h holds
  | tail _ h ih => exact ih (condition_dependency d _ _ h holds)

end LCTR.CoreLawConditionGraph
