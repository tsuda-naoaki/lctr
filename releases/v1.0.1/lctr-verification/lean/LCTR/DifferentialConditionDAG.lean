import Std

namespace LCTR.DifferentialConditionDAG
set_option autoImplicit false

 
abbrev Node := Fin 5
def Edge (i j : Node) : Prop :=
  (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 2) ∨
  (i.val = 0 ∧ j.val = 3) ∨ (i.val = 0 ∧ j.val = 4)

inductive Path : Node → Node → Prop where
  | edge {i j : Node} : Edge i j → Path i j
  | step {i j k : Node} : Edge i j → Path j k → Path i k

theorem edge_increases {i j : Node} (h : Edge i j) : i.val < j.val := by
  rcases h with h | h | h | h <;> omega

theorem path_increases {i j : Node} (h : Path i j) : i.val < j.val := by
  induction h with
  | edge h => exact edge_increases h
  | step h _ ih => exact Nat.lt_trans (edge_increases h) ih

theorem acyclic (i : Node) : ¬ Path i i := by
  intro h
  exact Nat.lt_irrefl i.val (path_increases h)

def ValueEdge (value : Node → Bool) (a b : Bool) : Prop :=
  ∃ i j, Edge i j ∧ value i = a ∧ value j = b

theorem truth_value_image_has_self_loop : ValueEdge (fun _ => true) true true :=
  ⟨⟨0,by decide⟩,⟨1,by decide⟩,Or.inl ⟨rfl,rfl⟩,rfl,rfl⟩

#print axioms edge_increases
#print axioms path_increases
#print axioms acyclic
#print axioms truth_value_image_has_self_loop
end LCTR.DifferentialConditionDAG
