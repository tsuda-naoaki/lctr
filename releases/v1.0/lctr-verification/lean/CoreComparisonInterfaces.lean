import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

namespace LCTR.CoreComparisonInterfaces
universe u v w
set_option autoImplicit false

abbrev Common (X : Type u) (J : Type v) := X × J
def evaluate {X : Type u} {J : Type v} {Y : Type w}
    (f : X → J → Y) (input : Common X J) : Y := f input.1 input.2

theorem common_evaluation {X : Type u} {J : Type v} {Y : Type w}
    (f : X → J → Y) (x : X) (j : J) : evaluate f (x,j) = f x j := rfl

abbrev Index (U : Type u) (m : Nat) := Fin 2 × (Fin m → U)
def packOne {U : Type u} (p : Fin 2 × U) : Index U 1 := (p.1,fun _ => p.2)
def packTwo {U : Type u} (p : Fin 2 × U × U) : Index U 2 :=
  (p.1,fun i => if i=0 then p.2.1 else p.2.2)

theorem index_one_unique {U : Type u} (x : Index U 1) :
    ∃! p : Fin 2 × U, packOne p = x := by
  refine ⟨(x.1,x.2 0), ?_, ?_⟩
  · apply Prod.ext
    · rfl
    · funext i
      fin_cases i
      rfl
  · intro p h
    apply Prod.ext
    · exact congrArg (fun q : Index U 1 => q.1) h
    · exact congrArg (fun q : Index U 1 => q.2 0) h

theorem index_two_unique {U : Type u} (x : Index U 2) :
    ∃! p : Fin 2 × U × U, packTwo p = x := by
  refine ⟨(x.1,x.2 0,x.2 1), ?_, ?_⟩
  · apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> rfl
  · intro p h
    apply Prod.ext
    · exact congrArg (fun q : Index U 2 => q.1) h
    · apply Prod.ext
      · exact congrArg (fun q : Index U 2 => q.2 0) h
      · exact congrArg (fun q : Index U 2 => q.2 1) h

def argument {X : Type u} {J : Type v} (x : X) (j : J) (i : Fin 7) : X ⊕ Common X J :=
  if i=0 then Sum.inl x else Sum.inr (x,j)

theorem first_argument {X : Type u} {J : Type v} (x : X) (j : J) :
    argument x j 0 = Sum.inl x := rfl

theorem later_argument {X : Type u} {J : Type v} (x : X) (j : J)
    (i : Fin 7) (h : i ≠ 0) : argument x j i = Sum.inr (x,j) := by
  simp only [argument,if_neg h]

def evaluateArgument {X : Type u} {J : Type v}
    (first : X → Prop) (later : Fin 7 → Common X J → Prop) (i : Fin 7) :
    X ⊕ Common X J → Prop
  | Sum.inl x => first x
  | Sum.inr input => later i input

theorem evaluation_dispatch {X : Type u} {J : Type v}
    (first : X → Prop) (later : Fin 7 → Common X J → Prop) (x : X) (j : J) (i : Fin 7) :
    evaluateArgument first later i (argument x j i) ↔
      if i=0 then first x else later i (x,j) := by
  by_cases h : i=0 <;> simp only [argument,h,ite_true,ite_false,evaluateArgument]

def before (c : Fin 7 → Prop) (i : Fin 7) : Prop := ∀ j, j.val < i.val → c j
def through (c : Fin 7 → Prop) (i : Fin 7) : Prop := ∀ j, j.val ≤ i.val → c j

theorem first_preceding (c : Fin 7 → Prop) : before c 0 ↔ True := by
  simp [before]

theorem preceding_successor (c : Fin 7 → Prop) (i : Fin 6) :
    before c i.succ ↔ through c i.castSucc := by
  simp only [before,through,Fin.val_succ,Fin.val_castSucc,Nat.lt_add_one_iff]

theorem established_step (c : Fin 7 → Prop) (i : Fin 7) :
    through c i ↔ before c i ∧ c i := by
  constructor
  · intro h
    exact ⟨fun j hj => h j (Nat.le_of_lt hj), h i (Nat.le_refl _)⟩
  · rintro ⟨h,hi⟩ j hji
    rcases Nat.lt_or_eq_of_le hji with hj | hj
    · exact h j hj
    · exact (Fin.ext hj).symm ▸ hi

theorem seven_conditions (c : Fin 7 → Prop) : through c 6 ↔ ∀ i, c i := by
  constructor
  · intro h i
    exact h i (Nat.le_of_lt_succ i.isLt)
  · intro h i _
    exact h i

end LCTR.CoreComparisonInterfaces
