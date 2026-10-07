import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic

namespace LCTR.CoreRepresentationPredicateBridge
open Set
set_option autoImplicit false
universe u v
variable {S : Type u} {T : Type v}

def eqKernel (f : S → T) : Set (S × S) := {p | f p.1 = f p.2}
def pullback (f : S → T) (lt : Set (T × T)) : Set (S × S) :=
  {p | (f p.1,f p.2) ∈ lt}
def ordRepCond (f : S → T) (E R : Set (S × S)) (lt : Set (T × T)) : Prop :=
  eqKernel f = E ∧ pullback f lt = R

theorem kernel_membership (f : S → T) (x y : S) :
    (x,y) ∈ eqKernel f ↔ f x = f y := Iff.rfl

theorem kernel_equivalence (f : S → T) :
    Equivalence (fun x y => (x,y) ∈ eqKernel f) :=
  ⟨fun _ => rfl,fun h => h.symm,fun hxy hyz => hxy.trans hyz⟩

theorem kernel_set_exact (f : S → T) (E : Set (S × S)) :
    eqKernel f = E ↔ ∀ x y, (f x = f y ↔ (x,y) ∈ E) := by
  constructor
  · intro h x y
    rw [← h]
    exact Iff.rfl
  · intro h
    ext p
    exact h p.1 p.2

theorem pullback_set_exact (f : S → T) (R : Set (S × S)) (lt : Set (T × T)) :
    pullback f lt = R ↔ ∀ x y, ((f x,f y) ∈ lt ↔ (x,y) ∈ R) := by
  constructor
  · intro h x y
    rw [← h]
    exact Iff.rfl
  · intro h
    ext p
    exact h p.1 p.2

theorem representation_condition_exact (f : S → T) (E R : Set (S × S))
    (lt : Set (T × T)) :
    ordRepCond f E R lt ↔
      (∀ x y, f x = f y ↔ (x,y) ∈ E) ∧
      (∀ x y, (f x,f y) ∈ lt ↔ (x,y) ∈ R) := by
  unfold ordRepCond
  rw [kernel_set_exact,pullback_set_exact]

def collapse (_ : Bool) : Nat := 0
def natStrict : Set (Nat × Nat) := {p | p.1 < p.2}

theorem noninjective_control :
    ordRepCond collapse univ ∅ natStrict ∧
    collapse false = collapse true ∧ false ≠ true := by
  refine ⟨?_,rfl,Bool.false_ne_true⟩
  rw [representation_condition_exact]
  simp [collapse,natStrict]

theorem missing_order_control :
    eqKernel collapse = univ ∧
    ¬ ordRepCond collapse univ {p | p.1 = false ∧ p.2 = true} natStrict := by
  refine ⟨?_,?_⟩
  · ext p
    simp [eqKernel,collapse]
  · intro h
    have v := ((representation_condition_exact _ _ _ _).mp h).2 false true
    have bad : (0 : Nat) < 0 := v.mpr ⟨rfl,rfl⟩
    exact Nat.lt_irrefl 0 bad

theorem missing_kernel_control :
    pullback collapse natStrict = ∅ ∧
    ¬ ordRepCond collapse {p | p.1 = p.2} ∅ natStrict := by
  refine ⟨?_,?_⟩
  · ext p
    simp [pullback,collapse,natStrict]
  · intro h
    have v := ((representation_condition_exact _ _ _ _).mp h).1 false true
    have bad : false = true := v.mp rfl
    exact Bool.false_ne_true bad

end LCTR.CoreRepresentationPredicateBridge
