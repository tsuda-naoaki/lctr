import Mathlib.Data.Set.Lattice

namespace LCTR.CoreRelativeInitial
set_option autoImplicit false
universe u
variable {T : Type u}

def Initial (A : Set T) (r : T → T → Prop) (I : Set T) : Prop :=
  ∀ x ∈ A, ∀ y ∈ I, r x y → x ∈ I
def Family (A V : Set T) (r : T → T → Prop) : Set (Set T) :=
  {I | I ⊆ V ∧ Initial A r I}
def Greatest (F : Set (Set T)) (I : Set T) : Prop :=
  I ∈ F ∧ ∀ J ∈ F, J ⊆ I
def Endpoint (r : T → T → Prop) (I : Set T) (a : T) : Prop :=
  a ∈ I ∧ ∀ x ∈ I, r x a

theorem empty_initial (A V : Set T) (r : T → T → Prop) :
    (∅ : Set T) ∈ Family A V r := by
  constructor
  · exact Set.empty_subset V
  · intro x hx y hy; exact False.elim hy

theorem union_initial (A V : Set T) (r : T → T → Prop) :
    ⋃₀ Family A V r ∈ Family A V r := by
  constructor
  · rintro x ⟨I,hI,hx⟩; exact hI.1 hx
  · intro x hx y hy hxy
    obtain ⟨I,hI,hy⟩ := hy
    exact ⟨I,hI,hI.2 x hx y hy hxy⟩

theorem union_greatest (A V : Set T) (r : T → T → Prop) :
    Greatest (Family A V r) (⋃₀ Family A V r) := by
  refine ⟨union_initial A V r,?_⟩
  intro J hJ x hx; exact ⟨J,hJ,hx⟩

theorem mono_identifies (A V : Set T) (r : T → T → Prop)
    (mono : Initial A r V) : ⋃₀ Family A V r = V := by
  apply Set.Subset.antisymm (union_initial A V r).1
  exact (union_greatest A V r).2 V ⟨Set.Subset.rfl,mono⟩

theorem maximum_unique (F : Set (Set T)) (I J : Set T)
    (hI : Greatest F I) (hJ : Greatest F J) : I = J :=
  Set.Subset.antisymm (hJ.2 I hI.1) (hI.2 J hJ.1)

theorem endpoint_characterization (r : T → T → Prop) (I : Set T) :
    (∃ a, Endpoint r I a) ↔ ∃ a ∈ I, ∀ x ∈ I, r x a := Iff.rfl

end LCTR.CoreRelativeInitial
