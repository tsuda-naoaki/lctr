import Mathlib.Data.Set.Basic

namespace LCTR.CoreScopeInputInterfaces
open Set
set_option autoImplicit false
universe u v

def restrictRelation {S : Type u} (r : Set (S × S)) (A : Set S) : Set (S × S) :=
  r ∩ (A ×ˢ A)

theorem restriction_membership {S : Type u} (r : Set (S × S)) (A : Set S) (x y : S) :
    (x,y) ∈ restrictRelation r A ↔ (x,y) ∈ r ∧ x ∈ A ∧ y ∈ A := Iff.rfl

theorem restriction_subtype {S : Type u} (r : Set (S × S)) (A : Set S) (x y : A) :
    (x.val,y.val) ∈ restrictRelation r A ↔ (x.val,y.val) ∈ r := by
  exact ⟨fun h => h.1, fun h => ⟨h,x.property,y.property⟩⟩

theorem support_selection {J : Type u} {Carrier : Type v}
    (I : Set J) (C : Set Carrier) (supports : J → Carrier → Prop) :
    (∀ i ∈ I, ∃ c ∈ C, supports i c) ↔
      ∃ f : I → C, ∀ i, supports i.val (f i).val := by
  classical
  constructor
  · intro h
    have typed : ∀ i : I, ∃ c : C, supports i.val c.val := by
      intro i
      obtain ⟨c,hc,hs⟩ := h i.val i.property
      exact ⟨⟨c,hc⟩,hs⟩
    exact ⟨fun i => (typed i).choose, fun i => (typed i).choose_spec⟩
  · rintro ⟨f,hf⟩ i hi
    exact ⟨(f ⟨i,hi⟩).val,(f ⟨i,hi⟩).property,hf ⟨i,hi⟩⟩

theorem shared_carrier_distinct_sources :
    ∃ carrier : Bool → Unit, carrier false = carrier true ∧
      ((false,0) : Bool × Nat) ≠ ((true,0) : Bool × Nat) := by
  refine ⟨fun _ => (),rfl,?_⟩
  intro h
  have hft : false = true := congrArg Prod.fst h
  cases hft

end LCTR.CoreScopeInputInterfaces
