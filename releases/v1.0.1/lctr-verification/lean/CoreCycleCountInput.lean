import Mathlib.Data.Nat.Basic

namespace LCTR.CoreCycleCountInput
set_option autoImplicit false
universe u v

structure Source (Phase : Type u) (Display : Type v) where
  phase : Nat → Phase
  display : Nat → Display

def update (k : Nat) : Nat := k + 1
def state {P : Type u} {D : Type v} (s : Source P D) (k : Nat) :=
  (k,s.phase k,s.display k)

theorem counter_update (k : Nat) : update k = k + 1 := rfl
theorem counter_distinction (k j : Nat) : update k = update j ↔ k = j := by
  simp only [update,Nat.add_right_cancel_iff]
theorem phase_display_correspondence {P : Type u} {D : Type v} (s : Source P D) (k : Nat) :
    state s k = (k,s.phase k,s.display k) := rfl
theorem updated_correspondence {P : Type u} {D : Type v} (s : Source P D) (k : Nat) :
    state s (update k) = (k+1,s.phase (k+1),s.display (k+1)) := rfl
theorem repeated_display_allowed :
    ∃ s : Source Unit Unit, s.display 0 = s.display 1 ∧ state s 0 ≠ state s 1 := by
  refine ⟨⟨fun _ => (),fun _ => ()⟩,rfl,?_⟩
  intro h
  have h01 : (0 : Nat) = 1 := congrArg Prod.fst h
  exact Nat.zero_ne_one h01

end LCTR.CoreCycleCountInput
