import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import «Chapter03SourceOrderRecovery»

open LCTR.Chapter03SourceOrderRecovery

namespace LCTR.Chapter03SourceOrderRecovery.PositiveControls

theorem positive_c_distinct_sources_same_nat :
    ((false, 7) : CToken Bool) ≠ ((true, 7) : CToken Bool) := by
  decide

def constantDisplay : CToken Bool → Unit := fun _ => ()

theorem positive_constant_display_preserves_token_identity :
    ((false, 1) : CToken Bool) ≠ ((true, 1) : CToken Bool) := by
  apply ch03_r031_equal_display_does_not_identify_tokens constantDisplay
  · decide
  · rfl

def d0 : DToken Bool := ⟨false, 5⟩
def d1 : DToken Bool := ⟨true, 5⟩

theorem positive_d_distinct_tokens_same_seq : d0 ≠ d1 := by decide

theorem positive_d_equal_seq_incomparable : (¬ DLE d0 d1) ∧ (¬ DLE d1 d0) := by
  apply ch03_r036_d_equal_index_incomparable
  · decide
  · rfl

def emptyArrival : PartialArrival Nat Unit where
  dom := ∅
  val := by
    intro x hx
    exact False.elim (by simpa using hx)

theorem positive_empty_arrival_domain_allowed :
    ¬ ∃ x : {x : Nat // x ∈ emptyArrival.dom}, True := by
  simp [emptyArrival]

end LCTR.Chapter03SourceOrderRecovery.PositiveControls
