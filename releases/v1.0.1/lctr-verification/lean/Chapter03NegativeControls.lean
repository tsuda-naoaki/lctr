import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import «Chapter03SourceOrderRecovery»

open LCTR.Chapter03SourceOrderRecovery

namespace LCTR.Chapter03SourceOrderRecovery.NegativeControls

def twoSourceOneArrival : PartialArrival Bool Unit where
  dom := Set.univ
  val := fun _ _ => ()

theorem two_source_one_arrival_not_uniquely_recoverable :
    ¬ UniqueRecoverable twoSourceOneArrival () := by
  intro h
  let x : {x : Bool // x ∈ twoSourceOneArrival.dom} :=
    ⟨false, by simp [twoSourceOneArrival]⟩
  let y : {x : Bool // x ∈ twoSourceOneArrival.dom} :=
    ⟨true, by simp [twoSourceOneArrival]⟩
  have hxy : x = y := h.2 x y (by rfl) (by rfl)
  have hfalse : false = true := congrArg Subtype.val hxy
  cases hfalse

def overlappingCells : Bool → Finset Bool
  | false => {false, true}
  | true => {true}

theorem missing_class_condition_allows_overlap :
    (∀ x, x ∈ overlappingCells x) ∧
    (∀ x, (overlappingCells x).Nonempty) ∧
    ∃ x y z, z ∈ overlappingCells x ∧ z ∈ overlappingCells y ∧
      overlappingCells x ≠ overlappingCells y := by
  constructor
  · intro x
    cases x <;> simp [overlappingCells]
  constructor
  · intro x
    cases x <;> simp [overlappingCells]
  · refine ⟨false, true, true, ?_, ?_, ?_⟩
    · simp [overlappingCells]
    · simp [overlappingCells]
    · simp [overlappingCells]

def emptyArrival : PartialArrival Nat Unit where
  dom := ∅
  val := by
    intro x hx
    exact False.elim (by simpa using hx)

theorem empty_arrival_has_no_recoverable_value :
    ∀ a : Unit, ¬ UniqueRecoverable emptyArrival a := by
  intro a h
  rcases h.1 with ⟨x, _⟩
  simpa [emptyArrival] using x.property

end LCTR.Chapter03SourceOrderRecovery.NegativeControls
