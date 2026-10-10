import CoreComparisonStage
import LCTR.TaggedArrivalPartition
import LCTR.RefinementDecompositionMonotonicity
import Mathlib.Data.Set.Lattice

namespace LCTR.CoreRemainingSetContracts
set_option autoImplicit false
open Set LCTR.CoreSourceMatch
universe u v w
variable {U : Type u} {S : Fin 2 → Type v} {V : Fin 2 → U → Type w}

def nativeRegion (x : LCTR.CoreComparisonStage.Input U S V) (r : Fin 2) (i : U) :
    Set (Tagged (x.data r).arrival) := LCTR.TaggedArrivalPartition.Region i

theorem native_arrival_cover (x : LCTR.CoreComparisonStage.Input U S V) (r : Fin 2) :
    (⋃ i, nativeRegion x r i) = Set.univ := by
  ext p
  constructor
  · intro _; trivial
  · intro _
    obtain ⟨i,hi⟩ := (LCTR.TaggedArrivalPartition.cover_and_pairwise_disjoint
      (Index := U) (Fiber := fun u => ↥(ImageAt (x.data r).arrival u))).1 p
    exact Set.mem_iUnion.mpr ⟨i,hi⟩

theorem native_arrival_disjoint (x : LCTR.CoreComparisonStage.Input U S V) (r : Fin 2)
    (i j : U) (different : i ≠ j) : nativeRegion x r i ∩ nativeRegion x r j = ∅ := by
  ext p
  constructor
  · intro hp
    exact (LCTR.TaggedArrivalPartition.cover_and_pairwise_disjoint
      (Index := U) (Fiber := fun u => ↥(ImageAt (x.data r).arrival u))).2 i j different p hp
  · intro hp; exact False.elim hp

open LCTR.Refinement

theorem full_refinement_contract {Point : Type u} {Index : Type v}
    (parent : Region Point) (idx0 idx1 : Index → Prop)
    (regions0 regions1 : Index → Region Point)
    (index : ∀ i, idx0 i → idx1 i)
    (shared : ∀ i, idx0 i → regions0 i = regions1 i)
    (within0 : ∀ i, idx0 i → Included (regions0 i) parent)
    (within1 : ∀ i, idx1 i → Included (regions1 i) parent) :
    DisjointDecomposition parent (covered idx0 regions0) (unrefined parent (covered idx0 regions0)) ∧
    DisjointDecomposition parent (covered idx1 regions1) (unrefined parent (covered idx1 regions1)) ∧
    (LCTR.Refinement.PairwiseDisjoint idx0 regions0 →
      DisjointFamilyWithRemainder idx0 regions0 (unrefined parent (covered idx0 regions0))) ∧
    (LCTR.Refinement.PairwiseDisjoint idx1 regions1 →
      DisjointFamilyWithRemainder idx1 regions1 (unrefined parent (covered idx1 regions1))) ∧
    Included (covered idx0 regions0) (covered idx1 regions1) ∧
    Included (unrefined parent (covered idx1 regions1)) (unrefined parent (covered idx0 regions0)) :=
  covered_unrefined_decomposition_and_refinement_monotonicity parent idx0 idx1 regions0 regions1
    index shared within0 within1

end LCTR.CoreRemainingSetContracts
