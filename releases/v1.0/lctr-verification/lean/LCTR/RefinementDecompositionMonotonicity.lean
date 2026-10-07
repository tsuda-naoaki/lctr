import LCTR.RefinementMonotonicity

namespace LCTR.Refinement

universe u v

 
def union {Point : Type u} (left right : Region Point) : Region Point :=
  fun point => left point ∨ right point

 
def Disjoint {Point : Type u} (left right : Region Point) : Prop :=
  ∀ point, ¬ (left point ∧ right point)

 
def PairwiseDisjoint
    {Point : Type u}
    {Index : Type v}
    (subIdx : Index → Prop)
    (subReg : Index → Region Point) : Prop :=
  ∀ leftIndex rightIndex,
    subIdx leftIndex →
    subIdx rightIndex →
    leftIndex ≠ rightIndex →
    Disjoint (subReg leftIndex) (subReg rightIndex)

 
def DisjointDecomposition
    {Point : Type u}
    (parentReg coveredReg unrefinedReg : Region Point) : Prop :=
  parentReg = union coveredReg unrefinedReg ∧
    Disjoint coveredReg unrefinedReg

 
def DisjointFamilyWithRemainder
    {Point : Type u}
    {Index : Type v}
    (subIdx : Index → Prop)
    (subReg : Index → Region Point)
    (remainder : Region Point) : Prop :=
  PairwiseDisjoint subIdx subReg ∧
    ∀ index, subIdx index → Disjoint (subReg index) remainder

theorem covered_unrefined_decomposition
    {Point : Type u}
    {Index : Type v}
    (parentReg : Region Point)
    (subIdx : Index → Prop)
    (subReg : Index → Region Point)
    (hSubReg : ∀ index, subIdx index → Included (subReg index) parentReg) :
    DisjointDecomposition
      parentReg
      (covered subIdx subReg)
      (unrefined parentReg (covered subIdx subReg)) := by
  classical
  constructor
  · funext point
    apply propext
    constructor
    · intro hParent
      by_cases hCovered : covered subIdx subReg point
      · exact Or.inl hCovered
      · exact Or.inr ⟨hParent, hCovered⟩
    · intro hUnion
      rcases hUnion with hCovered | hUnrefined
      · rcases hCovered with ⟨index, hIndex, hPoint⟩
        exact hSubReg index hIndex point hPoint
      · exact hUnrefined.1
  · intro point hIntersection
    exact hIntersection.2.2 hIntersection.1

theorem pairwise_family_with_unrefined_remainder
    {Point : Type u}
    {Index : Type v}
    (parentReg : Region Point)
    (subIdx : Index → Prop)
    (subReg : Index → Region Point)
    (hPairwise : PairwiseDisjoint subIdx subReg) :
    DisjointFamilyWithRemainder
      subIdx
      subReg
      (unrefined parentReg (covered subIdx subReg)) := by
  refine ⟨hPairwise, ?_⟩
  intro index hIndex point hIntersection
  exact hIntersection.2.2 ⟨index, hIndex, hIntersection.1⟩








theorem covered_unrefined_decomposition_and_refinement_monotonicity
    {Point : Type u}
    {Index : Type v}
    (parentReg : Region Point)
    (subIdx0 subIdx1 : Index → Prop)
    (subReg0 subReg1 : Index → Region Point)
    (hIndex : ∀ index, subIdx0 index → subIdx1 index)
    (hShared : ∀ index, subIdx0 index → subReg0 index = subReg1 index)
    (hSubReg0 : ∀ index, subIdx0 index → Included (subReg0 index) parentReg)
    (hSubReg1 : ∀ index, subIdx1 index → Included (subReg1 index) parentReg) :
    DisjointDecomposition
        parentReg
        (covered subIdx0 subReg0)
        (unrefined parentReg (covered subIdx0 subReg0)) ∧
      DisjointDecomposition
        parentReg
        (covered subIdx1 subReg1)
        (unrefined parentReg (covered subIdx1 subReg1)) ∧
      (PairwiseDisjoint subIdx0 subReg0 →
        DisjointFamilyWithRemainder
          subIdx0
          subReg0
          (unrefined parentReg (covered subIdx0 subReg0))) ∧
      (PairwiseDisjoint subIdx1 subReg1 →
        DisjointFamilyWithRemainder
          subIdx1
          subReg1
          (unrefined parentReg (covered subIdx1 subReg1))) ∧
      Included (covered subIdx0 subReg0) (covered subIdx1 subReg1) ∧
      Included
        (unrefined parentReg (covered subIdx1 subReg1))
        (unrefined parentReg (covered subIdx0 subReg0)) := by
  have hMonotonicity :=
    covered_unrefined_refinement_monotonicity
      parentReg subIdx0 subIdx1 subReg0 subReg1
      hIndex hShared hSubReg0 hSubReg1
  exact ⟨
    covered_unrefined_decomposition parentReg subIdx0 subReg0 hSubReg0,
    covered_unrefined_decomposition parentReg subIdx1 subReg1 hSubReg1,
    pairwise_family_with_unrefined_remainder parentReg subIdx0 subReg0,
    pairwise_family_with_unrefined_remainder parentReg subIdx1 subReg1,
    hMonotonicity.1,
    hMonotonicity.2
  ⟩

end LCTR.Refinement
