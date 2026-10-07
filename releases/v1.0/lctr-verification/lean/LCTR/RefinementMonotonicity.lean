import Std

namespace LCTR.Refinement

universe u v

 
abbrev Region (Point : Type u) := Point → Prop

 
def Included {Point : Type u} (left right : Region Point) : Prop :=
  ∀ point, left point → right point

 
def covered
    {Point : Type u}
    {Index : Type v}
    (subIdx : Index → Prop)
    (subReg : Index → Region Point) : Region Point :=
  fun point => ∃ index, subIdx index ∧ subReg index point

 
def unrefined
    {Point : Type u}
    (parentReg coveredReg : Region Point) : Region Point :=
  fun point => parentReg point ∧ ¬ coveredReg point









theorem covered_unrefined_refinement_monotonicity
    {Point : Type u}
    {Index : Type v}
    (parentReg : Region Point)
    (subIdx0 subIdx1 : Index → Prop)
    (subReg0 subReg1 : Index → Region Point)
    (hIndex : ∀ index, subIdx0 index → subIdx1 index)
    (hShared : ∀ index, subIdx0 index → subReg0 index = subReg1 index)
    (_hSubReg0 : ∀ index, subIdx0 index → Included (subReg0 index) parentReg)
    (_hSubReg1 : ∀ index, subIdx1 index → Included (subReg1 index) parentReg) :
    Included (covered subIdx0 subReg0) (covered subIdx1 subReg1) ∧
      Included
        (unrefined parentReg (covered subIdx1 subReg1))
        (unrefined parentReg (covered subIdx0 subReg0)) := by
  have hCovered :
      Included (covered subIdx0 subReg0) (covered subIdx1 subReg1) := by
    intro point hPoint
    rcases hPoint with ⟨index, hIndex0, hPointInSubReg0⟩
    refine ⟨index, hIndex index hIndex0, ?_⟩
    simpa [hShared index hIndex0] using hPointInSubReg0
  refine ⟨hCovered, ?_⟩
  intro point hPoint
  refine ⟨hPoint.1, ?_⟩
  intro hPointInCovered0
  exact hPoint.2 (hCovered point hPointInCovered0)

end LCTR.Refinement
