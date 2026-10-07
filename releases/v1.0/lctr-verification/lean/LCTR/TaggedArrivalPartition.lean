namespace LCTR.TaggedArrivalPartition

universe u v

 
abbrev Carrier (Index : Type u) (Fiber : Index → Type v) := Sigma Fiber

 
def Region
    {Index : Type u}
    {Fiber : Index → Type v}
    (index : Index) : Carrier Index Fiber → Prop :=
  fun point => point.1 = index







theorem cover_and_pairwise_disjoint
    {Index : Type u}
    {Fiber : Index → Type v} :
    (∀ point : Carrier Index Fiber, ∃ index, Region index point) ∧
      (∀ first second,
        first ≠ second →
        ∀ point : Carrier Index Fiber,
          ¬ (Region first point ∧ Region second point)) := by
  constructor
  · intro point
    exact ⟨point.1, rfl⟩
  · intro first second different point both
    exact different (both.1.symm.trans both.2)

end LCTR.TaggedArrivalPartition

