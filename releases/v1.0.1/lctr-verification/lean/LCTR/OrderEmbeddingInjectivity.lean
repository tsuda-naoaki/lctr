import LCTR.RefinementDecompositionMonotonicity

namespace LCTR.OrderEmbedding

universe u v








theorem strict_order_preserving_comparable_map_injective
    {Source : Type u}
    {Target : Type v}
    (sourceLt : Source → Source → Prop)
    (targetLt : Target → Target → Prop)
    (embedding : Source → Target)
    (hTargetIrreflexive : ∀ target, ¬ targetLt target target)
    (hSourceTrichotomy :
      ∀ left right,
        left = right ∨ sourceLt left right ∨ sourceLt right left)
    (hStrictOrderPreserving :
      ∀ left right, sourceLt left right →
        targetLt (embedding left) (embedding right)) :
    Function.Injective embedding := by
  intro left right hImage
  rcases hSourceTrichotomy left right with hEqual | hOrdered
  · exact hEqual
  · rcases hOrdered with hLeftRight | hRightLeft
    · have hTarget := hStrictOrderPreserving left right hLeftRight
      rw [hImage] at hTarget
      exact False.elim (hTargetIrreflexive (embedding right) hTarget)
    · have hTarget := hStrictOrderPreserving right left hRightLeft
      rw [hImage] at hTarget
      exact False.elim (hTargetIrreflexive (embedding right) hTarget)

end LCTR.OrderEmbedding
