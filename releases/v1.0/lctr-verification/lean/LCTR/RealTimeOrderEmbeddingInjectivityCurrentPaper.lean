import LCTR.OrderEmbeddingInjectivity

namespace LCTR.CurrentPaperCorrespondence

universe u v

 
def IsStrictOrderEmbedding
    {Source : Type u}
    {Target : Type v}
    (sourceLt : Source → Source → Prop)
    (targetLt : Target → Target → Prop)
    (embedding : Source → Target) : Prop :=
  ∀ left right, sourceLt left right ↔ targetLt (embedding left) (embedding right)









theorem real_time_order_embedding_member_injective
    {Source : Type u}
    {Target : Type v}
    (sourceLt : Source → Source → Prop)
    (targetLt : Target → Target → Prop)
    (hTargetIrreflexive : ∀ target, ¬ targetLt target target)
    (hSourceTrichotomy :
      ∀ left right,
        left = right ∨ sourceLt left right ∨ sourceLt right left)
    (hEmbeddingExists :
      ∃ embedding : Source → Target,
        IsStrictOrderEmbedding sourceLt targetLt embedding)
    (rho : Source → Target)
    (hRho : IsStrictOrderEmbedding sourceLt targetLt rho) :
    Function.Injective rho := by
  have _ := hEmbeddingExists
  exact OrderEmbedding.strict_order_preserving_comparable_map_injective
    sourceLt
    targetLt
    rho
    hTargetIrreflexive
    hSourceTrichotomy
    (fun left right hOrder => (hRho left right).mp hOrder)

#print axioms real_time_order_embedding_member_injective

end LCTR.CurrentPaperCorrespondence
