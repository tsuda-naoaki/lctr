import Init

namespace LCTR.StructuralBurdenSingletonCurrentPaper

abbrev Region (α : Type u) := α → Prop

def Singleton {α : Type u} (item : α) : Region α :=
  fun candidate => candidate = item

def Descendants
    {Token : Type u}
    (dependency : Token → Token → Prop)
    (root : Token) : Region Token :=
  fun token => dependency root token

def Image
    {Token : Type u}
    {Structure : Type v}
    (structureOf : Token → Structure)
    (tokens : Region Token) : Region Structure :=
  fun target => ∃ token, tokens token ∧ structureOf token = target

def StructuralBurden
    {Token : Type u}
    {Structure : Type v}
    (dependency : Token → Token → Prop)
    (structureOf : Token → Structure)
    (failed : Region Token) : Region Structure :=
  fun target =>
    ∃ root, failed root ∧ Image structureOf (Descendants dependency root) target

theorem singleton_structural_burden_membership
    {Token : Type u}
    {Structure : Type v}
    (dependency : Token → Token → Prop)
    (structureOf : Token → Structure)
    (root : Token)
    (target : Structure) :
    StructuralBurden dependency structureOf (Singleton root) target ↔
      Image structureOf (Descendants dependency root) target := by
  constructor
  · rintro ⟨candidate, hCandidate, hTarget⟩
    unfold Singleton at hCandidate
    subst candidate
    exact hTarget
  · intro hTarget
    exact ⟨root, rfl, hTarget⟩

#print axioms singleton_structural_burden_membership

end LCTR.StructuralBurdenSingletonCurrentPaper
