import CoreDifferentialRefinement

namespace LCTR.CoreDifferentialOutput
set_option autoImplicit false
open Set LCTR.SelectedInputEvaluation LCTR.DifferentialNativeDomains
open LCTR.CoreDifferentialFailure LCTR.CoreDifferentialRefinement
variable {E Law Ω : Type} {law : Selected E Law}
variable (s : MatchingDifferential E Law (Input Ω) law) (operative : Law → Prop) (S : Set E)
variable {J : Fin 5 → Type} (children : (i : Fin 5) → J i → Set E)

structure Output (E : Type) where
  dag : Node → Node → Prop
  parents : Node → Set E
  remainders : Node → Set E
  signatures : E → Node → Bool

noncomputable def output : Output E where
  dag := Edge
  parents := parent s operative S
  remainders := fun i => parent s operative S i \ ⋃ j, children i j
  signatures := signature s operative

def Represents (o : Output E) : Prop :=
  o.dag = Edge ∧ o.parents = parent s operative S ∧
  o.remainders = (fun i => parent s operative S i \ ⋃ j, children i j) ∧
  o.signatures = signature s operative

theorem output_unique : ∃! o : Output E, Represents s operative S children o := by
  refine ⟨output s operative S children,⟨rfl,rfl,rfl,rfl⟩,?_⟩
  rintro ⟨g,p,r,b⟩ ⟨hg,hp,hr,hb⟩
  change g = Edge at hg
  change p = parent s operative S at hp
  change r = (fun i => parent s operative S i \ ⋃ j, children i j) at hr
  change b = signature s operative at hb
  subst g; subst p; subst r; subst b
  rfl

theorem parent_signature_correspondence (i : Node) (ev : E) :
    ev ∈ (output s operative S children).parents i ↔
      ev ∈ S ∧ (output s operative S children).signatures ev i = true := by
  classical
  simp [output,parent,signature]

theorem output_parent_cover :
    (⋃ i, (output s operative S children).parents i) = {ev | ev ∈ S ∧ failure s operative ev} :=
  parents_cover s operative S

theorem remainder_subset_parent (i : Node) :
    (output s operative S children).remainders i ⊆ (output s operative S children).parents i :=
  fun _ h => h.1

theorem children_and_remainder (sub : ∀ i j, children i j ⊆ parent s operative S i) (i : Node) :
    (output s operative S children).parents i =
      (⋃ j, children i j) ∪ (output s operative S children).remainders i ∧
    Disjoint (⋃ j, children i j) ((output s operative S children).remainders i) := by
  constructor
  · ext ev
    change ev ∈ parent s operative S i ↔
      ev ∈ (⋃ j, children i j) ∨ (ev ∈ parent s operative S i ∧ ev ∉ ⋃ j, children i j)
    constructor
    · intro hp
      by_cases hc : ev ∈ ⋃ j, children i j
      · exact Or.inl hc
      · exact Or.inr ⟨hp,hc⟩
    · rintro (hc | ⟨hp,_⟩)
      · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hc
        exact sub i j hj
      · exact hp
  · apply Set.disjoint_left.mpr
    exact fun _ hc hr => hr.2 hc

theorem output_signature_nonzero (ev : E) :
    (output s operative S children).signatures ev ≠ (fun _ => false) ↔ failure s operative ev :=
  signature_nonzero s operative ev

theorem parent_indices_antichain (ev : E) (i j : Node)
    (hi : ev ∈ (output s operative S children).parents i)
    (hj : ev ∈ (output s operative S children).parents j) :
    ¬ Relation.TransGen ((output s operative S children).dag) i j ∧
    ¬ Relation.TransGen ((output s operative S children).dag) j i :=
  minimal_antichain s operative ev i j hi.2 hj.2

end LCTR.CoreDifferentialOutput
