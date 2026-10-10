import CoreRefinementForest

namespace LCTR.CoreRefinementPaths
set_option autoImplicit false
open Set
variable {I L E : Type}
abbrev RawPath (I L : Type) := I × List L
def appendChild (p : RawPath I L) (l : L) : RawPath I L := (p.1,p.2 ++ [l])
def paths (J : RawPath I L → Set L) : ℕ → Set (RawPath I L)
  | 0 => {p | p.2 = []}
  | n+1 => {p | ∃ q ∈ paths J n, ∃ l ∈ J q, p = appendChild q l}
def nodes (J : RawPath I L → Set L) : Set (RawPath I L) := ⋃ n, paths J n
def truncated (J : RawPath I L → Set L) (m : ℕ) : Set (RawPath I L) :=
  {p | ∃ n ≤ m, p ∈ paths J n}
abbrev TaggedTruncated (J : RawPath I L → Set L) (m : ℕ) :=
  (n : Fin (m+1)) × ↥(paths J n.val)
def forgetDepth {J : RawPath I L → Set L} {m : ℕ} (p : TaggedTruncated J m) : RawPath I L := p.2.val

theorem path_zero (J : RawPath I L → Set L) (p : RawPath I L) :
    p ∈ paths J 0 ↔ ∃ i, p = (i,[]) := by
  change p.2 = [] ↔ ∃ i, p = (i,[])
  constructor
  · intro h; exact ⟨p.1, Prod.ext rfl h⟩
  · rintro ⟨i,rfl⟩; rfl
theorem path_successor (J : RawPath I L → Set L) (n : ℕ) (p : RawPath I L) :
    p ∈ paths J (n+1) ↔ ∃ q ∈ paths J n, ∃ l ∈ J q, p = appendChild q l := Iff.rfl
theorem path_length (J : RawPath I L → Set L) (n : ℕ) (p : RawPath I L)
    (h : p ∈ paths J n) : p.2.length = n := by
  induction n generalizing p with
  | zero => change p.2 = [] at h; simp [h]
  | succ n ih =>
    obtain ⟨q,hq,l,_,rfl⟩ := h
    simp [appendChild,ih q hq]
theorem unique_level (J : RawPath I L → Set L) (n m : ℕ) (p : RawPath I L)
    (hn : p ∈ paths J n) (hm : p ∈ paths J m) : n = m :=
  (path_length J n p hn).symm.trans (path_length J m p hm)
theorem nodes_iff (J : RawPath I L → Set L) (p : RawPath I L) :
    p ∈ nodes J ↔ ∃ n, p ∈ paths J n := by simp [nodes]
theorem truncated_exact (J : RawPath I L → Set L) (m : ℕ) (p : RawPath I L) :
    p ∈ truncated J m ↔ p ∈ nodes J ∧ p.2.length ≤ m := by
  constructor
  · rintro ⟨n,hn,hp⟩
    exact ⟨(nodes_iff J p).mpr ⟨n,hp⟩,by rw [path_length J n p hp]; exact hn⟩
  · rintro ⟨hp,hl⟩
    obtain ⟨n,hn⟩ := (nodes_iff J p).mp hp
    exact ⟨n,by rw [← path_length J n p hn]; exact hl,hn⟩
theorem tagged_truncation_injective (J : RawPath I L → Set L) (m : ℕ) :
    Function.Injective (@forgetDepth I L J m) := by
  rintro ⟨n,p⟩ ⟨k,q⟩ h
  change p.val = q.val at h
  have hn : n = k := Fin.ext (unique_level J n k p.val p.property (h.symm ▸ q.property))
  subst k
  have hp : p = q := Subtype.ext h
  subst q
  rfl
theorem tagged_truncation_range (J : RawPath I L → Set L) (m : ℕ) :
    range (@forgetDepth I L J m) = truncated J m := by
  ext p
  constructor
  · rintro ⟨⟨n,q⟩,rfl⟩
    exact ⟨n,by omega,q.property⟩
  · rintro ⟨n,hn,hp⟩
    exact ⟨⟨⟨n,by omega⟩,⟨p,hp⟩⟩,rfl⟩
theorem child_closure (J : RawPath I L → Set L) (p : RawPath I L) (l : L)
    (hp : p ∈ nodes J) (hl : l ∈ J p) : appendChild p l ∈ nodes J := by
  obtain ⟨n,hn⟩ := (nodes_iff J p).mp hp
  exact (nodes_iff J _).mpr ⟨n+1,p,hn,l,hl,rfl⟩

abbrev PathNode (J : RawPath I L → Set L) := ↥(nodes J)
def asForest (J : RawPath I L → Set L) (R : RawPath I L → Set E)
    (within : ∀ p ∈ nodes J, ∀ l ∈ J p, R (appendChild p l) ⊆ R p) :
    LCTR.CoreRefinementForest.Forest (PathNode J) E where
  Child := fun p => ↥(J p.val)
  descend := fun p l => ⟨appendChild p.val l.val,child_closure J p.val l.val p.property l.property⟩
  region := fun p => R p.val
  child_subset := fun p l => within p.val p.property l.val l.property

variable (J : RawPath I L → Set L) (R : RawPath I L → Set E)
  (within : ∀ p ∈ nodes J, ∀ l ∈ J p, R (appendChild p l) ⊆ R p)

theorem child_edge_exact (p q : PathNode J) :
    LCTR.CoreRefinementForest.ChildEdge (asForest J R within) p q ↔
      ∃ l ∈ J p.val, q.val = appendChild p.val l := by
  constructor
  · rintro ⟨l,h⟩; exact ⟨l.val,l.property,congrArg Subtype.val h⟩
  · rintro ⟨l,hl,h⟩; exact ⟨⟨l,hl⟩,Subtype.ext h⟩
theorem child_depth (p q : PathNode J)
    (h : LCTR.CoreRefinementForest.ChildEdge (asForest J R within) p q) :
    q.val.2.length = p.val.2.length + 1 := by
  obtain ⟨l,_,h⟩ := (child_edge_exact J R within p q).mp h
  simp [h,appendChild]
theorem acyclic (p : PathNode J) :
    ¬ Relation.TransGen (LCTR.CoreRefinementForest.ChildEdge (asForest J R within)) p p := by
  intro h
  have lt := LCTR.CoreTokenGraph.path_increases
    (LCTR.CoreRefinementForest.ChildEdge (asForest J R within)) (· < ·)
    (fun q : PathNode J => q.val.2.length)
    (fun a b hab => by rw [child_depth J R within a b hab]; omega) h
  exact Nat.lt_irrefl _ lt
theorem node_decomposition (p : PathNode J) :
    R p.val = LCTR.CoreRefinementForest.covered (asForest J R within) p ∪
      LCTR.CoreRefinementForest.unrefined (asForest J R within) p ∧
    Disjoint (LCTR.CoreRefinementForest.covered (asForest J R within) p)
      (LCTR.CoreRefinementForest.unrefined (asForest J R within) p) :=
  LCTR.CoreRefinementForest.node_decomposition (asForest J R within) p
theorem ancestor_inclusion (p q : PathNode J)
    (h : Relation.ReflTransGen (LCTR.CoreRefinementForest.ChildEdge (asForest J R within)) p q) :
    R q.val ⊆ R p.val := LCTR.CoreRefinementForest.ancestor_inclusion _ h
theorem empty_leaf (p : PathNode J) (leaf : J p.val = ∅) :
    LCTR.CoreRefinementForest.covered (asForest J R within) p = ∅ ∧
    LCTR.CoreRefinementForest.unrefined (asForest J R within) p = R p.val := by
  have emp : LCTR.CoreRefinementForest.covered (asForest J R within) p = ∅ := by
    ext x
    constructor
    · intro hx
      obtain ⟨l,_⟩ := mem_iUnion.mp hx
      have bad : l.val ∈ J p.val := l.property
      exact (le_of_eq leaf : J p.val ⊆ ∅) bad
    · intro hx; exact False.elim hx
  exact ⟨emp,by rw [LCTR.CoreRefinementForest.unrefined,emp,sdiff_empty]; rfl⟩
theorem arbitrary_depth_control (n : ℕ) :
    ((),List.replicate n ()) ∈ paths (fun _ : RawPath Unit Unit => univ) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine ⟨((),List.replicate n ()),ih,(),mem_univ _,?_⟩
    change ((),List.replicate (n+1) ()) = ((),List.replicate n () ++ [()])
    rw [List.replicate_add]
    rfl

end LCTR.CoreRefinementPaths
