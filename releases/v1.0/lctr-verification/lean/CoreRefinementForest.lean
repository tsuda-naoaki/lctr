import CoreComparisonFailure
import Mathlib.Data.Set.Lattice

namespace LCTR.CoreRefinementForest
set_option autoImplicit false
open Set LCTR.CoreTokenGraph LCTR.CoreFiniteAudit LCTR.CoreComparisonFailure

structure Forest (N E : Type) where
  Child : N → Type
  descend : (n : N) → Child n → N
  region : N → Set E
  child_subset : ∀ n i, region (descend n i) ⊆ region n

def covered {N E : Type} (F : Forest N E) (n : N) : Set E := ⋃ i, F.region (F.descend n i)
def unrefined {N E : Type} (F : Forest N E) (n : N) : Set E := F.region n \ covered F n
def ChildEdge {N E : Type} (F : Forest N E) (n m : N) : Prop := ∃ i, m = F.descend n i

theorem covered_subset {N E : Type} (F : Forest N E) (n : N) : covered F n ⊆ F.region n := by
  intro x hx
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
  exact F.child_subset n i hi

theorem node_decomposition {N E : Type} (F : Forest N E) (n : N) :
    F.region n = covered F n ∪ unrefined F n ∧ Disjoint (covered F n) (unrefined F n) := by
  constructor
  · ext x
    constructor
    · intro hx
      by_cases hc : x ∈ covered F n
      · exact Or.inl hc
      · exact Or.inr ⟨hx,hc⟩
    · rintro (hx | hx)
      · exact covered_subset F n hx
      · exact hx.1
  · exact Set.disjoint_left.mpr (fun _ hc hu => hu.2 hc)

theorem child_family_with_remainder {N E : Type} (F : Forest N E) (n : N)
    (pairwise : ∀ i j : F.Child n, i ≠ j →
      Disjoint (F.region (F.descend n i)) (F.region (F.descend n j))) :
    (∀ i j : F.Child n, i ≠ j → Disjoint (F.region (F.descend n i)) (F.region (F.descend n j))) ∧
    (∀ i : F.Child n, Disjoint (F.region (F.descend n i)) (unrefined F n)) := by
  refine ⟨pairwise,?_⟩
  intro i
  exact Set.disjoint_left.mpr (fun _ hi hu => hu.2 (Set.mem_iUnion.mpr ⟨i,hi⟩))

theorem ancestor_inclusion {N E : Type} (F : Forest N E) {n m : N}
    (h : Relation.ReflTransGen (ChildEdge F) n m) : F.region m ⊆ F.region n := by
  induction h with
  | refl => exact Set.Subset.rfl
  | tail _ h ih =>
    obtain ⟨i,rfl⟩ := h
    exact (F.child_subset _ i).trans ih

theorem snapshot_monotonicity {E J K : Type} (P : Set E)
    (r : J → Set E) (s : K → Set E) (embed : J → K)
    (same : ∀ i, r i = s (embed i)) :
    (⋃ i, r i) ⊆ (⋃ j, s j) ∧ P \ (⋃ j, s j) ⊆ P \ (⋃ i, r i) := by
  have sub : (⋃ i, r i) ⊆ (⋃ j, s j) := by
    intro x hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨embed i,(same i) ▸ hi⟩
  exact ⟨sub,fun _ h => ⟨h.1,fun bad => h.2 (sub bad)⟩⟩

inductive Node (I : Type) (J : I → Type) (K : (i : I) → J i → Type) where
  | root (i : I)
  | first (i : I) (j : J i)
  | second (i : I) (j : J i) (k : K i j)

variable {I E : Type} {J : I → Type} {K : (i : I) → J i → Type}

def children : Node I J K → Type
  | .root i => J i
  | .first i j => K i j
  | .second _ _ _ => Empty

def descend : (n : Node I J K) → children n → Node I J K
  | .root i,j => .first i j
  | .first i j,k => .second i j k
  | .second _ _ _,x => nomatch x

def depth : Node I J K → ℕ
  | .root _ => 0
  | .first _ _ => 1
  | .second _ _ _ => 2

structure Regions (E I : Type) (J : I → Type) (K : (i : I) → J i → Type) where
  root : I → Set E
  first : (i : I) → J i → Set E
  second : (i : I) → (j : J i) → K i j → Set E
  first_subset : ∀ i j, first i j ⊆ root i
  second_subset : ∀ i j k, second i j k ⊆ first i j

def region (r : Regions E I J K) : Node I J K → Set E
  | .root i => r.root i
  | .first i j => r.first i j
  | .second i j k => r.second i j k

def asForest (r : Regions E I J K) : Forest (Node I J K) E where
  Child := children
  descend := descend
  region := region r
  child_subset := by
    intro n l
    cases n with
    | root i => exact r.first_subset i l
    | first i j => exact r.second_subset i j l
    | second i j k => exact nomatch l

theorem two_level_child_depth (r : Regions E I J K) {n m : Node I J K}
    (h : ChildEdge (asForest r) n m) : depth m = depth n + 1 := by
  obtain ⟨l,rfl⟩ := h
  cases n with
  | root i => rfl
  | first i j => rfl
  | second i j k => exact nomatch l

theorem two_level_acyclic (r : Regions E I J K) (n : Node I J K) :
    ¬ Relation.TransGen (ChildEdge (asForest r)) n n := by
  intro h
  have lt := LCTR.CoreTokenGraph.path_increases (ChildEdge (asForest r)) (· < ·) depth
    (fun _ _ h => by rw [two_level_child_depth r h]; omega) h
  exact Nat.lt_irrefl _ lt

theorem two_level_leaf (r : Regions E I J K) (i : I) (j : J i) (k : K i j) :
    covered (asForest r) (.second i j k) = ∅ ∧
    unrefined (asForest r) (.second i j k) = r.second i j k := by
  have empty : covered (asForest r) (.second i j k) = ∅ := by
    ext x
    constructor
    · intro hx
      obtain ⟨l,_⟩ := Set.mem_iUnion.mp hx
      exact nomatch l
    · simp
  refine ⟨empty,?_⟩
  rw [unrefined,empty,Set.sdiff_empty]
  rfl

def comparisonRegions {E : Type} {J : Fin 8 → Type} {K : (i : Fin 8) → J i → Type}
    (f e c : E → Token → Bool)
    (first : (i : Fin 8) → J i → Set E)
    (second : (i : Fin 8) → (j : J i) → K i j → Set E)
    (first_sub : ∀ i j, first i j ⊆ {x | run (f x) (e x) (c x) 40 (cmpToken i) = .failed})
    (second_sub : ∀ i j k, second i j k ⊆ first i j) : Regions E (Fin 8) J K :=
  ⟨fun i => {x | run (f x) (e x) (c x) 40 (cmpToken i) = .failed},first,second,first_sub,second_sub⟩

theorem native_comparison_forest_laws {E : Type} {J : Fin 8 → Type} {K : (i : Fin 8) → J i → Type}
    (f e c : E → Token → Bool)
    (first : (i : Fin 8) → J i → Set E)
    (second : (i : Fin 8) → (j : J i) → K i j → Set E)
    (first_sub : ∀ i j, first i j ⊆ {x | run (f x) (e x) (c x) 40 (cmpToken i) = .failed})
    (second_sub : ∀ i j k, second i j k ⊆ first i j) :
    let F := asForest (comparisonRegions f e c first second first_sub second_sub)
    (∀ n, F.region n = covered F n ∪ unrefined F n ∧ Disjoint (covered F n) (unrefined F n)) ∧
    (∀ n m, Relation.ReflTransGen (ChildEdge F) n m → F.region m ⊆ F.region n) := by
  exact ⟨fun n => node_decomposition _ n,fun _ _ h => ancestor_inclusion _ h⟩

end LCTR.CoreRefinementForest
