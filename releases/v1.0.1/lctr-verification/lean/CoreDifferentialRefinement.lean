import CoreDifferentialFailure
import CoreRefinementForest

namespace LCTR.CoreDifferentialRefinement
set_option autoImplicit false
open Set LCTR.SelectedInputEvaluation LCTR.DifferentialNativeDomains
open LCTR.CoreDifferentialFailure
open LCTR.CoreRefinementForest (Regions asForest covered unrefined ChildEdge)
variable {E Law Ω : Type} {law : Selected E Law}
variable (s : MatchingDifferential E Law (Input Ω) law) (operative : Law → Prop) (S : Set E)

def parent (i : Fin 5) : Set E := {e | e ∈ S ∧ minimalFailure s operative e i}
theorem parent_source_exact (i : Fin 5) :
    parent s operative S i = {e | e ∈ S ∧ failure s operative e ∧ minimalFailure s operative e i} := by
  ext e
  exact ⟨fun h => ⟨h.1,(failure_cover s operative e).mpr ⟨i,h.2⟩,h.2⟩,
    fun h => ⟨h.1,h.2.2⟩⟩
theorem parent_subset_evaluation (i : Fin 5) : parent s operative S i ⊆ S := fun _ h => h.1
theorem parent_requires_selection (i : Fin 5) :
    parent s operative S i ⊆ {e | s.domain e} := fun _ h => h.2.1.1.choose
theorem parents_cover :
    (⋃ i, parent s operative S i) = {e | e ∈ S ∧ failure s operative e} := by
  ext e
  simp only [mem_iUnion,parent,mem_ofPred_eq]
  constructor
  · rintro ⟨i,hs,hm⟩
    exact ⟨hs,(failure_cover s operative e).mpr ⟨i,hm⟩⟩
  · rintro ⟨hs,hf⟩
    obtain ⟨i,hm⟩ := (failure_cover s operative e).mp hf
    exact ⟨i,hs,hm⟩

variable {J : Fin 5 → Type} {K : (i : Fin 5) → J i → Type}
variable (first : (i : Fin 5) → J i → Set E)
variable (second : (i : Fin 5) → (j : J i) → K i j → Set E)
variable (firstSub : ∀ i j, first i j ⊆ parent s operative S i)
variable (secondSub : ∀ i j k, second i j k ⊆ first i j)

def regions : Regions E (Fin 5) J K :=
  ⟨parent s operative S,first,second,firstSub,secondSub⟩

theorem child_and_remainder_typing (i : Fin 5) (j : J i) :
    first i j ⊆ parent s operative S i ∧
    unrefined (asForest (regions s operative S first second firstSub secondSub)) (.root i) ⊆
      parent s operative S i := ⟨firstSub i j,fun _ h => h.1⟩

theorem all_node_decompositions :
    let F := asForest (regions s operative S first second firstSub secondSub)
    ∀ n, F.region n = covered F n ∪ unrefined F n ∧ Disjoint (covered F n) (unrefined F n) :=
  fun n => LCTR.CoreRefinementForest.node_decomposition _ n

theorem conditional_disjoint_children :
    let F := asForest (regions s operative S first second firstSub secondSub)
    ∀ n, (∀ i j : F.Child n, i ≠ j → Disjoint (F.region (F.descend n i)) (F.region (F.descend n j))) →
      (∀ i j : F.Child n, i ≠ j → Disjoint (F.region (F.descend n i)) (F.region (F.descend n j))) ∧
      (∀ i : F.Child n, Disjoint (F.region (F.descend n i)) (unrefined F n)) :=
  fun n hp => LCTR.CoreRefinementForest.child_family_with_remainder _ n hp

theorem ancestor_region_inclusion :
    let F := asForest (regions s operative S first second firstSub secondSub)
    ∀ n m, Relation.ReflTransGen (ChildEdge F) n m → F.region m ⊆ F.region n :=
  fun _ _ h => LCTR.CoreRefinementForest.ancestor_inclusion _ h

theorem second_level_terminal (i : Fin 5) (j : J i) (k : K i j) :
    let F := asForest (regions s operative S first second firstSub secondSub)
    covered F (.second i j k) = ∅ ∧ unrefined F (.second i j k) = second i j k :=
  LCTR.CoreRefinementForest.two_level_leaf _ i j k

theorem root_split_exact (i : Fin 5) :
    let F := asForest (regions s operative S first second firstSub secondSub)
    covered F (.root i) = ⋃ j, first i j ∧
      unrefined F (.root i) = parent s operative S i \ (⋃ j, first i j) := ⟨rfl,rfl⟩

theorem first_split_exact (i : Fin 5) (j : J i) :
    let F := asForest (regions s operative S first second firstSub secondSub)
    covered F (.first i j) = ⋃ k, second i j k ∧
      unrefined F (.first i j) = first i j \ (⋃ k, second i j k) := ⟨rfl,rfl⟩

theorem root_snapshot_monotonicity (i : Fin 5) {J0 J1 : Type}
    (r0 : J0 → Set E) (r1 : J1 → Set E) (embed : J0 → J1)
    (same : ∀ j, r0 j = r1 (embed j)) :
    (⋃ j, r0 j) ⊆ (⋃ j, r1 j) ∧
      parent s operative S i \ (⋃ j, r1 j) ⊆ parent s operative S i \ (⋃ j, r0 j) :=
  LCTR.CoreRefinementForest.snapshot_monotonicity _ r0 r1 embed same

end LCTR.CoreDifferentialRefinement
