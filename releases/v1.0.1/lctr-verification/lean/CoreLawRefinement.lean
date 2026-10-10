import CoreLawCounterCases
import CoreRefinementForest
import Mathlib.Data.Fin.VecNotation

namespace LCTR.CoreLawRefinement
set_option autoImplicit false
open Set LCTR.LawFamilyTransport LCTR.CoreLawCounterCases LCTR.CoreLawConditionGraph
open LCTR.CoreNativeLawFailure
open LCTR.CoreRefinementForest (Regions asForest covered unrefined)
variable {E T A : Type} {X Y : A → Type}

def arity (i : Fin 5) : ℕ := if i = 1 then 1 else 2
abbrev Case (i : Fin 5) := Fin (arity i)
def occurrence (d : Family T A X Y) (i : Fin 5) (j : Case i) : Prop :=
  if i = 0 then (if j.val = 0 then emptyTime d else outEval d)
  else if i = 1 then genConflict d
  else if i = 2 then (if j.val = 0 then emptyFiber d else altOutput d)
  else if i = 3 then (if j.val = 0 then loss d else gain d)
  else (if j.val = 0 then emptyCommon d else inadmissibleCommon d)
def pureCase (d : Family T A X Y) (i : Fin 5) (j : Case i) : Prop :=
  occurrence d i j ∧ ∀ k : Case i, k ≠ j → ¬ occurrence d i k
def remainderCase (d : Family T A X Y) (i : Fin 5) : Prop :=
  ![emptyTime d ∧ outEval d, offGenConflict d, emptyFiber d ∧ altOutput d,
    loss d ∧ gain d,False] i

theorem pure_cases_exclusive (d : Family T A X Y) (i : Fin 5) (j k : Case i)
    (ne : j ≠ k) : ¬ (pureCase d i j ∧ pureCase d i k) :=
  fun h => h.1.2 k (Ne.symm ne) h.2.1

theorem pure_cover_formula (d : Family T A X Y) (i : Fin 5) :
    (∃ j : Case i, pureCase d i j) ↔
      ![purePair (emptyTime d) (outEval d),genConflict d,
        purePair (emptyFiber d) (altOutput d),purePair (loss d) (gain d),
        purePair (emptyCommon d) (inadmissibleCommon d)] i := by
  fin_cases i <;>
    simp [pureCase,occurrence,Case,arity,Fin.exists_fin_succ,Fin.forall_fin_succ,purePair]

def rawParent (d : Family T A X Y) (i : Fin 5) : Prop :=
  (∀ j, Ancestor j i → condition d j) ∧ ¬ condition d i

theorem native_remainder_formula (d : Family T A X Y) (i : Fin 5) (hp : rawParent d i) :
    (¬ ∃ j : Case i, pureCase d i j) ↔ remainderCase d i := by
  rw [pure_cover_formula]
  fin_cases i
  · exact pair_remainder _ _ ((condition1_countercases d).mp (by simpa [condition] using hp.2))
  · exact condition2_remainder d (by simpa [condition] using hp.2)
  · have h1 : K1 d := by simpa [condition] using hp.1 0 (by decide)
    exact pair_remainder _ _ ((condition3_countercases d h1).mp (by simpa [condition] using hp.2))
  · exact condition4_remainder d (by simpa [condition] using hp.2)
  · have h3 : K3 d := by simpa [condition] using hp.1 2 (by decide)
    have pure := (condition135_remainders d).2.2 h3 (by simpa [condition] using hp.2)
    change ¬ purePair (emptyCommon d) (inadmissibleCommon d) ↔ False
    simp [pure]

variable (s : Selection (E := E) (T := T) (A := A) (X := X) (Y := Y)) (S : Set E)
def parent (i : Fin 5) : Set E := {e | e ∈ S ∧ minimalClass s e i}
def selectedPure (e : E) (i : Fin 5) (j : Case i) : Prop :=
  ∃ h : s.domain e, pureCase (s.datum ⟨e,h⟩) i j
def child (i : Fin 5) (j : Case i) : Set E :=
  {e | e ∈ parent s S i ∧ selectedPure s e i j}
def regions : Regions E (Fin 5) Case (fun _ _ => Empty) where
  root := parent s S
  first := child s S
  second _ _ k := nomatch k
  first_subset _ _ _ h := h.1
  second_subset _ _ k := nomatch k

theorem parent_subset_evaluation (i : Fin 5) : parent s S i ⊆ S := fun _ h => h.1
theorem child_subset_parent (i : Fin 5) (j : Case i) : child s S i j ⊆ parent s S i := fun _ h => h.1
theorem children_pairwise_disjoint (i : Fin 5) (j k : Case i) (ne : j ≠ k) :
    Disjoint (child s S i j) (child s S i k) := by
  apply Set.disjoint_left.mpr
  rintro e ⟨_,h,pj⟩ ⟨_,_,pk⟩
  exact pure_cases_exclusive (s.datum ⟨e,h⟩) i j k ne ⟨pj,pk⟩

theorem parent_to_native (i : Fin 5) (e : E) (h : s.domain e)
    (hp : e ∈ parent s S i) : rawParent (s.datum ⟨e,h⟩) i := by
  exact ⟨fun j hj => (selected_condition_exact s e h j).mp (hp.2.2.1 j hj),
    fun hc => hp.2.2.2 ((selected_condition_exact s e h i).mpr hc)⟩

theorem covered_membership (i : Fin 5) (e : E) (h : s.domain e) :
    e ∈ covered (asForest (regions s S)) (.root i) ↔
      e ∈ parent s S i ∧ ∃ j : Case i, pureCase (s.datum ⟨e,h⟩) i j := by
  change (e ∈ ⋃ j, child s S i j) ↔ _
  simp only [mem_iUnion,child,mem_ofPred_eq,selectedPure]
  constructor
  · rintro ⟨j,hp,_,hj⟩
    exact ⟨hp,j,hj⟩
  · rintro ⟨hp,j,hj⟩
    exact ⟨j,hp,h,hj⟩

theorem unrefined_exact (i : Fin 5) (e : E) (h : s.domain e) (hp : e ∈ parent s S i) :
    e ∈ unrefined (asForest (regions s S)) (.root i) ↔ remainderCase (s.datum ⟨e,h⟩) i := by
  change (e ∈ parent s S i ∧ e ∉ covered (asForest (regions s S)) (.root i)) ↔ _
  rw [covered_membership s S i e h]
  simp only [hp,true_and]
  exact native_remainder_formula _ i (parent_to_native s S i e h hp)

theorem root_decomposition (i : Fin 5) :
    let F := asForest (regions s S)
    parent s S i = covered F (.root i) ∪ unrefined F (.root i) ∧
      Disjoint (covered F (.root i)) (unrefined F (.root i)) :=
  LCTR.CoreRefinementForest.node_decomposition (asForest (regions s S)) (.root i)

theorem root_unrefined_subset (i : Fin 5) :
    unrefined (asForest (regions s S)) (.root i) ⊆ parent s S i := fun _ h => h.1

theorem node5_unrefined_empty : unrefined (asForest (regions s S)) (.root 4) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro e he
  have hp : e ∈ parent s S 4 := he.1
  have hd : s.domain e := hp.2.1
  exact (unrefined_exact s S 4 e hd hp).mp he

theorem node5_covered_all : covered (asForest (regions s S)) (.root 4) = parent s S 4 := by
  have split := (root_decomposition s S 4).1
  rw [node5_unrefined_empty,Set.union_empty] at split
  exact split.symm

theorem first_level_terminal (i : Fin 5) (j : Case i) :
    covered (asForest (regions s S)) (.first i j) = ∅ ∧
      unrefined (asForest (regions s S)) (.first i j) = child s S i j := by
  have hc : covered (asForest (regions s S)) (.first i j) = ∅ := by
    ext e
    simp [covered,asForest,LCTR.CoreRefinementForest.children]
  exact ⟨hc,by rw [unrefined,hc,Set.sdiff_empty]; rfl⟩

theorem root_snapshot_monotonicity (i : Fin 5) {J0 J1 : Type}
    (r0 : J0 → Set E) (r1 : J1 → Set E) (embed : J0 → J1)
    (same : ∀ j, r0 j = r1 (embed j)) :
    (⋃ j, r0 j) ⊆ (⋃ j, r1 j) ∧
      parent s S i \ (⋃ j, r1 j) ⊆ parent s S i \ (⋃ j, r0 j) :=
  LCTR.CoreRefinementForest.snapshot_monotonicity _ r0 r1 embed same

end LCTR.CoreLawRefinement
