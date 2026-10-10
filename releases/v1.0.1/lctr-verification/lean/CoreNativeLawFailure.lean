import CoreLawConditionGraph
import CoreNativeLawGeneration
import LCTR.SelectedInputEvaluation
import Mathlib.Data.Set.Card

namespace LCTR.CoreNativeLawFailure
set_option autoImplicit false
open LCTR.CoreLawConditionGraph LCTR.LawFamilyTransport LCTR.SelectedInputEvaluation
variable {E T A : Type} {X Y : A → Type}

abbrev Selection := Selected E (Family T A X Y)
def totalCondition (s : Selection (E := E) (T := T) (A := A) (X := X) (Y := Y))
    (e : E) (i : Node) : Prop := evaluate s (fun d => condition d i) e
def failure (s : Selection (E := E) (T := T) (A := A) (X := X) (Y := Y)) (e : E) : Prop :=
  s.domain e ∧ ¬ ∀ i, totalCondition s e i
def ancestorAll (s : Selection (E := E) (T := T) (A := A) (X := X) (Y := Y))
    (e : E) (i : Node) : Prop := ∀ j, Ancestor j i → totalCondition s e j
def minimalClass (s : Selection (E := E) (T := T) (A := A) (X := X) (Y := Y))
    (e : E) (i : Node) : Prop := s.domain e ∧ ancestorAll s e i ∧ ¬ totalCondition s e i

theorem selected_condition_exact (s : Selection (E := E) (T := T) (A := A) (X := X) (Y := Y))
    (e : E) (h : s.domain e) (i : Node) :
    totalCondition s e i ↔ condition (s.datum ⟨e,h⟩) i :=
  selection_defines_unique_value s (fun d => condition d i) e h

theorem outside_selection_not_failure (s : Selection (E := E) (T := T) (A := A) (X := X) (Y := Y))
    (e : E) (h : ¬ s.domain e) :
    (∀ i, ¬ totalCondition s e i) ∧ ¬ failure s e ∧ ∀ i, ¬ minimalClass s e i := by
  refine ⟨?_, fun hf => h hf.1, ?_⟩
  · intro i hi
    exact h hi.1
  · exact fun _ hm => h hm.1

theorem failure_on_selected_datum (s : Selection (E := E) (T := T) (A := A) (X := X) (Y := Y))
    (e : E) (h : s.domain e) : failure s e ↔ ¬ AllConditions (s.datum ⟨e,h⟩) := by
  have all : (∀ i, totalCondition s e i) ↔ AllConditions (s.datum ⟨e,h⟩) :=
    (forall_congr' (selected_condition_exact s e h)).trans (all_conditions_exact _)
  simp only [failure, h, true_and, all]

theorem ancestors_explicit (s : Selection (E := E) (T := T) (A := A) (X := X) (Y := Y))
    (e : E) (i : Node) :
    ancestorAll s e i ↔
      if i = 2 then totalCondition s e 0
      else if i = 4 then totalCondition s e 0 ∧ totalCondition s e 2 else True := by
  fin_cases i <;> simp [ancestorAll,Ancestor,Edge,and_comm]

theorem failure_covered_by_minimal_classes
    (s : Selection (E := E) (T := T) (A := A) (X := X) (Y := Y)) (e : E) :
    failure s e ↔ ∃ i, minimalClass s e i := by
  classical
  let k := totalCondition s e
  have all : (∀ i : Node, k i) ↔ k 0 ∧ k 1 ∧ k 2 ∧ k 3 ∧ k 4 := by
    constructor
    · intro h; exact ⟨h 0,h 1,h 2,h 3,h 4⟩
    · rintro ⟨h0,h1,h2,h3,h4⟩ i
      fin_cases i <;> assumption
  have covered := law_cover (s.domain e) ⟨k 0,k 1,k 2,k 3,k 4⟩
  constructor
  · rintro ⟨hd,hnot⟩
    have raw : lawFailure (s.domain e) ⟨k 0,k 1,k 2,k 3,k 4⟩ :=
      ⟨hd,fun hk => hnot (all.mpr hk)⟩
    have hclasses := covered.mp raw
    rcases hclasses with h0 | h1 | h2 | h3 | h4
    · exact ⟨0,h0.1,(ancestors_explicit s e 0).mpr (by trivial),h0.2⟩
    · exact ⟨1,h1.1,(ancestors_explicit s e 1).mpr (by trivial),h1.2⟩
    · exact ⟨2,h2.1,(ancestors_explicit s e 2).mpr h2.2.1,h2.2.2⟩
    · exact ⟨3,h3.1,(ancestors_explicit s e 3).mpr (by trivial),h3.2⟩
    · exact ⟨4,h4.1,(ancestors_explicit s e 4).mpr ⟨h4.2.1,h4.2.2.1⟩,h4.2.2.2⟩
  · rintro ⟨i,hd,_,hn⟩
    exact ⟨hd,fun hk => hn (hk i)⟩

theorem minimal_classes_antichain
    (s : Selection (E := E) (T := T) (A := A) (X := X) (Y := Y))
    (e : E) (i j : Node) (hi : minimalClass s e i) (hj : minimalClass s e j) :
    ¬ Relation.TransGen Edge i j ∧ ¬ Relation.TransGen Edge j i := by
  exact ⟨fun h => hi.2.2 (hj.2.1 i ((ancestors_exact i j).mp h)),
    fun h => hj.2.2 (hi.2.1 j ((ancestors_exact j i).mp h))⟩

theorem failure_domain_union
    (s : Selection (E := E) (T := T) (A := A) (X := X) (Y := Y)) :
    {e | failure s e} = ⋃ i : Node, {e | minimalClass s e i} := by
  ext e
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  exact failure_covered_by_minimal_classes s e

theorem finite_witness_set
    (s : Selection (E := E) (T := T) (A := A) (X := X) (Y := Y)) :
    ∃ W : Set E, W.Finite ∧ W.ncard ≤ 5 ∧
      ∀ i : Node, (∃ e, minimalClass s e i) ↔ ∃ e ∈ W, minimalClass s e i := by
  classical
  by_cases inhabited : Nonempty E
  · let active : Set Node := {i | ∃ e, minimalClass s e i}
    let pick : Node → E := fun i => if h : ∃ e, minimalClass s e i
      then Classical.choose h else Classical.choice inhabited
    let W := pick '' active
    have hf : active.Finite := Set.toFinite _
    refine ⟨W,hf.image pick,?_,?_⟩
    · calc
        W.ncard ≤ active.ncard := Set.ncard_image_le hf
        _ ≤ Nat.card Node := Set.ncard_le_card active
        _ = 5 := by simp [Node, Nat.card_eq_fintype_card]
    · intro i
      constructor
      · intro hi
        refine ⟨pick i,⟨i,hi,rfl⟩,?_⟩
        simpa only [pick, dif_pos hi] using Classical.choose_spec hi
      · rintro ⟨e,_,he⟩; exact ⟨e,he⟩
  · refine ⟨∅,Set.finite_empty,by simp,?_⟩
    intro i
    constructor
    · rintro ⟨e,_⟩; exact False.elim (inhabited ⟨e⟩)
    · rintro ⟨e,he,_⟩; exact False.elim he

noncomputable def nativeSelection {C D B I : Type} {Val : I → Type}
    (c : LCTR.CoreNativeLawComponents.Context C D B I Val)
    (a : LCTR.CoreNativeLawGeneration.LawInput c A) (domain : E → Prop) :=
  { domain := domain, datum := fun _ => LCTR.CoreNativeLawGeneration.family c a :
    Selected E (Family (LCTR.CoreNativeLawComponents.NativeTime c) A
      (fun j => LCTR.CoreNativeLawComponents.Values (Val := Val) (a.component j).inIndices)
      (fun j => LCTR.CoreNativeLawComponents.Values (Val := Val) (a.component j).outIndices)) }

theorem native_failure_exact {C D B I : Type} {Val : I → Type}
    (c : LCTR.CoreNativeLawComponents.Context C D B I Val)
    (a : LCTR.CoreNativeLawGeneration.LawInput c A) (domain : E → Prop) (e : E) (h : domain e) :
    failure (nativeSelection c a domain) e ↔
      ¬ AllConditions (LCTR.CoreNativeLawGeneration.family c a) :=
  failure_on_selected_datum _ e h

end LCTR.CoreNativeLawFailure
