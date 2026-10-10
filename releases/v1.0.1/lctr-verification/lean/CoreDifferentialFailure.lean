import LCTR.DifferentialConditionDAG
import LCTR.DifferentialNativeDomains
import CoreTokenGraph
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

namespace LCTR.CoreDifferentialFailure
set_option autoImplicit false
open LCTR.SelectedInputEvaluation LCTR.CoreEvaluation
abbrev Node := Fin 5
abbrev Edge := LCTR.DifferentialConditionDAG.Edge
def Ancestor (i j : Node) : Prop :=
  (i = 0 ∧ (j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4)) ∨ (i = 1 ∧ j = 2)
instance (i j : Node) : Decidable (Edge i j) := by unfold Edge LCTR.DifferentialConditionDAG.Edge; infer_instance
instance (i j : Node) : Decidable (Ancestor i j) := by unfold Ancestor; infer_instance

theorem edge_ancestor : ∀ i j : Node, Edge i j → Ancestor i j := by decide
theorem ancestor_transitive : ∀ i j k : Node, Ancestor i j → Ancestor j k → Ancestor i k := by decide
theorem ancestor_irreflexive : ∀ i : Node, ¬ Ancestor i i := by decide
theorem ancestors_exact (i j : Node) : Relation.TransGen Edge i j ↔ Ancestor i j := by
  constructor
  · intro path
    induction path with
    | single h => exact edge_ancestor _ _ h
    | tail _ h ih => exact ancestor_transitive _ _ _ ih (edge_ancestor _ _ h)
  · intro h
    have cases : Edge i j ∨ (i = 0 ∧ j = 2) := by
      have finite : ∀ a b : Node, Ancestor a b → Edge a b ∨ (a = 0 ∧ b = 2) := by decide
      exact finite i j h
    rcases cases with edge | ⟨rfl,rfl⟩
    · exact Relation.TransGen.single edge
    · exact Relation.TransGen.tail (Relation.TransGen.single (show Edge 0 1 by decide))
        (show Edge 1 2 by decide)

theorem ancestor_conjunctions (c : Node → Prop) :
    (∀ j, Ancestor j 0 → c j) ↔ True := by simp [Ancestor]

theorem ancestor_conjunctions_all (c : Node → Prop) (i : Node) :
    (∀ j, Ancestor j i → c j) ↔
      ![True,c 0,c 0 ∧ c 1,c 0,c 0] i := by
  fin_cases i <;> simp [Ancestor]

open LCTR.DifferentialNativeDomains
variable {E Law Ω : Type}
def condition (d : Input Ω) (i : Node) : Prop := ![c1 d,c2 d,c3 d,c4 d,c5 d] i
def counter (d : Input Ω) (i : Node) : Prop :=
  ![∃ r, ¬ d.atlas r,
    ∃ r, ¬ d.jet r,
    ∃ r, ∀ h : d.jet r, ¬ d.member r h,
    ∃ r, ∀ h : d.atlas r, ¬ d.value r h,
    ∃ r s, ∀ h : d.atlas r, ∀ k : d.atlas s, ¬ d.time r s h k] i

theorem condition_failure_witness (d : Input Ω) (i : Node) :
    ¬ condition d i ↔ counter d i := by
  classical
  fin_cases i <;> simp [condition,counter,c1,c2,c3,c4,c5]

theorem all_conditions_complete (d : Input Ω) : (∀ i, condition d i) ↔ complete d := by
  constructor
  · intro h
    exact ⟨h 0,h 1,h 2,h 3,h 4⟩
  · rintro ⟨h0,h1,h2,h3,h4⟩ i
    fin_cases i <;> assumption

variable {law : Selected E Law} (s : MatchingDifferential E Law (Input Ω) law)
variable (operative : Law → Prop)
def selectedCondition (e : E) (i : Node) : Prop :=
  ∃ h : s.domain e, condition (s.structureAt ⟨e,h⟩) i
def lawReady (e : E) : Prop :=
  ∃ h : s.domain e, operative (differentialInput s e h).1
def ancestorReady (e : E) (i : Node) : Prop :=
  lawReady s operative e ∧ ∀ j, Ancestor j i → selectedCondition s e j
def minimalFailure (e : E) (i : Node) : Prop :=
  ancestorReady s operative e i ∧ ¬ selectedCondition s e i
def failure (e : E) : Prop :=
  lawReady s operative e ∧ ¬ ∀ i, selectedCondition s e i

theorem selected_restricts (e : E) (h : s.domain e) (i : Node) :
    selectedCondition s e i ↔ condition (s.structureAt ⟨e,h⟩) i := by
  exact ⟨fun ⟨_,hc⟩ => hc,fun hc => ⟨h,hc⟩⟩

theorem ancestor_restricts (e : E) (h : s.domain e) (i : Node) :
    ancestorReady s operative e i ↔
      operative (law.datum ⟨e,s.subdomain e h⟩) ∧
      ∀ j, Ancestor j i → condition (s.structureAt ⟨e,h⟩) j := by
  constructor
  · rintro ⟨⟨_,hl⟩,ha⟩
    exact ⟨hl,fun j hj => (selected_restricts s e h j).mp (ha j hj)⟩
  · rintro ⟨hl,ha⟩
    exact ⟨⟨h,hl⟩,fun j hj => (selected_restricts s e h j).mpr (ha j hj)⟩

theorem outside_selection_no_failure (e : E) (outside : ¬ s.domain e) :
    ¬ failure s operative e ∧ ∀ i, ¬ minimalFailure s operative e i := by
  exact ⟨fun h => outside h.1.choose,fun _ h => outside h.1.1.choose⟩

theorem failure_vs_operative (e : E) (h : s.domain e) :
    failure s operative e ↔ operative (law.datum ⟨e,s.subdomain e h⟩) ∧
      ¬ (operative (law.datum ⟨e,s.subdomain e h⟩) ∧ complete (s.structureAt ⟨e,h⟩)) := by
  have hr : lawReady s operative e ↔ operative (law.datum ⟨e,s.subdomain e h⟩) :=
    ⟨fun ⟨_,hl⟩ => hl,fun hl => ⟨h,hl⟩⟩
  have hc : (∀ i, selectedCondition s e i) ↔ complete (s.structureAt ⟨e,h⟩) :=
    (forall_congr' (selected_restricts s e h)).trans (all_conditions_complete _)
  unfold failure
  rw [hr,hc]
  tauto

theorem minimal_failure_witness (e : E) (h : s.domain e) (i : Node) :
    minimalFailure s operative e i ↔ ancestorReady s operative e i ∧
      counter (s.structureAt ⟨e,h⟩) i := by
  unfold minimalFailure
  rw [selected_restricts s e h i,condition_failure_witness]

theorem failure_cover (e : E) : failure s operative e ↔ ∃ i, minimalFailure s operative e i := by
  classical
  constructor
  · rintro ⟨hl,notAll⟩
    have make (i : Node) (a : ![True,selectedCondition s e 0,
        selectedCondition s e 0 ∧ selectedCondition s e 1,
        selectedCondition s e 0,selectedCondition s e 0] i)
        (no : ¬ selectedCondition s e i) : ∃ j, minimalFailure s operative e j :=
      ⟨i,⟨hl,(ancestor_conjunctions_all _ i).mpr a⟩,no⟩
    by_cases h0 : selectedCondition s e 0
    · by_cases h1 : selectedCondition s e 1
      · by_cases h2 : selectedCondition s e 2
        · by_cases h3 : selectedCondition s e 3
          · by_cases h4 : selectedCondition s e 4
            · apply False.elim
              apply notAll
              intro i
              fin_cases i <;> assumption
            · exact make 4 h0 h4
          · exact make 3 h0 h3
        · exact make 2 ⟨h0,h1⟩ h2
      · exact make 1 h0 h1
    · exact make 0 True.intro h0
  · rintro ⟨i,⟨hl,_⟩,no⟩
    exact ⟨hl,fun h => no (h i)⟩

theorem failure_region_union :
    {e | failure s operative e} = ⋃ i, {e | minimalFailure s operative e i} := by
  ext e
  simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
  exact failure_cover s operative e

theorem minimal_antichain (e : E) (i j : Node)
    (hi : minimalFailure s operative e i) (hj : minimalFailure s operative e j) :
    ¬ Relation.TransGen Edge i j ∧ ¬ Relation.TransGen Edge j i :=
  ⟨fun path => hi.2 (hj.1.2 i ((ancestors_exact i j).mp path)),
    fun path => hj.2 (hi.1.2 j ((ancestors_exact j i).mp path))⟩

noncomputable def signature (e : E) (i : Node) : Bool := by
  classical
  exact decide (minimalFailure s operative e i)

theorem signature_support (e : E) :
    {i | signature s operative e i = true} = {i | minimalFailure s operative e i} := by
  ext i
  simp [signature]

theorem signature_nonzero (e : E) :
    signature s operative e ≠ (fun _ => false) ↔ failure s operative e := by
  classical
  rw [failure_cover]
  constructor
  · intro h
    by_contra none
    have none' : ∀ i, ¬ minimalFailure s operative e i := fun i h => none ⟨i,h⟩
    apply h
    funext i
    simp [signature,none' i]
  · rintro ⟨i,hi⟩ eq
    have h := congrFun eq i
    simp [signature,hi] at h

theorem finite_nonempty_failure_set (e : E) (hf : failure s operative e) :
    ({i | minimalFailure s operative e i} : Set Node).Finite ∧
      ({i | minimalFailure s operative e i} : Set Node).Nonempty :=
  ⟨Set.toFinite _,(failure_cover s operative e).mp hf⟩

 
theorem jet_does_not_require_atlas :
    condition independentJet 1 ∧ ¬ condition independentJet 0 :=
  second_need_not_require_first

end LCTR.CoreDifferentialFailure
