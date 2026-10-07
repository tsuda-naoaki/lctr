import CoreDifferentialFailure
import CoreFiniteAudit

namespace LCTR.CoreDifferentialTokens
set_option autoImplicit false
open Set LCTR.CoreDifferentialFailure LCTR.SelectedInputEvaluation LCTR.CoreEvaluation
open LCTR.CoreTokenGraph (Token series)
open LCTR.CoreFiniteAudit
abbrev FullEdge := LCTR.CoreTokenGraph.Edge
def token (i : Node) : Token := ⟨5,i⟩
def DifferentialSet : Set Token := {t | series t = 5}
def FailedStrict (st : Token → State) : Set Token := {t | series t ≠ 3 ∧ st t = .failed}
def Ready (f e : Token → Bool) (st : Token → State) (i : Node) : Prop :=
  f (token i) = true ∧ e (token i) = true ∧ ∀ y, FullEdge y (token i) → st y = .sat

theorem token_bijection : Function.Bijective (fun i : Node => (⟨token i,rfl⟩ : DifferentialSet)) := by
  constructor
  · intro i j h
    have eq : token i = token j := congrArg Subtype.val h
    exact Sigma.mk.inj_iff.mp eq |>.2 |> eq_of_heq
  · rintro ⟨⟨t,i⟩,h⟩
    have ht : t = (5 : Fin 6) := Fin.ext h
    subst t
    exact ⟨i,rfl⟩

theorem within_edges_exact : ∀ i j : Node, FullEdge (token i) (token j) ↔ Edge i j := by decide
theorem incoming_edges_exact : ∀ i : Node, ∀ y : Token,
    FullEdge y (token i) ↔ series y = 4 ∨ ∃ j : Node, y = token j ∧ Edge j i := by decide

theorem recursive_failure (f e c : Token → Bool) (st : Token → State)
    (rec : Recurs FullEdge f e c st) (i : Node) :
    st (token i) = .failed ↔ Ready f e st i ∧ c (token i) = false := by
  rw [rec (token i),update_failed_iff]
  rw [← predecessor_iff]
  unfold Ready
  tauto

theorem ready_failure (f e c : Token → Bool) (st : Token → State)
    (rec : Recurs FullEdge f e c st) (i : Node) (ready : Ready f e st i) :
    st (token i) = .failed ↔ c (token i) = false := by
  rw [recursive_failure f e c st rec i]
  exact and_iff_right ready

variable {E Law Ω : Type} {law : Selected E Law}
variable (s : MatchingDifferential E Law (LCTR.DifferentialNativeDomains.Input Ω) law)
variable (operative : Law → Prop)

theorem minimal_token_correspondence (ev : E) (f e c : Token → Bool) (st : Token → State)
    (rec : Recurs FullEdge f e c st) (i : Node)
    (assignment : c (token i) = true ↔ selectedCondition s ev i)
    (ancestors : ancestorReady s operative ev i) (ready : Ready f e st i) :
    minimalFailure s operative ev i ↔ token i ∈ FailedStrict st := by
  change (ancestorReady s operative ev i ∧ ¬ selectedCondition s ev i) ↔
    series (token i) ≠ 3 ∧ st (token i) = .failed
  rw [and_iff_right ancestors,and_iff_right (show series (token i) ≠ 3 by simp [series,token]),
    ready_failure f e c st rec i ready,← Bool.not_eq_true,assignment]

theorem signature_token_correspondence (ev : E) (f e c : Token → Bool) (st : Token → State)
    (rec : Recurs FullEdge f e c st)
    (assignment : ∀ i, c (token i) = true ↔ selectedCondition s ev i)
    (ancestors : ∀ i, ancestorReady s operative ev i) (ready : ∀ i, Ready f e st i) :
    ∀ i, signature s operative ev i = true ↔ token i ∈ FailedStrict st := by
  classical
  intro i
  rw [signature,decide_eq_true_eq]
  exact minimal_token_correspondence s operative ev f e c st rec i (assignment i) (ancestors i) (ready i)

theorem failure_set_token_image (ev : E) (f e c : Token → Bool) (st : Token → State)
    (rec : Recurs FullEdge f e c st)
    (assignment : ∀ i, c (token i) = true ↔ selectedCondition s ev i)
    (ancestors : ∀ i, ancestorReady s operative ev i) (ready : ∀ i, Ready f e st i) :
    token '' {i | minimalFailure s operative ev i} = FailedStrict st ∩ DifferentialSet := by
  ext t
  constructor
  · rintro ⟨i,hi,rfl⟩
    exact ⟨(minimal_token_correspondence s operative ev f e c st rec i
      (assignment i) (ancestors i) (ready i)).mp hi,rfl⟩
  · rintro ⟨hf,hd⟩
    obtain ⟨i,hi⟩ := token_bijection.2 ⟨t,hd⟩
    have eq : token i = t := congrArg Subtype.val hi
    refine ⟨i,?_,eq⟩
    exact (minimal_token_correspondence s operative ev f e c st rec i
      (assignment i) (ancestors i) (ready i)).mpr (eq.symm ▸ hf)

theorem law_failure_blocks_differential (f e c : Token → Bool) (st : Token → State)
    (rec : Recurs FullEdge f e c st) (t : Token) (lawSeries : series t = 4)
    (failed : st t = .failed) : ∀ i, st (token i) = .unformed := by
  intro i
  apply direct_nonsat_unformed FullEdge f e c st rec
    ((incoming_edges_exact i t).mpr (Or.inl lawSeries))
  rw [failed]
  decide

theorem atlas_failure_blocks_descendants (f e c : Token → Bool) (st : Token → State)
    (rec : Recurs FullEdge f e c st) (failed : st (token 0) = .failed) :
    ∀ i : Node, i ≠ 0 → st (token i) = .unformed := by
  have no : st (token 0) ≠ .sat := by rw [failed]; decide
  have one : st (token 1) = .unformed :=
    direct_nonsat_unformed FullEdge f e c st rec (by decide) no
  intro i hi
  fin_cases i
  · exact False.elim (hi rfl)
  · exact one
  · apply direct_nonsat_unformed FullEdge f e c st rec (show FullEdge (token 1) (token 2) by decide)
    rw [one]
    decide
  · exact direct_nonsat_unformed FullEdge f e c st rec (by decide) no
  · exact direct_nonsat_unformed FullEdge f e c st rec (by decide) no

theorem relative_nonemptiness :
    Nonempty ((i : Node) → {ev : E // minimalFailure s operative ev i}) ↔
      ∀ i : Node, ∃ ev : E, minimalFailure s operative ev i := by
  classical
  constructor
  · rintro ⟨w⟩ i
    exact ⟨(w i).val,(w i).property⟩
  · intro h
    exact ⟨fun i => ⟨Classical.choose (h i),Classical.choose_spec (h i)⟩⟩

theorem relative_nonempty_witness_family :
    (∀ i : Node, ∃ ev : E, minimalFailure s operative ev i) ↔
      ∃ w : Node → E, ∀ i, minimalFailure s operative (w i) i := by
  classical
  exact ⟨fun h => ⟨fun i => Classical.choose (h i),fun i => Classical.choose_spec (h i)⟩,
    fun ⟨w,h⟩ i => ⟨w i,h i⟩⟩

theorem finite_witness_set (w : Node → E) (hw : ∀ i, minimalFailure s operative (w i) i) :
    ∃ A : Finset E, A.card ≤ 5 ∧ ∀ i, ∃ ev ∈ A, minimalFailure s operative ev i := by
  classical
  refine ⟨Finset.univ.image w,?_,?_⟩
  · exact le_trans (Finset.card_image_le) (by simp)
  · intro i
    exact ⟨w i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,hw i⟩

end LCTR.CoreDifferentialTokens
