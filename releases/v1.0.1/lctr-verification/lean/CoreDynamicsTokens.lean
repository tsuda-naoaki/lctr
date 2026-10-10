import CoreFiniteAudit
import CoreContinuumIntegration

namespace LCTR.CoreDynamicsTokens
set_option autoImplicit false
open LCTR.CoreTokenGraph LCTR.CoreEvaluation LCTR.CoreFiniteAudit
open LCTR.SelectedInputEvaluation
open LCTR.CoreContinuumIntegration (all_sat_iff_tests)

abbrev Node := Fin 8
def token (i : Node) : Token := ⟨2,i⟩
def DynamicsSet : Set Token := {t | series t = 2}
def FailedStrict (s : Token → State) : Set Token := {t | series t ≠ 3 ∧ s t = .failed}
def Ready (f e : Token → Bool) (s : Token → State) (i : Node) : Prop :=
  f (token i) = true ∧ e (token i) = true ∧ ∀ y, Edge y (token i) → s y = .sat
def InputSat (f e : Token → Bool) (s : Token → State) : Prop :=
  (∀ i : Node, f (token i) = true ∧ e (token i) = true) ∧
  ∀ y, series y = 1 → s y = .sat
def MinimalFalse (c : Token → Bool) (i : Node) : Prop :=
  c (token i) = false ∧ ∀ j : Node, c (token j) = false →
    Relation.ReflTransGen Edge (token j) (token i) → j = i

theorem token_bijection : Function.Bijective
    (fun i : Node => (⟨token i,rfl⟩ : DynamicsSet)) := by
  constructor
  · intro i j h
    have eq : token i = token j := congrArg Subtype.val h
    exact Sigma.mk.inj_iff.mp eq |>.2 |> eq_of_heq
  · rintro ⟨⟨s,i⟩,h⟩
    have hs : s = (2 : Fin 6) := Fin.ext h
    subst s
    exact ⟨i,rfl⟩

theorem within_edges_exact : ∀ i j : Node, Edge (token i) (token j) ↔
    (i.val,j.val) ∈ [(0,5),(5,6),(1,2),(2,7),(5,7)] := by decide

theorem incoming_edges_exact : ∀ i : Node, ∀ y : Token, Edge y (token i) ↔
    series y = 1 ∨ ∃ j : Node, y = token j ∧ Edge (token j) (token i) := by decide

theorem recursive_failure (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) (i : Node) :
    s (token i) = .failed ↔ Ready f e s i ∧ c (token i) = false := by
  rw [rec (token i),update_failed_iff,← predecessor_iff]
  unfold Ready
  tauto

theorem condition_correspondence (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) (K : Node → Prop)
    (assignment : ∀ i, c (token i) = true ↔ K i) (i : Node) :
    token i ∈ FailedStrict s ↔ Ready f e s i ∧ ¬ K i := by
  change (series (token i) ≠ 3 ∧ s (token i) = .failed) ↔ _
  rw [and_iff_right (show series (token i) ≠ 3 by simp [series,token]),recursive_failure f e c s rec,
    ← Bool.not_eq_true,assignment i]

theorem sat_implies_condition (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) (t : Token) (h : s t = .sat) : c t = true := by
  classical
  rw [rec t] at h
  exact ((state_sat_iff _ _ _ _).mp h).2.2.2

theorem ready_iff_ancestor_conditions (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) (inp : InputSat f e s) (i : Node) :
    Ready f e s i ↔ ∀ j : Node, Relation.TransGen Edge (token j) (token i) → c (token j) = true := by
  classical
  constructor
  · intro r j path
    have decomposition : ∃ z, Relation.ReflTransGen Edge (token j) z ∧ Edge z (token i) := by
      cases path with
      | single h => exact ⟨token j,Relation.ReflTransGen.refl,h⟩
      | tail p h => exact ⟨_,p.to_reflTransGen,h⟩
    obtain ⟨z,initial,last⟩ := decomposition
    have sz : s z = .sat := r.2.2 z last
    have sj : s (token j) = .sat := by
      rcases Relation.reflTransGen_iff_eq_or_transGen.mp initial with eq | hp
      · simpa only [eq] using sz
      · by_contra hn
        have bad := path_nonsat_unformed Edge f e c s rec hp hn
        rw [sz] at bad
        cases bad
    exact sat_implies_condition f e c s rec _ sj
  · intro hc
    let J : Set Token := {t | series t = 2 ∧ Relation.TransGen Edge t (token i)}
    have allsat : ∀ t ∈ J, s t = .sat := by
      apply (all_sat_iff_tests Edge
        (LCTR.CoreDagRecursion.finite_acyclic_wellFounded Edge acyclic) f e c s rec J ?_ ?_).mpr
      · intro t ht
        obtain ⟨j,hj⟩ := token_bijection.2 ⟨t,ht.1⟩
        have eq : token j = t := congrArg Subtype.val hj
        simpa only [← eq] using hc j (eq.symm ▸ ht.2)
      · intro t ht
        obtain ⟨j,hj⟩ := token_bijection.2 ⟨t,ht.1⟩
        have eq : token j = t := congrArg Subtype.val hj
        exact eq ▸ inp.1 j
      · intro x hx y hy hn
        obtain ⟨k,hk⟩ := token_bijection.2 ⟨x,hx.1⟩
        have eq : token k = x := congrArg Subtype.val hk
        rcases (incoming_edges_exact k y).mp (eq.symm ▸ hy) with hr | ⟨j,rfl,_⟩
        · exact inp.2 y hr
        · exact False.elim (hn ⟨rfl,(Relation.TransGen.single hy).trans hx.2⟩)
    refine ⟨(inp.1 i).1,(inp.1 i).2,?_⟩
    intro y hy
    rcases (incoming_edges_exact i y).mp hy with hr | ⟨j,rfl,hj⟩
    · exact inp.2 y hr
    · exact allsat _ ⟨rfl,Relation.TransGen.single hj⟩

theorem minimal_false_iff (c : Token → Bool) (i : Node) :
    MinimalFalse c i ↔ (∀ j : Node, Relation.TransGen Edge (token j) (token i) →
      c (token j) = true) ∧ c (token i) = false := by
  constructor
  · rintro ⟨hi,hm⟩
    refine ⟨?_,hi⟩
    intro j hj
    by_contra hc
    have ji := hm j (by simpa using hc) hj.to_reflTransGen
    subst j
    exact acyclic _ hj
  · rintro ⟨ha,hi⟩
    refine ⟨hi,?_⟩
    intro j hj path
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp path with eq | hp
    · have val := congrArg (fun t : Token => t.2.val) eq
      exact Fin.ext val.symm
    · have bad := ha j hp
      rw [hj] at bad
      cases bad

theorem failure_iff_minimal (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) (inp : InputSat f e s) (i : Node) :
    s (token i) = .failed ↔ MinimalFalse c i := by
  rw [recursive_failure f e c s rec,ready_iff_ancestor_conditions f e c s rec inp,
    minimal_false_iff]

theorem false_condition_has_failure (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) (inp : InputSat f e s) (i : Node)
    (hi : c (token i) = false) : ∃ j : Node, s (token j) = .failed := by
  classical
  have induction : ∀ n : ℕ, ∀ i : Node, scalarRank (token i) = n →
      c (token i) = false → ∃ j : Node, s (token j) = .failed := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hn hc
      by_cases ha : ∀ j : Node, Relation.TransGen Edge (token j) (token i) → c (token j) = true
      · exact ⟨i,(recursive_failure f e c s rec i).mpr
          ⟨(ready_iff_ancestor_conditions f e c s rec inp i).mpr ha,hc⟩⟩
      · push Not at ha
        obtain ⟨j,hp,hj⟩ := ha
        have lower := path_increases Edge (· < ·) scalarRank (fun _ _ => edge_rank_increasing) hp
        exact ih (scalarRank (token j)) (hn ▸ lower) j rfl (by simpa using hj)
  exact induction _ i rfl hi

theorem stage_failure_iff (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) (inp : InputSat f e s) :
    (∃ i : Node, s (token i) = .failed) ↔ ¬ ∀ i : Node, c (token i) = true := by
  constructor
  · rintro ⟨i,hi⟩ h
    have no := ((recursive_failure f e c s rec i).mp hi).2
    rw [h i] at no
    cases no
  · intro h
    push Not at h
    obtain ⟨i,hi⟩ := h
    exact false_condition_has_failure f e c s rec inp i (by simpa using hi)

theorem failed_intersection_image (s : Token → State) :
    FailedStrict s ∩ DynamicsSet = token '' {i | s (token i) = .failed} := by
  ext t
  constructor
  · rintro ⟨hf,hd⟩
    obtain ⟨i,hi⟩ := token_bijection.2 ⟨t,hd⟩
    have eq : token i = t := congrArg Subtype.val hi
    refine ⟨i,?_,eq⟩
    change s (token i) = .failed
    rw [eq]
    exact hf.2
  · rintro ⟨i,hi,rfl⟩
    exact ⟨⟨by simp [series,token],hi⟩,rfl⟩

theorem stage_intersection_nonempty (s : Token → State) :
    (FailedStrict s ∩ DynamicsSet).Nonempty ↔ ∃ i : Node, s (token i) = .failed := by
  rw [failed_intersection_image,Set.image_nonempty]
  rfl

theorem minimal_set_nonempty (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) (inp : InputSat f e s) :
    (∃ i : Node, MinimalFalse c i) ↔ ¬ ∀ i : Node, c (token i) = true := by
  rw [← stage_failure_iff f e c s rec inp]
  exact exists_congr (fun i => (failure_iff_minimal f e c s rec inp i).symm)

theorem unconditional_antichain (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) (i j : Node)
    (hi : s (token i) = .failed) (hj : s (token j) = .failed)
    (path : Relation.ReflTransGen Edge (token i) (token j)) : i = j := by
  exact Fin.ext (congrArg (fun t : Token => t.2.val) (failed_minimal Edge f e c s rec hi hj path))

theorem simultaneous_minima (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) (inp : InputSat f e s) (i j : Node)
    (hi : MinimalFalse c i) (hj : MinimalFalse c j) :
    s (token i) = .failed ∧ s (token j) = .failed :=
  ⟨(failure_iff_minimal f e c s rec inp i).mpr hi,
    (failure_iff_minimal f e c s rec inp j).mpr hj⟩

theorem upstream_failure_blocks_all (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) (r : Token) (hr : series r = 1)
    (hf : s r = .failed) : ∀ i : Node, s (token i) = .unformed := by
  intro i
  apply direct_nonsat_unformed Edge f e c s rec ((incoming_edges_exact i r).mpr (Or.inl hr))
  rw [hf]
  decide

end LCTR.CoreDynamicsTokens
