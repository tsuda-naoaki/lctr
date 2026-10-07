import CoreFiniteAudit
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace LCTR.CoreComparisonFailure
set_option autoImplicit false
open Set LCTR.CoreTokenGraph LCTR.CoreEvaluation LCTR.CoreFiniteAudit LCTR.SelectedInputEvaluation

def cmpToken (i : Fin 8) : Token := ⟨0,i⟩

theorem comparison_incoming_exact : ∀ i : Fin 8, ∀ t : Token,
    Edge t (cmpToken i) ↔ ∃ j : Fin 8, t = cmpToken j ∧ j.val + 1 = i.val := by decide

def Prefix (c : Token → Bool) (i : Fin 8) : Prop := ∀ j : Fin 8, j < i → c (cmpToken j) = true
def First (c : Token → Bool) (i : Fin 8) : Prop := Prefix c i ∧ c (cmpToken i) = false

theorem incoming_from_prior_sat (c : Token → Bool) (s : Token → State) (i : Fin 8)
    (prior : ∀ j : Fin 8, j < i →
      (s (cmpToken j) = .sat ↔ ∀ k : Fin 8, k ≤ j → c (cmpToken k) = true)) :
    (∀ y : {y : Token // Edge y (cmpToken i)}, s y.val = .sat) ↔ Prefix c i := by
  constructor
  · intro hs j hji
    let p : Fin 8 := ⟨i.val-1,by omega⟩
    have pi : p < i := by change i.val-1 < i.val; omega
    have ep : Edge (cmpToken p) (cmpToken i) :=
      (comparison_incoming_exact i _).mpr ⟨p,rfl,by dsimp [p]; omega⟩
    exact ((prior p pi).mp (hs ⟨cmpToken p,ep⟩)) j (by change j.val ≤ i.val-1; omega)
  · rintro hp ⟨t,ht⟩
    obtain ⟨j,rfl,hj⟩ := (comparison_incoming_exact i t).mp ht
    apply (prior j (by omega)).mpr
    intro k hk
    exact hp k (by omega)

theorem comparison_sat_prefix (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s)
    (ready : ∀ i : Fin 8, f (cmpToken i) = true ∧ e (cmpToken i) = true) (i : Fin 8) :
    s (cmpToken i) = .sat ↔ ∀ j : Fin 8, j ≤ i → c (cmpToken j) = true := by
  classical
  induction i using Fin.strong_induction_on with
  | h i ih =>
    have prior := incoming_from_prior_sat c s i ih
    rw [rec (cmpToken i)]
    simp only [update,state_sat_iff,(ready i).1,(ready i).2,true_and,decide_eq_true_eq,prior]
    constructor
    · rintro ⟨hp,hc⟩ j hj
      rcases lt_or_eq_of_le hj with lt | rfl
      · exact hp j lt
      · exact hc
    · intro h
      exact ⟨fun j hj => h j hj.le,h i le_rfl⟩

theorem comparison_failed_prefix (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s)
    (ready : ∀ i : Fin 8, f (cmpToken i) = true ∧ e (cmpToken i) = true) (i : Fin 8) :
    s (cmpToken i) = .failed ↔ First c i := by
  have prior := incoming_from_prior_sat c s i
    (fun j _ => comparison_sat_prefix f e c s rec ready j)
  rw [rec (cmpToken i),update_failed_iff]
  simp only [(ready i).1,(ready i).2,true_and,prior,First]

theorem first_index_unique (c : Token → Bool) {i j : Fin 8} (hi : First c i) (hj : First c j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have bad := (hj.1 i h).symm.trans hi.2; cases bad
  · exact h
  · have bad := (hi.1 j h).symm.trans hj.2; cases bad

theorem first_failure_partition (c : Token → Bool) :
    (¬ ∀ i : Fin 8, c (cmpToken i) = true) ↔ ∃! i : Fin 8, First c i := by
  classical
  constructor
  · intro h
    let bad : Finset (Fin 8) := Finset.univ.filter (fun i => c (cmpToken i) = false)
    have nonempty : bad.Nonempty := by
      obtain ⟨i,hi⟩ := not_forall.mp h
      exact ⟨i,by simp [bad,Bool.eq_false_iff.mpr hi]⟩
    let i := bad.min' nonempty
    have hi : c (cmpToken i) = false := (Finset.mem_filter.mp (Finset.min'_mem bad nonempty)).2
    have first : First c i := by
      refine ⟨?_,hi⟩
      intro j hj
      by_contra hc
      have mem : j ∈ bad := by simp [bad,Bool.eq_false_iff.mpr hc]
      have le : i ≤ j := Finset.min'_le bad j mem
      exact (not_le_of_gt hj) le
    exact ⟨i,first,fun j hj => first_index_unique c hj first⟩
  · rintro ⟨i,hi,_⟩ all
    have bad := (all i).symm.trans hi.2; cases bad

theorem native_failure_partition (f e c : Token → Bool)
    (ready : ∀ i : Fin 8, f (cmpToken i) = true ∧ e (cmpToken i) = true) :
    (¬ ∀ i : Fin 8, c (cmpToken i) = true) ↔
    ∃! i : Fin 8, run f e c 40 (cmpToken i) = .failed := by
  simp only [comparison_failed_prefix f e c _ (finite_run_solves f e c) ready]
  exact first_failure_partition c

def signature (s : Token → State) (i : Fin 8) : ℕ := if s (cmpToken i) = .failed then 1 else 0
def basis (i j : Fin 8) : ℕ := if j = i then 1 else 0

theorem native_signature_at_failure (f e c : Token → Bool)
    (ready : ∀ i : Fin 8, f (cmpToken i) = true ∧ e (cmpToken i) = true)
    (i : Fin 8) (hi : run f e c 40 (cmpToken i) = .failed) :
    signature (run f e c 40) = basis i := by
  funext j
  have iff : run f e c 40 (cmpToken j) = .failed ↔ j = i := by
    constructor
    · intro hj
      exact first_index_unique c
        ((comparison_failed_prefix f e c _ (finite_run_solves f e c) ready j).mp hj)
        ((comparison_failed_prefix f e c _ (finite_run_solves f e c) ready i).mp hi)
    · rintro rfl; exact hi
  simp only [signature,basis,iff]

theorem native_signature_unique (f e c : Token → Bool)
    (ready : ∀ i : Fin 8, f (cmpToken i) = true ∧ e (cmpToken i) = true)
    (fails : ¬ ∀ i : Fin 8, c (cmpToken i) = true) :
    ∃! i : Fin 8, signature (run f e c 40) = basis i := by
  obtain ⟨i,hi,_⟩ := (native_failure_partition f e c ready).mp fails
  refine ⟨i,native_signature_at_failure f e c ready i hi,?_⟩
  intro j hj
  have hji : basis j i = 1 := by
    rw [← hj]; simp [signature,hi]
  have : i = j := by simpa [basis] using hji
  exact this.symm

theorem native_signature_component_sum (f e c : Token → Bool)
    (ready : ∀ i : Fin 8, f (cmpToken i) = true ∧ e (cmpToken i) = true)
    (fails : ¬ ∀ i : Fin 8, c (cmpToken i) = true) :
    (∑ i : Fin 8, signature (run f e c 40) i) = 1 := by
  obtain ⟨i,hi,_⟩ := native_signature_unique f e c ready fails
  rw [hi]
  rw [Finset.sum_eq_single i]
  · simp [basis]
  · intro j _ hji; simp [basis,hji]
  · intro h; exact False.elim (h (Finset.mem_univ i))

theorem first_and_last_conditions (c : Token → Bool) :
    (First c 0 ↔ c (cmpToken 0) = false) ∧
    (First c 7 ↔ (∀ i : Fin 7, c (cmpToken i.castSucc) = true) ∧ c (cmpToken 7) = false) := by
  constructor
  · simp [First,Prefix]
  · have hp : Prefix c 7 ↔ ∀ i : Fin 7, c (cmpToken i.castSucc) = true := by
      constructor
      · intro h i; exact h i.castSucc (show i.val < 7 from i.isLt)
      · intro h j hj
        exact h ⟨j.val,by omega⟩
    simp only [First,hp]

theorem native_region_union {E : Type*} (f e c : E → Token → Bool)
    (ready : ∀ x, ∀ i : Fin 8, f x (cmpToken i) = true ∧ e x (cmpToken i) = true) :
    {x | ¬ ∀ i : Fin 8, c x (cmpToken i) = true} =
      ⋃ i : Fin 8, {x | run (f x) (e x) (c x) 40 (cmpToken i) = .failed} := by
  ext x
  simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
  constructor
  · intro h; exact ((native_failure_partition (f x) (e x) (c x) (ready x)).mp h).exists
  · rintro ⟨i,hi⟩ all
    have ff := (comparison_failed_prefix (f x) (e x) (c x) _
      (finite_run_solves _ _ _) (ready x) i).mp hi
    have bad := (all i).symm.trans ff.2; cases bad

theorem native_regions_disjoint {E : Type*} (f e c : E → Token → Bool)
    (ready : ∀ x, ∀ i : Fin 8, f x (cmpToken i) = true ∧ e x (cmpToken i) = true)
    (i j : Fin 8) (ne : i ≠ j) :
    Disjoint {x | run (f x) (e x) (c x) 40 (cmpToken i) = .failed}
      {x | run (f x) (e x) (c x) 40 (cmpToken j) = .failed} := by
  apply Set.disjoint_left.mpr
  intro x hi hj
  exact ne (first_index_unique (c x)
    ((comparison_failed_prefix _ _ _ _ (finite_run_solves _ _ _) (ready x) i).mp hi)
    ((comparison_failed_prefix _ _ _ _ (finite_run_solves _ _ _) (ready x) j).mp hj))

theorem unrefined_region_signature {E : Type*} (f e c : E → Token → Bool)
    (ready : ∀ x, ∀ i : Fin 8, f x (cmpToken i) = true ∧ e x (cmpToken i) = true)
    (i : Fin 8) (R : Set E)
    (sub : R ⊆ {x | run (f x) (e x) (c x) 40 (cmpToken i) = .failed})
    (x : E) (hx : x ∈ R) : signature (run (f x) (e x) (c x) 40) = basis i :=
  native_signature_at_failure _ _ _ (ready x) i (sub hx)

end LCTR.CoreComparisonFailure
