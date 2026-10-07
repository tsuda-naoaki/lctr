import CoreTokenGraph
import CoreContinuumBoundary

namespace LCTR.CoreContinuumIntegration
set_option autoImplicit false
open Set LCTR.CoreEvaluation LCTR.CoreTokenGraph LCTR.SelectedInputEvaluation
open LCTR.CoreContinuumBoundary
open scoped ENNReal

theorem all_sat_iff_tests {A : Type*} (E : A → A → Prop) (wf : WellFounded E)
    (f e c : A → Bool) (s : A → State) (h : Recurs E f e c s) (J : Set A)
    (inputs : ∀ x ∈ J, f x = true ∧ e x = true)
    (outside : ∀ x ∈ J, ∀ y, E y x → y ∉ J → s y = .sat) :
    (∀ x ∈ J, s x = .sat) ↔ (∀ x ∈ J, c x = true) := by
  classical
  constructor
  · intro hs x hx
    have eq := hs x hx
    rw [h x] at eq
    change state (f x) (e x) (decide (∀ y : {y // E y x}, s y.val = .sat)) (c x) = .sat at eq
    exact ((state_sat_iff _ _ _ _).mp eq).2.2.2
  · intro hc x
    apply wf.induction x
    intro x ih hx
    rw [h x]
    change state (f x) (e x) (decide (∀ y : {y // E y x}, s y.val = .sat)) (c x) = .sat
    apply (state_sat_iff _ _ _ _).mpr
    refine ⟨(inputs x hx).1,(inputs x hx).2,?_,hc x hx⟩
    simp only [decide_eq_true_eq]
    intro y
    by_cases hy : y.val ∈ J
    · exact ih y.val y.property hy
    · exact outside x hx y.val y.property hy

def approxToken (i : Fin 9) : Token := ⟨3,i⟩
def ApproxSet : Set Token := {t | series t = 3}

theorem approx_predecessor_kinds : ∀ x y : Token, series x = 3 → Edge y x →
    series y = 3 ∨ series y = 2 := by decide

theorem approx_index_bijection : Function.Bijective
    (fun i : Fin 9 => (⟨approxToken i,rfl⟩ : ApproxSet)) := by
  constructor
  · intro i j h
    have eq : approxToken i = approxToken j := congrArg Subtype.val h
    exact Sigma.mk.inj_iff.mp eq |>.2 |> eq_of_heq
  · rintro ⟨⟨t,i⟩,h⟩
    have ht : t = (3 : Fin 6) := Fin.ext h
    subst t
    exact ⟨i,rfl⟩

theorem approx_all_iff (P : Token → Prop) :
    (∀ t ∈ ApproxSet, P t) ↔ ∀ i : Fin 9, P (approxToken i) := by
  constructor
  · intro h i; exact h _ rfl
  · intro h t ht
    obtain ⟨i,hi⟩ := approx_index_bijection.2 ⟨t,ht⟩
    have eq : approxToken i = t := congrArg Subtype.val hi
    rw [←eq]; exact h i

def InputSat (f e : Token → Bool) (s : Token → State) : Prop :=
  (∀ t, series t = 2 → s t = .sat) ∧
  (∀ t ∈ ApproxSet, f t = true ∧ e t = true)

theorem approx_states_iff_conditions (f e c : Token → Bool) (s : Token → State)
    (h : Recurs Edge f e c s) (inp : InputSat f e s) :
    (∀ i : Fin 9, s (approxToken i) = .sat) ↔
    (∀ i : Fin 9, c (approxToken i) = true) := by
  rw [← approx_all_iff (fun t => s t = .sat), ← approx_all_iff (fun t => c t = true)]
  apply all_sat_iff_tests Edge (LCTR.CoreDagRecursion.finite_acyclic_wellFounded Edge acyclic)
    f e c s h ApproxSet inp.2
  intro x hx y hy ny
  rcases approx_predecessor_kinds x y hx hy with ha | hd
  · exact False.elim (ny ha)
  · exact inp.1 y hd

theorem quantitative_validity (f e c : Token → Bool) (s : Token → State)
    (h : Recurs Edge f e c s) (inp : InputSat f e s) (d eps : Fin 9 → ℝ≥0∞)
    (encoding : ∀ i, c (approxToken i) = true ↔ d i ≤ eps i) :
    ((∀ i, s (approxToken i) = .sat) ↔ Valid d eps) ∧
    ((∀ i, s (approxToken i) = .sat) ↔ ∀ i, 0 ≤ margin (eps i) (d i)) ∧
    ((∀ i, s (approxToken i) = .sat) ↔ ∀ i, excess (eps i) (d i) = 0) ∧
    ((∀ i, s (approxToken i) = .sat) ↔ Exceeded d eps = ∅) := by
  have v : (∀ i, s (approxToken i) = .sat) ↔ Valid d eps := by
    rw [approx_states_iff_conditions f e c s h inp]
    exact forall_congr' encoding
  exact ⟨v,v.trans (validity_characterizations d eps).1,
    v.trans (validity_characterizations d eps).2.1,v.trans (validity_characterizations d eps).2.2⟩

theorem operational_first_excess {Λ : Type*} [LinearOrder Λ]
    (f e c : Λ → Token → Bool) (s : Λ → Token → State)
    (recur : ∀ x, Recurs Edge (f x) (e x) (c x) (s x))
    (inp : ∀ x, InputSat (f x) (e x) (s x))
    (d : Λ → Fin 9 → ℝ≥0∞) (eps : Fin 9 → ℝ≥0∞)
    (encoding : ∀ x i, c x (approxToken i) = true ↔ d x i ≤ eps i)
    (mono : ∀ i, Monotone (fun x => d x i)) (b : Λ)
    (hb : IsLeast {x | ¬ ∀ i, s x (approxToken i) = .sat} b) :
    MaximalInitial {x | ∀ i, s x (approxToken i) = .sat} = Iio b ∧
    Exceeded (d b) eps ≠ ∅ ∧ ∀ x, x < b → Exceeded (d x) eps = ∅ := by
  have v : ∀ x, (∀ i, s x (approxToken i) = .sat) ↔ Valid (d x) eps :=
    fun x => (quantitative_validity (f x) (e x) (c x) (s x) (recur x) (inp x)
      (d x) eps (encoding x)).1
  simp only [v] at hb ⊢
  exact first_excess d eps mono b hb

end LCTR.CoreContinuumIntegration
