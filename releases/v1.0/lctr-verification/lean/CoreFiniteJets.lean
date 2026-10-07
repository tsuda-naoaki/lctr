import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace LCTR.CoreFiniteJets
set_option autoImplicit false
open Set Filter
open scoped Topology
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def monomial (i : ℕ) (a : ℝ) (x : ℝ) : ℝ := (x-a)^i / (i.factorial : ℝ)

theorem monomial_smooth (i : ℕ) (a : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (monomial i a) :=
  ((contDiff_id.sub contDiff_const).pow i).div_const _

theorem monomial_derivative (i n : ℕ) (a : ℝ) :
    iteratedDeriv n (monomial i a) a = if n=i then 1 else 0 := by
  unfold monomial
  rw [iteratedDeriv_div_const]
  have h := congrFun (iteratedDeriv_comp_sub_const n (fun x : ℝ => x^i) a) a
  rw [h,sub_self,iteratedDeriv_fun_pow_zero]
  split_ifs with hi
  · exact div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i))
  · simpa only [Nat.cast_zero] using zero_div (i.factorial : ℝ)

noncomputable def curve (k : ℕ) (a : ℝ) (v : Fin (k+1) → E) (x : ℝ) : E :=
  ∑ i : Fin (k+1), monomial i.val a x • v i

theorem curve_smooth (k : ℕ) (a : ℝ) (v : Fin (k+1) → E) {n : WithTop ℕ∞} :
    ContDiff ℝ n (curve k a v) := by
  apply ContDiff.sum
  intro i _
  exact (monomial_smooth i.val a).smul contDiff_const

theorem curve_derivative (k : ℕ) (a : ℝ) (v : Fin (k+1) → E) (n : Fin (k+1)) :
    iteratedDeriv n.val (curve k a v) a = v n := by
  unfold curve
  rw [iteratedDeriv_fun_sum]
  · have term : ∀ i : Fin (k+1),
        iteratedDeriv n.val (fun x => monomial i.val a x • v i) a =
          if n=i then v i else 0 := by
      intro i
      rw [iteratedDeriv_smul_const (monomial_smooth i.val a).contDiffAt,monomial_derivative]
      by_cases h : n=i
      · subst i
        simp
      · have hn : n.val ≠ i.val := fun hv => h (Fin.ext hv)
        simp [h,hn]
    simp only [term]
    simp
  · intro i _
    exact ((monomial_smooth i.val a).smul contDiff_const).contDiffAt

theorem finite_jet_realization (k : ℕ) (a : ℝ) (v : Fin (k+1) → E) :
    ∃ f : ℝ → E, ContDiff ℝ ⊤ f ∧ ∀ n : Fin (k+1), iteratedDeriv n.val f a = v n :=
  ⟨curve k a v,curve_smooth k a v,curve_derivative k a v⟩

theorem realization_in_open_value_chart (k : ℕ) (a : ℝ) (v : Fin (k+1) → E)
    (V : Set E) (hv : IsOpen V) (h0 : v 0 ∈ V) :
    ∃ f : ℝ → E, ContDiff ℝ ⊤ f ∧ (∀ n : Fin (k+1), iteratedDeriv n.val f a = v n) ∧
      ∀ᶠ x in 𝓝 a, f x ∈ V := by
  let f := curve k a v
  have hder : ∀ n : Fin (k+1), iteratedDeriv n.val f a = v n := curve_derivative k a v
  have hfa : f a = v 0 := by simpa only [Fin.val_zero,iteratedDeriv_zero] using hder 0
  have hf : ContDiff ℝ ⊤ f := curve_smooth k a v
  refine ⟨f,hf,hder,?_⟩
  exact hf.continuous.continuousAt (hv.mem_nhds (hfa.symm ▸ h0))

theorem realization_in_time_and_value_charts (k : ℕ) (a : ℝ) (v : Fin (k+1) → E)
    (U : Set ℝ) (hu : IsOpen U) (ha : a ∈ U)
    (V : Set E) (hv : IsOpen V) (h0 : v 0 ∈ V) :
    ∃ f : ℝ → E, ContDiff ℝ ⊤ f ∧ (∀ n : Fin (k+1), iteratedDeriv n.val f a = v n) ∧
      ∀ᶠ x in 𝓝 a, x ∈ U ∧ f x ∈ V := by
  obtain ⟨f,hf,hd,hg⟩ := realization_in_open_value_chart k a v V hv h0
  exact ⟨f,hf,hd,Filter.Eventually.and (hu.mem_nhds ha) hg⟩

noncomputable def jet (k : ℕ) (a : ℝ) (f : ℝ → E) : Fin (k+1) → E :=
  fun n => iteratedDeriv n.val f a

theorem smooth_jet_projection_surjective (k : ℕ) (a : ℝ) :
    Function.Surjective (fun f : {f : ℝ → E // ContDiff ℝ ⊤ f} => jet k a f.val) := by
  intro v
  refine ⟨⟨curve k a v,curve_smooth k a v⟩,?_⟩
  funext n
  exact curve_derivative k a v n

theorem zeroth_order_control (a : ℝ) (v : Fin 1 → E) : curve 0 a v a = v 0 := by
  simpa only [Fin.val_zero,iteratedDeriv_zero] using curve_derivative 0 a v 0

end LCTR.CoreFiniteJets
