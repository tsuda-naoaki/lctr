import CoreContinuumEncoding
import CoreFiniteAudit

namespace LCTR.CoreApproximateBoundary
set_option autoImplicit false
open Set LCTR.CoreEvaluation LCTR.CoreTokenGraph LCTR.CoreFiniteAudit
open LCTR.SelectedInputEvaluation
open LCTR.CoreContinuumBoundary LCTR.CoreContinuumIntegration LCTR.CoreContinuumEncoding
open scoped ENNReal

def Complete (q : Token → State) : Prop := ∀ i : Fin 9, q (approxToken i) = .sat
def FailedScale {Λ : Type*} (q : Λ → Token → State) : Set Λ :=
  {x | ∃ i : Fin 9, q x (approxToken i) = .failed}
def UnsatisfiedScale {Λ : Type*} (q : Λ → Token → State) : Set Λ :=
  {x | ¬ Complete (q x)}

theorem failure_implies_noncompletion {Λ : Type*} (q : Λ → Token → State) :
    FailedScale q ⊆ UnsatisfiedScale q := by
  rintro x ⟨i,hi⟩ hc
  have bad := (hc i).symm.trans hi
  cases bad

theorem least_failure_after_boundary {Λ : Type*} [Preorder Λ]
    (q : Λ → Token → State) (a b : Λ)
    (ha : IsLeast (FailedScale q) a) (hb : IsLeast (UnsatisfiedScale q) b) : b ≤ a :=
  least_subset _ _ (failure_implies_noncompletion q) a b ha hb

theorem scale_sets_equal_if_failure_detected {Λ : Type*} (q : Λ → Token → State)
    (detect : ∀ x, ¬ Complete (q x) → ∃ i : Fin 9, q x (approxToken i) = .failed) :
    FailedScale q = UnsatisfiedScale q :=
  Set.Subset.antisymm (failure_implies_noncompletion q) detect

theorem least_scales_equal_if_failure_detected {Λ : Type*} [PartialOrder Λ]
    (q : Λ → Token → State)
    (detect : ∀ x, ¬ Complete (q x) → ∃ i : Fin 9, q x (approxToken i) = .failed)
    (a b : Λ) (ha : IsLeast (FailedScale q) a) (hb : IsLeast (UnsatisfiedScale q) b) : a = b := by
  rw [scale_sets_equal_if_failure_detected q detect] at ha
  exact le_antisymm (ha.2 hb.1) (hb.2 ha.1)

theorem initial_completion_interval {Λ : Type*} [LinearOrder Λ]
    (q : Λ → Token → State) (hi : Initial {x | Complete (q x)}) (b : Λ)
    (hb : IsLeast (UnsatisfiedScale q) b) :
    MaximalInitial {x | Complete (q x)} = Iio b :=
  (maximal_initial_eq _ hi).trans (initial_boundary _ hi b hb)

theorem least_failure_unique {Λ : Type*} [PartialOrder Λ]
    (q : Λ → Token → State) (a b : Λ)
    (ha : IsLeast (FailedScale q) a) (hb : IsLeast (FailedScale q) b) : a = b :=
  le_antisymm (ha.2 hb.1) (hb.2 ha.1)

def failedTokens (q : Token → State) : Finset Token :=
  Finset.univ.filter (fun t => q t = .failed)

theorem least_failure_case {Λ : Type*} [Preorder Λ]
    (q : Λ → Token → State) (a : Λ) (ha : IsLeast (FailedScale q) a) :
    (∃ i : Fin 9, q a (approxToken i) = .failed) ∧
    (failureCase (failedTokens (q a)).card = .unique ∨
      failureCase (failedTokens (q a)).card = .parallel) := by
  refine ⟨ha.1,?_⟩
  obtain ⟨i,hi⟩ := ha.1
  have hn : (failedTokens (q a)).Nonempty := ⟨approxToken i,by simp [failedTokens,hi]⟩
  have hp := Finset.card_pos.mpr hn
  by_cases hc : (failedTokens (q a)).card = 1
  · exact Or.inl ((case_exact _).2.1.mpr hc)
  · exact Or.inr ((case_exact _).2.2.mpr (by omega))

theorem unformed_scale_separation_control :
    FailedScale (fun (_ : Unit) (_ : Token) => .unformed) = ∅ ∧
    UnsatisfiedScale (fun (_ : Unit) (_ : Token) => .unformed) = Set.univ := by
  constructor
  · simp [FailedScale]
  · ext x
    simp [UnsatisfiedScale,Complete]

structure ScaleInput (Λ : Type*) where
  formed : Λ → Token → Bool
  evaluated : Λ → Token → Bool
  condition : Λ → Token → Bool
  defect : Λ → Fin 9 → ℝ≥0∞
  tolerance : Fin 9 → ℝ≥0∞
  qualitative : Λ → Fin 9 → Bool
  matching : ∀ x i, condition x (approxToken i) = paperCondition (defect x) tolerance (qualitative x) i
  inputs : ∀ x, InputSat (formed x) (evaluated x) (run (formed x) (evaluated x) (condition x) 40)

def states {Λ : Type*} (a : ScaleInput Λ) (x : Λ) : Token → State :=
  run (a.formed x) (a.evaluated x) (a.condition x) 40
def defects {Λ : Type*} (a : ScaleInput Λ) (x : Λ) : Fin 9 → ℝ≥0∞ :=
  paperDefect (a.defect x) (a.qualitative x)
noncomputable def tolerances {Λ : Type*} (a : ScaleInput Λ) : Fin 9 → ℝ≥0∞ :=
  paperTolerance a.tolerance
noncomputable def signature {Λ : Type*} (a : ScaleInput Λ) (x : Λ) (i : Fin 9) : Bool :=
  by classical exact decide (i ∈ Exceeded (defects a x) (tolerances a))

theorem native_completion_threshold {Λ : Type*} (a : ScaleInput Λ) (x : Λ) :
    Complete (states a x) ↔ Valid (defects a x) (tolerances a) :=
  (source_quantitative_validity (a.formed x) (a.evaluated x) (a.condition x) _
    (finite_run_solves _ _ _) (a.inputs x) (a.defect x) a.tolerance (a.qualitative x) (a.matching x)).1

theorem native_validity_initial {Λ : Type*} [Preorder Λ] (a : ScaleInput Λ)
    (mono : ∀ i, Monotone (fun x => defects a x i)) : Initial {x | Complete (states a x)} := by
  simp only [native_completion_threshold]
  exact monotone_defects_initial (defects a) (tolerances a) mono

theorem native_maximal_interval {Λ : Type*} [Preorder Λ] (a : ScaleInput Λ)
    (mono : ∀ i, Monotone (fun x => defects a x i)) :
    MaximalInitial {x | Complete (states a x)} = {x | Complete (states a x)} :=
  maximal_initial_eq _ (native_validity_initial a mono)

theorem native_all_scales_valid {Λ : Type*} [Preorder Λ] (a : ScaleInput Λ)
    (all : ∀ x, Complete (states a x)) : MaximalInitial {x | Complete (states a x)} = Set.univ := by
  have he : {x | Complete (states a x)} = Set.univ := by ext x; simp [all]
  rw [he]
  exact maximal_initial_eq _ (fun _ _ _ _ => Set.mem_univ _)

theorem native_boundary_nonzero_signature {Λ : Type*} [LinearOrder Λ]
    (a : ScaleInput Λ) (mono : ∀ i, Monotone (fun x => defects a x i)) (b : Λ)
    (hb : IsLeast (UnsatisfiedScale (states a)) b) :
    MaximalInitial {x | Complete (states a x)} = Iio b ∧
    signature a b ≠ (fun _ => false) ∧
    (∀ x, x < b → signature a x = (fun _ => false)) := by
  have interval := initial_completion_interval (states a) (native_validity_initial a mono) b hb
  have bad : Exceeded (defects a b) (tolerances a) ≠ ∅ := by
    intro he
    exact hb.1 ((native_completion_threshold a b).mpr
      ((validity_characterizations _ _).2.2.mpr he))
  refine ⟨interval,?_,?_⟩
  · intro hz
    obtain ⟨i,hi⟩ := Set.nonempty_iff_ne_empty.mpr bad
    have eq := congrFun hz i
    simp [signature,hi] at eq
  · intro x hx
    have valid : Complete (states a x) := by
      apply (maximal_initial_greatest {y | Complete (states a y)}).1.1
      rw [interval]; exact hx
    have he := (validity_characterizations _ _).2.2.mp ((native_completion_threshold a x).mp valid)
    funext i
    simp [signature,he]

theorem native_saturation_is_valid {Λ : Type*} (a : ScaleInput Λ) (x : Λ) (i : Fin 9)
    (eq : defects a x i = tolerances a i) : a.condition x (approxToken i) = true := by
  rw [a.matching x i,nine_component_encoding]
  exact le_of_eq eq

end LCTR.CoreApproximateBoundary
