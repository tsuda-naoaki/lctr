import CoreContinuumIntegration
import Mathlib.Topology.Semicontinuity.Defs
import Mathlib.Topology.Order.Basic

namespace LCTR.CoreContinuumTopology
set_option autoImplicit false
open Set LCTR.CoreContinuumBoundary LCTR.CoreContinuumIntegration
open LCTR.CoreTokenGraph LCTR.CoreEvaluation LCTR.SelectedInputEvaluation
open scoped ENNReal
open Topology

theorem positive_domain_open {X I : Type*} [TopologicalSpace X] [Finite I]
    (m : X → I → EReal) (h : ∀ i, LowerSemicontinuous (fun x => m x i)) :
    IsOpen {x | ∀ i, 0 < m x i} := by
  have hi : ∀ i, IsOpen {x | 0 < m x i} := by
    intro i
    exact isOpen_iff_mem_nhds.mpr (fun x hx => h i x 0 hx)
  have eq : {x | ∀ i, 0 < m x i} = ⋂ i, {x | 0 < m x i} := by ext x; simp
  rw [eq]
  exact isOpen_iInter_of_finite hi

theorem open_neighborhood_iff {X : Type*} [TopologicalSpace X] (V : Set X)
    (h : IsOpen V) (x : X) :
    x ∈ V ↔ ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ W ⊆ V := by
  constructor
  · intro hx; exact ⟨V,h,hx,Subset.rfl⟩
  · rintro ⟨W,_,hx,hW⟩; exact hW hx

def OperationalRobust (s : Token → State) (d eps : Fin 9 → ℝ≥0∞) : Prop :=
  (∀ i, s (approxToken i) = .sat) ∧ ∀ i, 0 < margin (eps i) (d i)

theorem robust_positive_iff (f e c : Token → Bool) (s : Token → State)
    (h : Recurs Edge f e c s) (inp : InputSat f e s) (d eps : Fin 9 → ℝ≥0∞)
    (encoding : ∀ i, c (approxToken i) = true ↔ d i ≤ eps i) :
    OperationalRobust s d eps ↔ ∀ i, 0 < margin (eps i) (d i) := by
  constructor
  · exact fun r => r.2
  · intro pos
    refine ⟨(quantitative_validity f e c s h inp d eps encoding).1.mpr ?_,pos⟩
    intro i; exact (margin_nonneg _ _).mp (pos i).le

theorem operational_robust_domain_open {X : Type*} [TopologicalSpace X]
    (f e c : X → Token → Bool) (s : X → Token → State)
    (h : ∀ x, Recurs Edge (f x) (e x) (c x) (s x))
    (inp : ∀ x, InputSat (f x) (e x) (s x)) (d : X → Fin 9 → ℝ≥0∞) (eps : Fin 9 → ℝ≥0∞)
    (encoding : ∀ x i, c x (approxToken i) = true ↔ d x i ≤ eps i)
    (lsc : ∀ i, LowerSemicontinuous (fun x => margin (eps i) (d x i))) :
    IsOpen {x | OperationalRobust (s x) (d x) eps} := by
  have eq : {x | OperationalRobust (s x) (d x) eps} =
      {x | ∀ i, 0 < margin (eps i) (d x i)} := by
    ext x
    exact robust_positive_iff (f x) (e x) (c x) (s x) (h x) (inp x) (d x) eps (encoding x)
  rw [eq]
  exact positive_domain_open _ lsc

theorem source_order_topology_neighborhood {X : Type*} [LinearOrder X]
    [TopologicalSpace X] [OrderTopology X]
    (f e c : X → Token → Bool) (s : X → Token → State)
    (h : ∀ x, Recurs Edge (f x) (e x) (c x) (s x))
    (inp : ∀ x, InputSat (f x) (e x) (s x)) (d : X → Fin 9 → ℝ≥0∞) (eps : Fin 9 → ℝ≥0∞)
    (encoding : ∀ x i, c x (approxToken i) = true ↔ d x i ≤ eps i)
    (lsc : ∀ i, LowerSemicontinuous (fun x => margin (eps i) (d x i))) (x : X) :
    OperationalRobust (s x) (d x) eps ↔
    ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ W ⊆ {y | OperationalRobust (s y) (d y) eps} :=
  open_neighborhood_iff _ (operational_robust_domain_open f e c s h inp d eps encoding lsc) x

theorem missing_input_control :
    Recurs Edge (fun _ => false) (fun _ => true) (fun _ => true) (fun _ => .unformed) ∧
    (∀ _i : Fin 9, 0 < margin 1 0) ∧
    ¬ OperationalRobust (fun _ => .unformed) (fun _ => 0) (fun _ => 1) := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro x; simp [LCTR.CoreEvaluation.update,state]
  · intro i; exact (margin_positive 1 0).mpr (by simp)
  · intro bad; have contra := bad.1 (0 : Fin 9); cases contra

end LCTR.CoreContinuumTopology
