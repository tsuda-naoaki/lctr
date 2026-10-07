import CoreRepresentationImages
import LCTR.ImageInverseConstruction
import Mathlib.Topology.Algebra.Ring.Real

namespace LCTR.CoreLocalCharts
set_option autoImplicit false
open LCTR.CoreRepresentationImages
variable {T TI : Type} {Val VI : Fin 2 → Type}

structure Chart (X Y : Type) where
  source : Set X
  target : Set Y
  coordinates : source ≃ target

abbrev Index (TI : Type) (VI : Fin 2 → Type) := TI × ((s : Fin 2) → VI s)

structure Atlas (T TI : Type) (Val VI : Fin 2 → Type) where
  dim : Fin 2 → ℕ
  value : (s : Fin 2) → T → Val s
  time : TI → Chart T ℝ
  valChart : (s : Fin 2) → VI s → Chart (Val s) (Fin (dim s) → ℝ)
  timeIndexNonempty : Nonempty TI
  valueIndexNonempty : ∀ s, Nonempty (VI s)
  timeOpen : ∀ i, IsOpen (time i).target
  valueOpen : ∀ s i, IsOpen (valChart s i).target
  cover : ∀ t, ∃ i : Index TI VI,
    t ∈ (time i.1).source ∧ ∀ s, value s t ∈ (valChart s (i.2 s)).source

variable (a : Atlas T TI Val VI) (i : Index TI VI)
abbrev JointDomain := {t : T // t ∈ (a.time i.1).source ∧
  ∀ s, a.value s t ∈ (a.valChart s (i.2 s)).source}
def timeValue (t : JointDomain a i) : ℝ :=
  ((a.time i.1).coordinates ⟨t.val,t.property.1⟩).val
abbrev NumericDomain := Set.range (timeValue a i)
def timeCoord : JointDomain a i → NumericDomain a i := imageProjection (timeValue a i)

theorem time_value_injective : Function.Injective (timeValue a i) := by
  intro x y h
  apply Subtype.ext
  have same : (a.time i.1).coordinates ⟨x.val,x.property.1⟩ =
      (a.time i.1).coordinates ⟨y.val,y.property.1⟩ := Subtype.ext h
  exact congrArg (fun z : (a.time i.1).source => z.val) ((a.time i.1).coordinates.injective same)

theorem time_coordinate_bijective : Function.Bijective (timeCoord a i) := by
  refine ⟨?_,imageProjection_surjective _⟩
  intro x y h
  exact time_value_injective a i (congrArg (fun z : NumericDomain a i => z.val) h)

noncomputable def inverse : NumericDomain a i → JointDomain a i :=
  LCTR.ImageInverseConstruction.inverse (timeValue a i)

theorem inverse_left (t : JointDomain a i) : inverse a i (timeCoord a i t) = t :=
  LCTR.ImageInverseConstruction.inverse_left _ (time_value_injective a i) t

theorem inverse_right (theta : NumericDomain a i) : timeCoord a i (inverse a i theta) = theta :=
  Subtype.ext (LCTR.ImageInverseConstruction.inverse_right _ theta)

abbrev CoordinateValues := (s : Fin 2) → (a.valChart s (i.2 s)).target

def atSource (t : JointDomain a i) : CoordinateValues a i :=
  fun s => (a.valChart s (i.2 s)).coordinates ⟨a.value s t.val,t.property.2 s⟩

noncomputable def curve (theta : NumericDomain a i) : CoordinateValues a i :=
  atSource a i (inverse a i theta)

theorem coordinate_curve_generated (t : JointDomain a i) :
    curve a i (timeCoord a i t) = atSource a i t := by
  unfold curve
  rw [inverse_left]

theorem side_curve_generated (t : JointDomain a i) (s : Fin 2) :
    curve a i (timeCoord a i t) s =
      (a.valChart s (i.2 s)).coordinates ⟨a.value s t.val,t.property.2 s⟩ :=
  congrFun (coordinate_curve_generated a i t) s

theorem curve_unique (f : NumericDomain a i → CoordinateValues a i)
    (hf : ∀ t, f (timeCoord a i t) = atSource a i t) : f = curve a i := by
  funext theta
  obtain ⟨t,rfl⟩ := (time_coordinate_bijective a i).2 theta
  exact (hf t).trans (coordinate_curve_generated a i t).symm

theorem joint_domain_coverage (t : T) :
    ∃ i : Index TI VI, ∃ x : JointDomain a i, x.val = t := by
  obtain ⟨j,hj⟩ := a.cover t
  exact ⟨j,⟨t,hj⟩,rfl⟩

theorem generation_at_every_time (t : T) :
    ∃ i : Index TI VI, ∃ x : JointDomain a i,
      x.val = t ∧ curve a i (timeCoord a i x) = atSource a i x := by
  obtain ⟨j,x,hx⟩ := joint_domain_coverage a t
  exact ⟨j,x,hx,coordinate_curve_generated a j x⟩

theorem inverse_agrees_with_time_chart (theta : NumericDomain a i) :
    ∃ ht : theta.val ∈ (a.time i.1).target,
      ((a.time i.1).coordinates.symm ⟨theta.val,ht⟩).val = (inverse a i theta).val := by
  obtain ⟨t,rfl⟩ := (time_coordinate_bijective a i).2 theta
  refine ⟨((a.time i.1).coordinates ⟨t.val,t.property.1⟩).property,?_⟩
  rw [inverse_left]
  exact congrArg Subtype.val ((a.time i.1).coordinates.symm_apply_apply ⟨t.val,t.property.1⟩)

end LCTR.CoreLocalCharts
