import CoreLawInputBundle

namespace LCTR.CoreDynamicsBundle
set_option autoImplicit false
open LCTR.CoreTrajectoryDescent LCTR.CoreObserverTime LCTR.CoreNativeCurves
open LCTR.CoreRecordCodes LCTR.CoreNativeObservables LCTR.CoreLawInputBundle
universe u v w
variable {C : Type u} {D : Type v} {B : Type w}
variable {U L J V W P N : Type} {Arr : U → Type}

structure TimeData (d : Input C D B) (inc : IncTrans d) where
  order : OrderTime d inc → OrderTime d inc → Prop
  projection : Time d → OrderTime d inc
  embedding : OrderTime d inc → ℝ
  representation : Time d → ℝ

def TimeSpec (d : Input C D B) (inc : IncTrans d) (rho : RealEmbedding d inc)
    (t : TimeData d inc) : Prop :=
  t.order = orderLt d inc ∧ t.projection = orderProjection d inc ∧
  t.embedding = rho.value ∧ ∀ x, t.representation x = t.embedding (t.projection x)

def timeData (d : Input C D B) (inc : IncTrans d) (rho : RealEmbedding d inc) : TimeData d inc :=
  ⟨orderLt d inc, orderProjection d inc, rho.value, timeRep d inc rho⟩

theorem time_spec (d : Input C D B) (inc : IncTrans d) (rho : RealEmbedding d inc) :
    TimeSpec d inc rho (timeData d inc rho) := ⟨rfl,rfl,rfl,fun _ => rfl⟩

theorem time_unique (d : Input C D B) (inc : IncTrans d) (rho : RealEmbedding d inc)
    (t : TimeData d inc) (ht : TimeSpec d inc rho t) : t = timeData d inc rho := by
  obtain ⟨ho,hp,he,hr⟩ := ht
  have er : t.representation = timeRep d inc rho := by
    funext x
    rw [hr x, he, hp]
    rfl
  cases t
  simp_all [timeData]

structure TrajectoryData (d : Input C D B) (inc : IncTrans d) (rho : RealEmbedding d inc)
    (J V : Type) where
  orderDomain : Set (OrderTime d inc)
  scalar : OrderDomain d inc → State d
  realDomain : Set ℝ
  curves : (J → OrderDomain d inc → V) × (J → RealDomain d inc rho → V)

def TrajectorySpec (d : Input C D B) (inc : IncTrans d) (single : Single d)
    (rho : RealEmbedding d inc) (obs : J → State d → V)
    (t : TrajectoryData d inc rho J V) : Prop :=
  t.orderDomain = OrderDomain d inc ∧ t.realDomain = RealDomain d inc rho ∧
  (∀ x, canonicalTrajectory d single x = t.scalar (restrictedProjection d inc x)) ∧
  (∀ j q, t.curves.1 j q = obs j (t.scalar q)) ∧
  (∀ j q, t.curves.2 j (realEmbedding d inc rho q) = t.curves.1 j q)

noncomputable def trajectoryData (d : Input C D B) (inc : IncTrans d) (single : Single d)
    (fiber : FiberCondition d inc single) (rho : RealEmbedding d inc)
    (obs : J → State d → V) : TrajectoryData d inc rho J V :=
  ⟨OrderDomain d inc, scalarTrajectory d inc single fiber, RealDomain d inc rho,
    (fun j => orderCurve d inc single fiber (obs j),
     fun j => realCurve d inc single fiber rho (obs j))⟩

theorem trajectory_spec (d : Input C D B) (inc : IncTrans d) (single : Single d)
    (fiber : FiberCondition d inc single) (rho : RealEmbedding d inc)
    (obs : J → State d → V) :
    TrajectorySpec d inc single rho obs (trajectoryData d inc single fiber rho obs) := by
  refine ⟨rfl,rfl,(scalar_factor_contract d inc single fiber).1,fun _ _ => rfl,?_⟩
  intro j q
  change orderCurve d inc single fiber (obs j) (realInverse d inc rho (realEmbedding d inc rho q)) = _
  rw [(real_image_inverse_contract d inc rho).2.1 q]
  rfl

theorem trajectory_unique (d : Input C D B) (inc : IncTrans d) (single : Single d)
    (fiber : FiberCondition d inc single) (rho : RealEmbedding d inc)
    (obs : J → State d → V) (t : TrajectoryData d inc rho J V)
    (ht : TrajectorySpec d inc single rho obs t) : t = trajectoryData d inc single fiber rho obs := by
  obtain ⟨hd,hr,hs,ho,hv⟩ := ht
  have es := (scalar_factor_contract d inc single fiber).2 t.scalar hs
  have eo : t.curves.1 = fun j => orderCurve d inc single fiber (obs j) := by
    funext j q
    rw [ho j q, es]
    rfl
  have ev : t.curves.2 = fun j => realCurve d inc single fiber rho (obs j) := by
    funext j
    apply (observable_factorization d inc single fiber rho (obs j)).2
    intro q
    rw [hv j q, eo]
  have ec : t.curves = (fun j => orderCurve d inc single fiber (obs j),
      fun j => realCurve d inc single fiber rho (obs j)) := Prod.ext eo ev
  cases t
  simp_all [trajectoryData]

structure Description (d : Input C D B) (inc : IncTrans d) (rho : RealEmbedding d inc)
    (J V W P N : Type) where
  law : LawInput d J V W P N
  time : TimeData d inc
  trajectory : TrajectoryData d inc rho J V

def DescriptionSpec (d : Input C D B) (inc : IncTrans d) (single : Single d)
    (rho : RealEmbedding d inc) (a : LocalDatum B U L J V Arr) (h : Descent d a)
    (code : Code D W P N) (x : Description d inc rho J V W P N) : Prop :=
  LawInputSpec d a code x.law ∧ TimeSpec d inc rho x.time ∧
  TrajectorySpec d inc single rho (fun j s => canonical d a h (j,s)) x.trajectory

noncomputable def description (d : Input C D B) (inc : IncTrans d) (single : Single d)
    (fiber : FiberCondition d inc single) (rho : RealEmbedding d inc)
    (a : LocalDatum B U L J V Arr) (h : Descent d a) (code : Code D W P N) :
    Description d inc rho J V W P N :=
  ⟨lawInput d single a h code, timeData d inc rho,
    trajectoryData d inc single fiber rho (fun j s => canonical d a h (j,s))⟩

theorem description_spec (d : Input C D B) (inc : IncTrans d) (single : Single d)
    (fiber : FiberCondition d inc single) (rho : RealEmbedding d inc)
    (a : LocalDatum B U L J V Arr) (h : Descent d a) (code : Code D W P N) :
    DescriptionSpec d inc single rho a h code (description d inc single fiber rho a h code) :=
  ⟨law_input_spec d single a h code, time_spec d inc rho,
    trajectory_spec d inc single fiber rho _⟩

theorem description_unique (d : Input C D B) (inc : IncTrans d) (single : Single d)
    (fiber : FiberCondition d inc single) (rho : RealEmbedding d inc)
    (a : LocalDatum B U L J V Arr) (h : Descent d a) (code : Code D W P N)
    (x : Description d inc rho J V W P N) (hx : DescriptionSpec d inc single rho a h code x) :
    x = description d inc single fiber rho a h code := by
  have el := law_input_unique d single a h code x.law hx.1
  have et := time_unique d inc rho x.time hx.2.1
  have er := trajectory_unique d inc single fiber rho _ x.trajectory hx.2.2
  cases x
  simp_all [description]

theorem description_exists_unique (d : Input C D B) (inc : IncTrans d) (single : Single d)
    (fiber : FiberCondition d inc single) (rho : RealEmbedding d inc)
    (a : LocalDatum B U L J V Arr) (h : Descent d a) (code : Code D W P N) :
    ∃! x : Description d inc rho J V W P N, DescriptionSpec d inc single rho a h code x :=
  ⟨description d inc single fiber rho a h code, description_spec d inc single fiber rho a h code,
    description_unique d inc single fiber rho a h code⟩

def WitnessSpec (d : Input C D B) (inc : IncTrans d) (single : Single d)
    (rho : RealEmbedding d inc) (a : LocalDatum B U L J V Arr) (h : Descent d a)
    (code : Code D W P N)
    (x : LawInput d J V W P N × Description d inc rho J V W P N) : Prop :=
  LawInputSpec d a code x.1 ∧ DescriptionSpec d inc single rho a h code x.2 ∧ x.1 = x.2.law

theorem witness_exists_unique (d : Input C D B) (inc : IncTrans d) (single : Single d)
    (fiber : FiberCondition d inc single) (rho : RealEmbedding d inc)
    (a : LocalDatum B U L J V Arr) (h : Descent d a) (code : Code D W P N) :
    ∃! x : LawInput d J V W P N × Description d inc rho J V W P N,
      WitnessSpec d inc single rho a h code x := by
  refine ⟨(lawInput d single a h code, description d inc single fiber rho a h code),
    ⟨law_input_spec d single a h code, description_spec d inc single fiber rho a h code, rfl⟩, ?_⟩
  intro x hx
  exact Prod.ext (law_input_unique d single a h code x.1 hx.1)
    (description_unique d inc single fiber rho a h code x.2 hx.2.1)

theorem shared_input_exact (d : Input C D B) (inc : IncTrans d) (single : Single d)
    (fiber : FiberCondition d inc single) (rho : RealEmbedding d inc)
    (a : LocalDatum B U L J V Arr) (h : Descent d a) (code : Code D W P N)
    (j : J) (x : Domain d) :
    (description d inc single fiber rho a h code).law.observables.values
        (j,(description d inc single fiber rho a h code).law.trajectory x) =
      (description d inc single fiber rho a h code).trajectory.curves.2 j
        (realEmbedding d inc rho (restrictedProjection d inc x)) := by
  have hx := (observable_factorization d inc single fiber rho (fun s => canonical d a h (j,s))).1 x
  exact hx.1.trans hx.2

theorem curve_range_preserved (d : Input C D B) (inc : IncTrans d) (single : Single d)
    (fiber : FiberCondition d inc single) (rho : RealEmbedding d inc)
    (a : LocalDatum B U L J V Arr) (h : Descent d a) (code : Code D W P N)
    (j : J) (t : RealDomain d inc rho) :
    (description d inc single fiber rho a h code).trajectory.curves.2 j t ∈
      (description d inc single fiber rho a h code).law.observables.ranges j :=
  canonical_value_typed d a h j (scalarTrajectory d inc single fiber (realInverse d inc rho t))

end LCTR.CoreDynamicsBundle
