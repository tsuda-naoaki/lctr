import CoreDynamicsBundle
import CoreNativeLawGeneration

namespace LCTR.CoreLawDifferentialBundle
set_option autoImplicit false
open LCTR.CoreObserverTime LCTR.CoreNativeCurves LCTR.CoreRecordCodes
open LCTR.CoreNativeObservables LCTR.CoreDynamicsBundle
open LCTR.CoreNativeLawComponents LCTR.LawTimeTransport LCTR.LawFamilyTransport
variable {C D B U L J V W P N A : Type} {Arr : U → Type}

structure Basis (C D B U L J V W P N : Type) (Arr : U → Type) where
  data : Input C D B
  inc : IncTrans data
  single : Single data
  fiber : FiberCondition data inc single
  rho : RealEmbedding data inc
  localDatum : LocalDatum B U L J V Arr
  descent : Descent data localDatum
  code : Code D W P N

variable (b : Basis C D B U L J V W P N Arr)
abbrev ObsValue (j : J) : Type := ↥(canonicalRange b.localDatum b.descent.indexSurj j)
noncomputable def context : Context C D B J (ObsValue b) :=
  ⟨b.data,b.inc,b.single,b.fiber,b.rho,typedObservable b.data b.localDatum b.descent⟩
noncomputable def dynamics := description b.data b.inc b.single b.fiber b.rho b.localDatum b.descent b.code
abbrev LawData := CoreNativeLawGeneration.LawInput (context b) A

variable (a : LawData (A := A) b)
abbrev CandidateFamily := Family (NativeTime (context b)) A
  (fun j => Values (Val := ObsValue b) (a.component j).inIndices)
  (fun j => Values (Val := ObsValue b) (a.component j).outIndices)
noncomputable def candidates : CandidateFamily b a := CoreNativeLawGeneration.family (context b) a

def CoreSpec (x : Description b.data b.inc b.rho J V W P N × CandidateFamily b a) : Prop :=
  DescriptionSpec b.data b.inc b.single b.rho b.localDatum b.descent b.code x.1 ∧ x.2 = candidates b a

theorem law_core_exists_unique :
    ∃! x : Description b.data b.inc b.rho J V W P N × CandidateFamily b a, CoreSpec b a x := by
  refine ⟨(dynamics b,candidates b a),
    ⟨description_spec b.data b.inc b.single b.fiber b.rho b.localDatum b.descent b.code,rfl⟩,?_⟩
  intro x hx
  exact Prod.ext
    (description_unique b.data b.inc b.single b.fiber b.rho b.localDatum b.descent b.code x.1 hx.1) hx.2

theorem law_core_validity (conditions : AllConditions (candidates b a)) :
    AllConditions (candidates b a) ∧
    (∃ t, common (candidates b a) t) ∧ a.allowed (common (candidates b a)) :=
  ⟨conditions,conditions.2.2.2.2.2⟩

theorem law_core_same_source (t : NativeTime (context b)) (valid : common (candidates b a) t) :
    ∃ x : Domain b.data,
      realEmbedding b.data b.inc b.rho (restrictedProjection b.data b.inc x) = t ∧
      ∀ j, ∃ ht : t ∈ (a.component j).evalTimes,
        evalTuple (generated (context b) (a.component j)) ⟨t,ht⟩ =
          ((t,fun i : (a.component j).inIndices =>
              (context b).observable i.val ((dynamics b).law.trajectory x)),
            fun i : (a.component j).outIndices =>
              (context b).observable i.val ((dynamics b).law.trajectory x)) ∧
        evalTuple (generated (context b) (a.component j)) ⟨t,ht⟩ ∈ (a.component j).candidate :=
  CoreNativeLawGeneration.common_evaluation_source_values (context b) a t valid

abbrev Faithfulness := ((j : A) → Reindex
  (Tuple (NativeTime (context b)) (Values (Val := ObsValue b) (a.component j).inIndices)
    (Values (Val := ObsValue b) (a.component j).outIndices))
  (Tuple (NativeTime (context b)) (Values (Val := ObsValue b) (a.component j).inIndices)
    (Values (Val := ObsValue b) (a.component j).outIndices))) → Prop

structure DifferentialData where
  embedding : OrderTime b.data b.inc → ℝ
  representation : Time b.data → ℝ
  scalar : OrderDomain b.data b.inc → State b.data
  curves : J → RealDomain b.data b.inc b.rho → V
  candidate : CandidateFamily b a
  faithful : Faithfulness b a

def DifferentialSpec (x : DifferentialData b a) : Prop :=
  x.embedding = b.rho.value ∧
  (∀ q, x.representation q = x.embedding (orderProjection b.data b.inc q)) ∧
  (∀ t, canonicalTrajectory b.data b.single t = x.scalar (restrictedProjection b.data b.inc t)) ∧
  (∀ j t, x.curves j (realEmbedding b.data b.inc b.rho (restrictedProjection b.data b.inc t)) =
    canonical b.data b.localDatum b.descent (j,canonicalTrajectory b.data b.single t)) ∧
  x.candidate = candidates b a ∧ x.faithful = x.candidate.faithful

noncomputable def differential : DifferentialData b a :=
  ⟨b.rho.value,timeRep b.data b.inc b.rho,scalarTrajectory b.data b.inc b.single b.fiber,
    fun j => realCurve b.data b.inc b.single b.fiber b.rho
      (fun s => canonical b.data b.localDatum b.descent (j,s)),candidates b a,a.faithful⟩

theorem differential_spec : DifferentialSpec b a (differential b a) := by
  refine ⟨rfl,fun _ => rfl,(scalar_factor_contract b.data b.inc b.single b.fiber).1,?_,rfl,rfl⟩
  intro j t
  have h := (observable_factorization b.data b.inc b.single b.fiber b.rho
    (fun s => canonical b.data b.localDatum b.descent (j,s))).1 t
  exact (h.1.trans h.2).symm

theorem differential_unique (x : DifferentialData b a) (hx : DifferentialSpec b a x) :
    x = differential b a := by
  obtain ⟨he,ht,hs,hc,hf,hfaith⟩ := hx
  have et : x.representation = timeRep b.data b.inc b.rho := by
    funext q
    rw [ht q,he]
    rfl
  have es := (scalar_factor_contract b.data b.inc b.single b.fiber).2 x.scalar hs
  have ec : x.curves = fun j => realCurve b.data b.inc b.single b.fiber b.rho
      (fun s => canonical b.data b.localDatum b.descent (j,s)) := by
    funext j
    exact observable_curve_unique_from_canonical b.data b.inc b.single b.fiber b.rho _ (x.curves j) (hc j)
  have ef : x.faithful = a.faithful := by rw [hfaith,hf]; rfl
  cases x
  simp_all [differential]

theorem differential_exists_unique : ∃! x : DifferentialData b a, DifferentialSpec b a x :=
  ⟨differential b a,differential_spec b a,differential_unique b a⟩

theorem differential_with_law_conditions (conditions : AllConditions (candidates b a)) :
    ∃! x : DifferentialData b a, DifferentialSpec b a x ∧ AllConditions x.candidate := by
  refine ⟨differential b a,⟨differential_spec b a,conditions⟩,?_⟩
  intro x hx
  exact differential_unique b a x hx.1

theorem differential_same_dynamics :
    (differential b a).embedding = (dynamics b).time.embedding ∧
    (differential b a).representation = (dynamics b).time.representation ∧
    (differential b a).scalar = (dynamics b).trajectory.scalar ∧
    (differential b a).curves = (dynamics b).trajectory.curves.2 := ⟨rfl,rfl,rfl,rfl⟩

theorem typed_law_curve_agrees (j : J) (t : NativeTime (context b)) :
    (curve (context b) j t).val = (differential b a).curves j t := rfl

theorem differential_curve_typed (j : J) (t : NativeTime (context b)) :
    (differential b a).curves j t ∈ canonicalRange b.localDatum b.descent.indexSurj j :=
  (curve (context b) j t).property

end LCTR.CoreLawDifferentialBundle
