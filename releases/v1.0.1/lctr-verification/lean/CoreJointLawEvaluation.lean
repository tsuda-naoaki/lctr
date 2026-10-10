import CoreNativeJointRelation
import CoreNativeLawFailure

namespace LCTR.CoreJointLawEvaluation
set_option autoImplicit false
open LCTR.CoreObserverTime LCTR.CoreNativeCurves LCTR.CoreRepresentationImages
open LCTR.CoreJointTime LCTR.CoreNativeJointRelation
open LCTR.LawTimeTransport LCTR.LawFamilyTransport
variable {C D B I R A : Type}

structure Context (C D B I R : Type) where
  objects : CoreJointTime.Family C D B I
  base : I
  rho : RealEmbedding (objects.data base) (objects.inc base)
  obsIndex : I → Type
  obsValue : (Sigma obsIndex) → Type
  observable : (o : Sigma obsIndex) → State (objects.data o.1) → obsValue o
  relValue : R → Type
  sourceRelation : (r : R) → Set ((I → B) × relValue r)

variable (c : Context C D B I R)
def realValue (q : CommonDomain c.objects c.base) : ℝ := c.rho.value q.val
abbrev RealTime := Set.range (realValue c)
def realProjection : CommonDomain c.objects c.base → RealTime c := imageProjection (realValue c)
noncomputable def orderInverse : RealTime c → CommonDomain c.objects c.base :=
  LCTR.ImageInverseConstruction.inverse (realValue c)

theorem real_value_injective : Function.Injective (realValue c) := by
  intro x y h
  exact Subtype.ext (embedding_injective _ _ c.rho h)

theorem real_projection_bijective : Function.Bijective (realProjection c) := by
  refine ⟨?_,imageProjection_surjective _⟩
  intro x y h
  exact real_value_injective c (congrArg (fun t : RealTime c => t.val) h)

theorem inverse_on_projection (q : CommonDomain c.objects c.base) :
    orderInverse c (realProjection c q) = q :=
  LCTR.ImageInverseConstruction.inverse_left _ (real_value_injective c) q

def realRelation (r : R) : Set (RealTime c × c.relValue r) :=
  {p | (orderInverse c p.1,p.2) ∈ jointRelation c.objects c.base (c.sourceRelation r)}
abbrev RelationDomain (r : R) := {t : RealTime c // ∃ v, (t,v) ∈ realRelation c r}

structure Observation where
  value : (r : R) → RelationDomain c r → c.relValue r
  belongs : ∀ r t, (t.val,value r t) ∈ realRelation c r

noncomputable def observableValue (o : Sigma c.obsIndex) (t : RealTime c) : c.obsValue o :=
  c.observable o (jointCurve c.objects c.base (orderInverse c t) o.1)

structure Selection where
  obsIndices : Fin 2 → Set (Sigma c.obsIndex)
  relIndices : Fin 2 → Set R
  evalTimes : Set (RealTime c)
  relationDefined : ∀ s (r : relIndices s) t, t ∈ evalTimes → ∃ v, (t,v) ∈ realRelation c r.val

abbrev SideSpace (s : Selection c) (side : Fin 2) :=
  ((o : s.obsIndices side) → c.obsValue o.val) × ((r : s.relIndices side) → c.relValue r.val)

noncomputable def sideValue (obs : Observation c) (s : Selection c) (side : Fin 2)
    (t : s.evalTimes) : SideSpace c s side :=
  (fun o => observableValue c o.val t.val,
   fun r => obs.value r.val ⟨t.val,s.relationDefined side r t.val t.property⟩)

structure ComponentInput where
  selectors : Selection c
  evalDomain : Set (RealTime c × SideSpace c selectors 0)
  candidate : Set ((RealTime c × SideSpace c selectors 0) × SideSpace c selectors 1)
  candidateTyped : ∀ p ∈ candidate, p.1 ∈ evalDomain

noncomputable def component (obs : Observation c) (a : ComponentInput c) :
    Component (RealTime c) (SideSpace c a.selectors 0) (SideSpace c a.selectors 1) where
  evalTime t := t ∈ a.selectors.evalTimes
  input := sideValue c obs a.selectors 0
  output := sideValue c obs a.selectors 1
  evalDomain t x := (t,x) ∈ a.evalDomain
  relation t x y := ((t,x),y) ∈ a.candidate
  relationTyped t x y h := a.candidateTyped ((t,x),y) h

theorem individual_observable_component (obs : Observation c) (s : Selection c)
    (side : Fin 2) (t : s.evalTimes) (o : s.obsIndices side) :
    (sideValue c obs s side t).1 o =
      c.observable o.val (jointCurve c.objects c.base (orderInverse c t.val) o.val.1) := rfl

theorem joint_relation_component_valid (obs : Observation c) (s : Selection c)
    (side : Fin 2) (t : s.evalTimes) (r : s.relIndices side) :
    (t.val,(sideValue c obs s side t).2 r) ∈ realRelation c r.val :=
  obs.belongs r.val ⟨t.val,s.relationDefined side r t.val t.property⟩

theorem joint_relation_source_valid (obs : Observation c) (s : Selection c)
    (side : Fin 2) (t : s.evalTimes) (r : s.relIndices side)
    (domain : Set (I → B))
    (sat : CoreJointDescent.Sat (sourceSame c.objects) domain (c.sourceRelation r.val))
    (x : I → B) (hx : sourceProjection c.objects x = jointCurve c.objects c.base (orderInverse c t.val)) :
    (x,(sideValue c obs s side t).2 r) ∈ c.sourceRelation r.val :=
  (joint_source_membership c.objects c.base domain (c.sourceRelation r.val) sat
    (orderInverse c t.val) x hx _).mp (joint_relation_component_valid c obs s side t r)

theorem tuple_components (obs : Observation c) (a : ComponentInput c) (t : a.selectors.evalTimes) :
    evalTuple (component c obs a) t =
      ((t.val,sideValue c obs a.selectors 0 t),sideValue c obs a.selectors 1 t) := rfl

structure FamilyInput where
  nonempty : Nonempty A
  law : A → ComponentInput c
  allowed : (RealTime c → Prop) → Prop
  faithful : ((j : A) → Reindex
    (Tuple (RealTime c) (SideSpace c (law j).selectors 0) (SideSpace c (law j).selectors 1))
    (Tuple (RealTime c) (SideSpace c (law j).selectors 0) (SideSpace c (law j).selectors 1))) → Prop

variable (obs : Observation c) (f : FamilyInput (A := A) c)
noncomputable def family : LawFamilyTransport.Family (RealTime c) A
    (fun j => SideSpace c (f.law j).selectors 0) (fun j => SideSpace c (f.law j).selectors 1) where
  indicesNonempty := f.nonempty
  component j := component c obs (f.law j)
  admissibleCommon := f.allowed
  faithful := f.faithful

theorem five_condition_connection :
    CoreLawConditionGraph.condition (family c obs f) 0 = K1 (family c obs f) ∧
    CoreLawConditionGraph.condition (family c obs f) 1 = K2 (family c obs f) ∧
    CoreLawConditionGraph.condition (family c obs f) 2 = K3 (family c obs f) ∧
    CoreLawConditionGraph.condition (family c obs f) 3 = K4 (family c obs f) ∧
    CoreLawConditionGraph.condition (family c obs f) 4 = K5 (family c obs f) :=
  CoreLawConditionGraph.condition_vector_exact (family c obs f)

theorem common_valid_joint_tuples (h : AllConditions (family c obs f)) :
    (∃ t, common (family c obs f) t) ∧ f.allowed (common (family c obs f)) ∧
    ∀ t, common (family c obs f) t → ∀ j,
      ∃ ht : t ∈ (f.law j).selectors.evalTimes,
        evalTuple (component c obs (f.law j)) ⟨t,ht⟩ ∈ (f.law j).candidate :=
  ⟨h.2.2.2.2.2.1,h.2.2.2.2.2.2,fun _ ht j => ht j⟩

noncomputable def selected : CoreNativeLawFailure.Selection (E := Unit)
    (T := RealTime c) (A := A)
    (X := fun j => SideSpace c (f.law j).selectors 0)
    (Y := fun j => SideSpace c (f.law j).selectors 1) where
  domain _ := True
  datum _ := family c obs f

theorem joint_failure_exact :
    CoreNativeLawFailure.failure (selected c obs f) () ↔ ¬ AllConditions (family c obs f) :=
  CoreNativeLawFailure.failure_on_selected_datum (selected c obs f) () trivial

theorem joint_minimal_failure_cover :
    ¬ AllConditions (family c obs f) ↔
      ∃ i, CoreNativeLawFailure.minimalClass (selected c obs f) () i :=
  (joint_failure_exact c obs f).symm.trans
    (CoreNativeLawFailure.failure_covered_by_minimal_classes (selected c obs f) ())

end LCTR.CoreJointLawEvaluation
