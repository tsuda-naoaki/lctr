import CoreJointTime
import CoreJointDescent

namespace LCTR.CoreNativeJointRelation
set_option autoImplicit false
open LCTR.CoreTrajectoryDescent LCTR.CoreObserverTime LCTR.CoreNativeCurves LCTR.CoreJointTime
open LCTR.CoreJointDescent
universe u v w z
variable {C : Type u} {D : Type v} {B : Type w} {I : Type} {V : Type z}

def stateSetoid (f : Family C D B I) (i : I) : Setoid B :=
  Relation.EqvGen.setoid (genB (f.data i).relation (f.data i).binding)
def sourceProjection (f : Family C D B I) : (I → B) → ((i : I) → State (f.data i)) :=
  prodPrj (stateSetoid f)
def sourceSame (f : Family C D B I) (x y : I → B) : Prop :=
  ∀ i, Relation.EqvGen (genB (f.data i).relation (f.data i).binding) (x i) (y i)

theorem source_projection_components (f : Family C D B I) (x : I → B) (i : I) :
    sourceProjection f x i = prj (genB (f.data i).relation (f.data i).binding) (x i) := rfl

theorem source_projection_surjective (f : Family C D B I) : Function.Surjective (sourceProjection f) :=
  prodPrj_surjective (stateSetoid f)

theorem source_projection_kernel (f : Family C D B I) (x y : I → B) :
    sourceSame f x y ↔ sourceProjection f x = sourceProjection f y :=
  prodPrj_kernel (stateSetoid f) x y

theorem native_source_descent (f : Family C D B I)
    (A : Set (I → B)) (S : Set ((I → B) × V)) (sat : Sat (sourceSame f) A S) :
    (∀ x, sourceProjection f x ∈ sourceProjection f '' A ↔ x ∈ A) ∧
    (∀ x a, (sourceProjection f x,a) ∈ relImage (sourceProjection f) S ↔ (x,a) ∈ S) ∧
    ∀ A' S', (∀ x, sourceProjection f x ∈ A' ↔ x ∈ A) →
      (∀ x a, (sourceProjection f x,a) ∈ S' ↔ (x,a) ∈ S) →
      A' = sourceProjection f '' A ∧ S' = relImage (sourceProjection f) S :=
  native_joint_descent (stateSetoid f) A S sat

theorem native_relation_typed (f : Family C D B I)
    (A : Set (I → B)) (S : Set ((I → B) × V)) (typed : ∀ p ∈ S, p.1 ∈ A) :
    ∀ p ∈ relImage (sourceProjection f) S, p.1 ∈ sourceProjection f '' A :=
  quotient_relation_typed (sourceProjection f) A S typed

theorem trajectory_has_source_representative (f : Family C D B I) (base : I) (q : CommonDomain f base) :
    ∃ x : I → B, sourceProjection f x = jointCurve f base q :=
  source_projection_surjective f (jointCurve f base q)

def jointRelation (f : Family C D B I) (base : I) (S : Set ((I → B) × V)) :
    Set (CommonDomain f base × V) :=
  {p | (jointCurve f base p.1,p.2) ∈ relImage (sourceProjection f) S}

theorem joint_source_membership (f : Family C D B I) (base : I)
    (A : Set (I → B)) (S : Set ((I → B) × V)) (sat : Sat (sourceSame f) A S)
    (q : CommonDomain f base) (x : I → B) (same : sourceProjection f x = jointCurve f base q) (v : V) :
    (q,v) ∈ jointRelation f base S ↔ (x,v) ∈ S := by
  change (jointCurve f base q,v) ∈ relImage (sourceProjection f) S ↔ (x,v) ∈ S
  rw [← same]
  exact (native_source_descent f A S sat).2.1 x v

theorem every_trajectory_representative_agrees (f : Family C D B I) (base : I)
    (A : Set (I → B)) (S : Set ((I → B) × V)) (sat : Sat (sourceSame f) A S)
    (q : CommonDomain f base) :
    (∃ x : I → B, sourceProjection f x = jointCurve f base q) ∧
    (∀ x : I → B, sourceProjection f x = jointCurve f base q → ∀ v : V,
      (q,v) ∈ jointRelation f base S ↔ (x,v) ∈ S) :=
  ⟨trajectory_has_source_representative f base q,
    fun x same v => joint_source_membership f base A S sat q x same v⟩

theorem joint_relation_unique (f : Family C D B I) (base : I)
    (S : Set ((I → B) × V)) (candidate : Set (CommonDomain f base × V))
    (membership : ∀ q v, (q,v) ∈ candidate ↔
      (jointCurve f base q,v) ∈ relImage (sourceProjection f) S) :
    candidate = jointRelation f base S := by
  ext p
  exact membership p.1 p.2

end LCTR.CoreNativeJointRelation
