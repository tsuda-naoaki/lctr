import CoreConfigurationComparison

namespace LCTR.CorePairInputBridge
open Set LCTR.CoreOperationalConfiguration LCTR.CoreConfigurationComparison
set_option autoImplicit false
universe u v

variable {X : Type u} {Y : Type v} (A : Set X) (B : Set Y)

def CarrierTyped (R : X → Y → Prop) : Prop := ∀ x y, R x y → x ∈ A ∧ y ∈ B

def extend (r : A → B → Prop) (x : X) (y : Y) : Prop :=
  ∃ hx : x ∈ A, ∃ hy : y ∈ B, r ⟨x,hx⟩ ⟨y,hy⟩

def restrict (R : X → Y → Prop) (x : A) (y : B) : Prop := R x.val y.val

theorem joint_input_typed (r : A → B → Prop) : CarrierTyped A B (extend A B r) := by
  rintro x y ⟨hx,hy,_⟩
  exact ⟨hx,hy⟩

theorem joint_input_roundtrip (r : A → B → Prop) (x : A) (y : B) :
    restrict A B (extend A B r) x y ↔ r x y := by
  constructor
  · rintro ⟨hx,hy,h⟩
    exact h
  · intro h
    exact ⟨x.property,y.property,h⟩

theorem restriction_exact (R : X → Y → Prop) (x : X) (y : Y) :
    extend A B (restrict A B R) x y ↔ x ∈ A ∧ y ∈ B ∧ R x y := by
  constructor
  · rintro ⟨hx,hy,h⟩
    exact ⟨hx,hy,h⟩
  · rintro ⟨hx,hy,h⟩
    exact ⟨hx,hy,h⟩

theorem restriction_identity_iff (R : X → Y → Prop) :
    (∀ x y, extend A B (restrict A B R) x y ↔ R x y) ↔ CarrierTyped A B R := by
  constructor
  · intro h x y hr
    exact (joint_input_typed A B (restrict A B R)) x y ((h x y).mpr hr)
  · intro h x y
    rw [restriction_exact]
    exact ⟨fun h => h.2.2, fun hr => ⟨(h x y hr).1,(h x y hr).2,hr⟩⟩

theorem empty_source_image_excludes_joint (r : (∅ : Set X) → B → Prop) (x : X) (y : Y) :
    ¬ extend ∅ B r x y := by
  rintro ⟨hx,_,_⟩
  exact hx

theorem empty_target_image_excludes_joint (r : A → (∅ : Set Y) → Prop) (x : X) (y : Y) :
    ¬ extend A ∅ r x y := by
  rintro ⟨_,hy,_⟩
  exact hy

theorem missing_carrier_control :
    ¬ CarrierTyped ({false} : Set Bool) (Set.univ : Set Unit) (fun _ _ => True) := by
  intro h
  have bad := (h true () trivial).1
  simp at bad

abbrev AmbientPair (x : Configuration) (i : Node x) := (r : Fin 2) → Received x r i
def pairCarrier (x : Configuration) (i : Node x) : Set (AmbientPair x i) :=
  {a | ∀ r, a r ∈ LCTR.CoreSourceMatch.ImageAt (arrival x r) i}

def pairEncoding (x : Configuration) (i : Node x) : PairAt x i ≃ pairCarrier x i where
  toFun a := ⟨fun r => (a r).val,fun r => (a r).property⟩
  invFun a := fun r => ⟨a.val r,a.property r⟩
  left_inv _a := rfl
  right_inv _a := rfl

def nativeJoint (x : Configuration) (d : PairDatum x) (i j : Node x) :=
  extend (pairCarrier x i) (pairCarrier x j)
    (fun a b => d.joint i j ((pairEncoding x i).symm a) ((pairEncoding x j).symm b))

theorem native_joint_carrier (x : Configuration) (d : PairDatum x) (i j : Node x) :
    CarrierTyped (pairCarrier x i) (pairCarrier x j) (nativeJoint x d i j) :=
  joint_input_typed _ _ _

end LCTR.CorePairInputBridge
