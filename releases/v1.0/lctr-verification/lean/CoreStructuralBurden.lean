import CoreTokenGraph
import CoreAuditStateTransport
import LCTR.StructuralBurdenSingletonCurrentPaper

namespace LCTR.CoreStructuralBurden
set_option autoImplicit false
open Set LCTR.CoreTokenGraph LCTR.CoreAuditStateTransport
universe u v w z

abbrev burden {A : Type u} {S : Type v} (R : A → A → Prop) (m : A → S) (F : Set A) : Set S :=
  LCTR.StructuralBurdenSingletonCurrentPaper.StructuralBurden R m F

theorem singleton_burden {A : Type u} {S : Type v} (R : A → A → Prop) (m : A → S) (a : A) :
    burden R m {a} = m '' {b | R a b} := by
  ext s
  exact LCTR.StructuralBurdenSingletonCurrentPaper.singleton_structural_burden_membership R m a s

theorem burden_mono {A : Type u} {S : Type v} (R : A → A → Prop) (m : A → S)
    {F G : Set A} (h : F ⊆ G) : burden R m F ⊆ burden R m G := by
  rintro s ⟨a,ha,b,hr,hm⟩
  exact ⟨a,h ha,b,hr,hm⟩

theorem root_burden_subset {A : Type u} {S : Type v} (R : A → A → Prop) (m : A → S)
    {F : Set A} {a : A} (ha : a ∈ F) : burden R m {a} ⊆ burden R m F :=
  burden_mono R m (singleton_subset_iff.mpr ha)

theorem burden_separation {A : Type u} {S : Type v} (R : A → A → Prop) (m : A → S)
    {F G : Set A} {a : A} (ha : a ∈ F) (h : ¬ burden R m {a} ⊆ burden R m G) :
    (burden R m F \ burden R m G).Nonempty := by
  obtain ⟨s,hs,hn⟩ := Set.not_subset.mp h
  exact ⟨s,root_burden_subset R m ha hs,hn⟩

theorem reach_map {A : Type u} {B : Type v} (f : A → B)
    (R : A → A → Prop) (S : B → B → Prop)
    (hf : ∀ x y, R x y → S (f x) (f y)) {x y : A}
    (h : Relation.ReflTransGen R x y) : Relation.ReflTransGen S (f x) (f y) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail (hf _ _ h)

theorem reach_transport {A : Type u} {B : Type v} (c : A ≃ B)
    (E : A → A → Prop) (F : B → B → Prop)
    (he : ∀ a b, E a b ↔ F (c a) (c b)) (a b : A) :
    Relation.ReflTransGen E a b ↔ Relation.ReflTransGen F (c a) (c b) := by
  constructor
  · exact reach_map c E F (fun x y => (he x y).mp)
  · intro h
    have reverse : ∀ x y, F x y → E (c.symm x) (c.symm y) := by
      intro x y hxy
      apply (he _ _).mpr
      simpa only [Equiv.apply_symm_apply] using hxy
    have h' := reach_map c.symm F E reverse h
    simpa only [Equiv.symm_apply_apply] using h'

theorem burden_transport {A : Type u} {B : Type v} {S : Type w} {T : Type z}
    (c : A ≃ B) (d : S ≃ T) (R : A → A → Prop) (Q : B → B → Prop)
    (m : A → S) (n : B → T)
    (order : ∀ a b, R a b ↔ Q (c a) (c b)) (targets : ∀ a, d (m a)=n (c a))
    (F : Set A) : d '' burden R m F = burden Q n (c '' F) := by
  ext t
  constructor
  · rintro ⟨s,⟨a,ha,b,hr,hm⟩,rfl⟩
    refine ⟨c a,⟨a,ha,rfl⟩,c b,(order a b).mp hr,?_⟩
    rw [← targets b,hm]
  · rintro ⟨ca,⟨a,ha,rfl⟩,cb,hr,hm⟩
    obtain ⟨b,rfl⟩ := c.surjective cb
    exact ⟨m b,⟨a,ha,b,(order a b).mpr hr,rfl⟩,(targets b).trans hm⟩

structure StructTok where
  token : Token

def structOf : Token ≃ StructTok where
  toFun := StructTok.mk
  invFun := StructTok.token
  left_inv _ := rfl
  right_inv _ := rfl

abbrev nativeBurden (F : Set Token) : Set StructTok :=
  burden (Relation.ReflTransGen Edge) structOf F

theorem native_root_included {F : Set Token} {a : Token} (ha : a ∈ F) :
    structOf a ∈ nativeBurden F := ⟨a,ha,a,.refl,rfl⟩

theorem native_burden_upward {F : Set Token} {a b : Token}
    (ha : structOf a ∈ nativeBurden F) (hab : Relation.ReflTransGen Edge a b) :
    structOf b ∈ nativeBurden F := by
  rcases ha with ⟨s,hs,t,hst,hta⟩
  have hta' : t=a := structOf.injective hta
  subst t
  exact ⟨s,hs,b,hst.trans hab,rfl⟩

def boundaryBurden (boundary : Option (Set Token)) : Set StructTok :=
  match boundary with
  | none => ∅
  | some F => nativeBurden F

def report (failed : Set Token) (boundary : Option (Set Token)) : Set StructTok × Set StructTok :=
  (nativeBurden failed,boundaryBurden boundary)

theorem report_unique (failed : Set Token) (boundary : Option (Set Token)) :
    ∃! p : Set StructTok × Set StructTok,
      p.1=nativeBurden failed ∧ p.2=boundaryBurden boundary := by
  refine ⟨report failed boundary,⟨rfl,rfl⟩,?_⟩
  intro p hp
  exact Prod.ext hp.1 hp.2

theorem native_burden_covariance (c : Token ≃ Token) (d : StructTok ≃ StructTok)
    (edges : ∀ a b, Edge a b ↔ Edge (c a) (c b)) (targets : ∀ a, d (structOf a)=structOf (c a))
    (F : Set Token) : d '' nativeBurden F = nativeBurden (c '' F) :=
  burden_transport c d _ _ structOf structOf (reach_transport c Edge Edge edges) targets F

theorem native_failed_burden_covariance (c : Token ≃ Token) (d : StructTok ≃ StructTok)
    (edges : ∀ a b, Edge a b ↔ Edge (c a) (c b)) (targets : ∀ a, d (structOf a)=structOf (c a))
    (s t : Token → AuditStatus) (hs : ∀ a, t (c a)=s a) :
    d '' nativeBurden {a | s a=.fail} = nativeBurden {b | t b=.fail} := by
  rw [native_burden_covariance c d edges targets,audit_fiber_image c s t hs .fail]

theorem boundary_burden_covariance (c : Token ≃ Token) (d : StructTok ≃ StructTok)
    (edges : ∀ a b, Edge a b ↔ Edge (c a) (c b)) (targets : ∀ a, d (structOf a)=structOf (c a))
    (boundary : Option (Set Token)) :
    d '' boundaryBurden boundary = boundaryBurden (boundary.map (fun F => c '' F)) := by
  cases boundary with
  | none => exact Set.image_empty _
  | some F => exact native_burden_covariance c d edges targets F

end LCTR.CoreStructuralBurden
