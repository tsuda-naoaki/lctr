import Mathlib.Data.Set.Prod
import Mathlib.Data.Quot

namespace LCTR.CoreJointDescent
set_option autoImplicit false
open Set
universe u v w z
variable {X : Type u} {Q : Type v} {V : Type w}

def Sat (same : X → X → Prop) (A : Set X) (S : Set (X × V)) : Prop :=
  ∀ x y, same x y → (x ∈ A ↔ y ∈ A) ∧ ∀ a, (x,a) ∈ S ↔ (y,a) ∈ S
def relImage (q : X → Q) (S : Set (X × V)) : Set (Q × V) :=
  (fun p => (q p.1,p.2)) '' S

theorem domain_criterion (q : X → Q) (same : X → X → Prop)
    (A : Set X) (S : Set (X × V))
    (kernel : ∀ x y, same x y ↔ q x = q y) (sat : Sat same A S) (x : X) :
    q x ∈ q '' A ↔ x ∈ A := by
  constructor
  · rintro ⟨y,hy,hq⟩
    exact (sat y x ((kernel y x).mpr hq)).1.mp hy
  · exact fun h => ⟨x,h,rfl⟩

theorem relation_criterion (q : X → Q) (same : X → X → Prop)
    (A : Set X) (S : Set (X × V))
    (kernel : ∀ x y, same x y ↔ q x = q y) (sat : Sat same A S) (x : X) (a : V) :
    (q x,a) ∈ relImage q S ↔ (x,a) ∈ S := by
  constructor
  · rintro ⟨⟨y,b⟩,hs,hq⟩
    have h := Prod.mk.inj hq
    dsimp at h
    rcases h with ⟨hy,hb⟩
    subst b
    exact (sat y x ((kernel y x).mpr hy)).2 a |>.mp hs
  · exact fun h => ⟨(x,a),h,rfl⟩

theorem quotient_relation_typed (q : X → Q) (A : Set X) (S : Set (X × V))
    (typed : ∀ p ∈ S, p.1 ∈ A) :
    ∀ p ∈ relImage q S, p.1 ∈ q '' A := by
  rintro p ⟨x,hx,rfl⟩
  exact ⟨x.1,typed x hx,rfl⟩

theorem quotient_pair_unique (q : X → Q) (onto : Function.Surjective q)
    (A₀ A₁ : Set Q) (S₀ S₁ : Set (Q × V))
    (dom : ∀ x, q x ∈ A₀ ↔ q x ∈ A₁)
    (rel : ∀ x a, (q x,a) ∈ S₀ ↔ (q x,a) ∈ S₁) : A₀ = A₁ ∧ S₀ = S₁ := by
  constructor
  · ext y
    obtain ⟨x,rfl⟩ := onto y
    exact dom x
  · ext ⟨y,a⟩
    obtain ⟨x,rfl⟩ := onto y
    exact rel x a

variable {I : Type z} {Xi : I → Type u}
def prodPrj (s : ∀ i, Setoid (Xi i)) (x : ∀ i, Xi i) : ∀ i, Quotient (s i) :=
  fun i => Quotient.mk (s i) (x i)

theorem prodPrj_surjective (s : ∀ i, Setoid (Xi i)) : Function.Surjective (prodPrj s) := by
  intro y
  classical
  have h : ∀ i, ∃ x : Xi i, Quotient.mk (s i) x = y i := fun i => Quotient.mk_surjective (y i)
  exact ⟨fun i => Classical.choose (h i),funext (fun i => Classical.choose_spec (h i))⟩

theorem prodPrj_kernel (s : ∀ i, Setoid (Xi i)) (x y : ∀ i, Xi i) :
    (∀ i, (s i).r (x i) (y i)) ↔ prodPrj s x = prodPrj s y := by
  constructor
  · intro h
    exact funext (fun i => Quotient.sound (h i))
  · intro h i
    exact Quotient.exact (congrFun h i)

theorem native_joint_descent (s : ∀ i, Setoid (Xi i))
    (A : Set (∀ i, Xi i)) (S : Set ((∀ i, Xi i) × V))
    (sat : Sat (fun x y => ∀ i, (s i).r (x i) (y i)) A S) :
    (∀ x, prodPrj s x ∈ prodPrj s '' A ↔ x ∈ A) ∧
    (∀ x a, (prodPrj s x,a) ∈ relImage (prodPrj s) S ↔ (x,a) ∈ S) ∧
    ∀ A' S', (∀ x, prodPrj s x ∈ A' ↔ x ∈ A) →
      (∀ x a, (prodPrj s x,a) ∈ S' ↔ (x,a) ∈ S) →
      A' = prodPrj s '' A ∧ S' = relImage (prodPrj s) S := by
  have hd := domain_criterion (prodPrj s) _ A S (prodPrj_kernel s) sat
  have hr := relation_criterion (prodPrj s) _ A S (prodPrj_kernel s) sat
  refine ⟨hd,hr,?_⟩
  intro A' S' hA hS
  exact quotient_pair_unique (prodPrj s) (prodPrj_surjective s) _ _ _ _
    (fun x => (hA x).trans (hd x).symm) (fun x a => (hS x a).trans (hr x a).symm)

theorem missing_domain_saturation_control :
    relImage (fun (_ : Bool) => ()) (∅ : Set (Bool × Unit)) = ∅ ∧
    (fun (_ : Bool) => ()) false ∈ (fun (_ : Bool) => ()) '' ({true} : Set Bool) ∧
    false ∉ ({true} : Set Bool) := by
  simp [relImage]

theorem missing_surjectivity_control :
    (∀ x : Unit, (fun _ : Unit => false) x ∈ (∅ : Set Bool) ↔
      (fun _ : Unit => false) x ∈ ({true} : Set Bool)) ∧ (∅ : Set Bool) ≠ {true} := by
  simp

theorem empty_domain_control (q : X → Q) :
    q '' (∅ : Set X) = ∅ ∧ relImage q (∅ : Set (X × V)) = ∅ := by
  simp [relImage]
end LCTR.CoreJointDescent
