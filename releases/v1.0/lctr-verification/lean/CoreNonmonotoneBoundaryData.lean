import Mathlib.Data.ENNReal.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Data.Set.Finite.Basic

namespace LCTR.CoreNonmonotoneBoundaryData
set_option autoImplicit false
open Set
open scoped ENNReal
variable {Λ K : Type} [Preorder Λ]

noncomputable def envelope (D : Set Λ) (f : Λ → ENNReal) (x : Λ) : ENNReal :=
  sSup (f '' {y | y ∈ D ∧ y ≤ x})
theorem envelope_member_bound (D : Set Λ) (f : Λ → ENNReal) (x y : Λ)
    (hy : y ∈ D) (h : y ≤ x) : f y ≤ envelope D f x :=
  le_sSup ⟨y,⟨hy,h⟩,rfl⟩
theorem envelope_dominates (D : Set Λ) (f : Λ → ENNReal) (x : Λ) (hx : x ∈ D) :
    f x ≤ envelope D f x := envelope_member_bound D f x x hx le_rfl
theorem envelope_monotone (D : Set Λ) (f : Λ → ENNReal) : Monotone (envelope D f) := by
  intro x y hxy
  apply sSup_le
  rintro v ⟨z,⟨hz,hzx⟩,rfl⟩
  exact envelope_member_bound D f y z hz (le_trans hzx hxy)
theorem envelope_least (D : Set Λ) (f : Λ → ENNReal) (x : Λ) (b : ENNReal)
    (h : ∀ y ∈ D, y ≤ x → f y ≤ b) : envelope D f x ≤ b := by
  apply sSup_le
  rintro v ⟨y,⟨hy,hyx⟩,rfl⟩
  exact h y hy hyx
def finiteEnvelope (D : Set Λ) (f : Λ → ENNReal) : Prop :=
  ∀ x ∈ D, envelope D f x < ⊤
theorem finite_envelope_exact (D : Set Λ) (f : Λ → ENNReal) :
    finiteEnvelope D f ↔ ∀ x ∈ D, envelope D f x < ⊤ := Iff.rfl
theorem finite_envelope_defects_finite (D : Set Λ) (f : Λ → ENNReal)
    (h : finiteEnvelope D f) (x : Λ) (hx : x ∈ D) : f x < ⊤ :=
  lt_of_le_of_lt (envelope_dominates D f x hx) (h x hx)
theorem infinite_defect_no_finite_envelope (D : Set Λ) (f : Λ → ENNReal)
    (x : Λ) (hx : x ∈ D) (hi : f x = ⊤) : ¬ finiteEnvelope D f := by
  intro h
  have hf := finite_envelope_defects_finite D f h x hx
  simp [hi] at hf

structure PartitionData (D : Set Λ) (f : Λ → ENNReal) (K : Type) where
  active : Set K
  finite : active.Finite
  region : K → Set Λ
  cover : ∀ x, x ∈ D ↔ ∃ k ∈ active, x ∈ region k
  disjoint : ∀ i ∈ active, ∀ j ∈ active, i ≠ j → Disjoint (region i) (region j)
  convex : ∀ k ∈ active, ∀ a ∈ region k, ∀ c ∈ region k, ∀ b, a ≤ b → b ≤ c → b ∈ region k
  monotone : ∀ k ∈ active, ∀ a ∈ region k, ∀ b ∈ region k, a ≤ b → f a ≤ f b
theorem partition_cover (D : Set Λ) (f : Λ → ENNReal) (p : PartitionData D f K) :
    p.active.Finite ∧ ∀ x, x ∈ D ↔ ∃ k ∈ p.active, x ∈ p.region k := ⟨p.finite,p.cover⟩
theorem partition_unique (D : Set Λ) (f : Λ → ENNReal) (p : PartitionData D f K)
    (x : Λ) (hx : x ∈ D) : ∃! k, k ∈ p.active ∧ x ∈ p.region k := by
  obtain ⟨k,hk,hxk⟩ := (p.cover x).mp hx
  refine ⟨k,⟨hk,hxk⟩,?_⟩
  rintro j ⟨hj,hxj⟩
  by_contra ne
  exact Set.disjoint_left.mp (p.disjoint j hj k hk ne) hxj hxk
theorem partition_order_convex (D : Set Λ) (f : Λ → ENNReal) (p : PartitionData D f K)
    (k : K) (hk : k ∈ p.active) (a b c : Λ)
    (ha : a ∈ p.region k) (hc : c ∈ p.region k) (hab : a ≤ b) (hbc : b ≤ c) :
    b ∈ p.region k := p.convex k hk a ha c hc b hab hbc
theorem partition_monotone (D : Set Λ) (f : Λ → ENNReal) (p : PartitionData D f K)
    (k : K) (hk : k ∈ p.active) (a b : Λ)
    (ha : a ∈ p.region k) (hb : b ∈ p.region k) (hab : a ≤ b) :
    f a ≤ f b := p.monotone k hk a ha b hb hab

inductive Method where
  | envelope | partition | unformed
  deriving DecidableEq
def statedPermission (envelopeGiven partitionGiven : Prop) : Method → Prop
  | .envelope => envelopeGiven
  | .partition => partitionGiven
  | .unformed => ¬ envelopeGiven ∧ ¬ partitionGiven
theorem envelope_method_permission (e p : Prop) (he : e) : statedPermission e p .envelope := he
theorem partition_method_permission (e p : Prop) (hp : p) : statedPermission e p .partition := hp
theorem unformed_when_neither (e p : Prop) (he : ¬ e) (hp : ¬ p) (m : Method) :
    statedPermission e p m ↔ m = .unformed := by
  cases m <;> simp [statedPermission,he,hp]
theorem no_priority_when_both (e p : Prop) (he : e) (hp : p) :
    statedPermission e p .envelope ∧ statedPermission e p .partition := ⟨he,hp⟩

end LCTR.CoreNonmonotoneBoundaryData
