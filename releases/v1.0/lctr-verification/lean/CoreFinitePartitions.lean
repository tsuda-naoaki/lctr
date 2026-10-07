import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Nat.Find

namespace LCTR.CoreFinitePartitions
set_option autoImplicit false
universe u v w z

noncomputable def taggedEquiv {T : Type u} {I : T → Type v} {A : T → Type w}
    (f : (t : T) → I t → A t) (inj : ∀ t, Function.Injective (f t)) :
    ((t : T) × I t) ≃ ((t : T) × Set.range (f t)) :=
  Equiv.sigmaCongrRight fun t => Equiv.ofInjective (f t) (inj t)

theorem tagged_finite {T : Type u} [Finite T] {I : T → Type v} [∀ t, Finite (I t)]
    {A : T → Type w} (f : (t : T) → I t → A t) (inj : ∀ t, Function.Injective (f t)) :
    Finite ((t : T) × Set.range (f t)) := by
  let : Fintype T := Fintype.ofFinite T
  let : (t : T) → Fintype (I t) := fun t => Fintype.ofFinite (I t)
  exact Finite.of_equiv _ (taggedEquiv f inj)

theorem tagged_card {T : Type u} [Fintype T] {I : T → Type v}
    [∀ t, Fintype (I t)] {A : T → Type w}
    (f : (t : T) → I t → A t) (inj : ∀ t, Function.Injective (f t)) :
    Nat.card ((t : T) × Set.range (f t)) = ∑ t, Fintype.card (I t) := by
  calc
    Nat.card ((t : T) × Set.range (f t)) = Nat.card ((t : T) × I t) :=
      Nat.card_congr (taggedEquiv f inj).symm
    _ = ∑ t, Fintype.card (I t) := by rw [Nat.card_eq_fintype_card, Fintype.card_sigma]

theorem tagged_partition {T : Type u} {I : T → Type v} [∀ t, Nonempty (I t)]
    {A : T → Type w} (f : (t : T) → I t → A t) :
    (∀ x : (t : T) × Set.range (f t), ∃! t : T, x.1 = t) ∧
    (∀ t : T, ∃ x : (s : T) × Set.range (f s), x.1 = t) := by
  constructor
  · intro x
    exact ⟨x.1, rfl, fun _ h => h.symm⟩
  · intro t
    obtain ⟨i⟩ := (inferInstance : Nonempty (I t))
    exact ⟨⟨t, ⟨f t i, i, rfl⟩⟩, rfl⟩

def graphEquiv {Q : Type u} (P : Q → Type v) (K : (q : Q) → P q) :
    Q ≃ {p : (q : Q) × P q // p.2 = K p.1} where
  toFun q := ⟨⟨q,K q⟩,rfl⟩
  invFun p := p.val.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨q,p⟩,h⟩
    apply Subtype.ext
    change Sigma.mk q (K q) = Sigma.mk q p
    congr 1
    exact h.symm

noncomputable def taggedClassification {T : Type u} {I : T → Type v} {A : T → Type w}
    (f : (t : T) → I t → A t) (inj : ∀ t, Function.Injective (f t))
    (P : ((t : T) × I t) → Type z) (K : (q : (t : T) × I t) → P q) :
    ((t : T) × Set.range (f t)) ≃ {p : (q : (t : T) × I t) × P q // p.2 = K p.1} :=
  (taggedEquiv f inj).symm.trans (graphEquiv P K)

theorem classification_on_generator {T : Type u} {I : T → Type v} {A : T → Type w}
    (f : (t : T) → I t → A t) (inj : ∀ t, Function.Injective (f t))
    (P : ((t : T) × I t) → Type z) (K : (q : (t : T) × I t) → P q)
    (t : T) (i : I t) :
    taggedClassification f inj P K ⟨t,⟨f t i,i,rfl⟩⟩ = ⟨⟨⟨t,i⟩,K ⟨t,i⟩⟩,rfl⟩ := by
  change graphEquiv P K ((taggedEquiv f inj).symm ⟨t,⟨f t i,i,rfl⟩⟩) = _
  have h : (taggedEquiv f inj) ⟨t,i⟩ = ⟨t,⟨f t i,i,rfl⟩⟩ := rfl
  rw [← h, Equiv.symm_apply_apply]
  rfl

theorem classification_bijective {T : Type u} {I : T → Type v} {A : T → Type w}
    (f : (t : T) → I t → A t) (inj : ∀ t, Function.Injective (f t))
    (P : ((t : T) × I t) → Type z) (K : (q : (t : T) × I t) → P q) :
    Function.Bijective (taggedClassification f inj P K) := (taggedClassification f inj P K).bijective

 
def First (n : Nat) (K : Nat → Prop) (i : Nat) : Prop :=
  1 ≤ i ∧ i ≤ n ∧ ¬ K i ∧ ∀ j, 1 ≤ j → j < i → K j

theorem first_failure_unique (n : Nat) (K : Nat → Prop)
    (fails : ¬ ∀ i, 1 ≤ i → i ≤ n → K i) : ∃! i, First n K i := by
  classical
  have ex : ∃ i, 1 ≤ i ∧ i ≤ n ∧ ¬ K i := by
    by_contra h
    apply fails
    intro i hi hn
    by_contra hk
    exact h ⟨i,hi,hn,hk⟩
  let i := Nat.find ex
  have hi := Nat.find_spec ex
  have fi : First n K i := by
    refine ⟨hi.1,hi.2.1,hi.2.2,?_⟩
    intro j hj ji
    by_contra hk
    exact Nat.find_min ex ji ⟨hj, Nat.le_trans (Nat.le_of_lt ji) hi.2.1, hk⟩
  refine ⟨i,fi,?_⟩
  intro k fk
  have ik : i ≤ k := Nat.find_min' ex ⟨fk.1,fk.2.1,fk.2.2.1⟩
  by_contra ne
  have lt : i < k := Nat.lt_of_le_of_ne ik (Ne.symm ne)
  exact fi.2.2.1 (fk.2.2.2 i fi.1 lt)

theorem first_failure_partition (n : Nat) (K : Nat → Prop) :
    (¬ ∀ i, 1 ≤ i → i ≤ n → K i) ↔ ∃! i, First n K i := by
  constructor
  · exact first_failure_unique n K
  · rintro ⟨i,h,_⟩ all
    exact h.2.2.1 (all i h.1 h.2.1)

theorem first_failure_sets {Y : Type u} (n : Nat) (K : Nat → Y → Prop) :
    {y | ¬ ∀ i, 1 ≤ i → i ≤ n → K i y} =
      ⋃ i : Nat, {y | First n (fun j => K j y) i} := by
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · intro h
    exact (first_failure_unique n (fun j => K j y) h).exists
  · rintro ⟨i,h⟩ all
    exact h.2.2.1 (all i h.1 h.2.1)

theorem first_failure_components_disjoint (n : Nat) (K : Nat → Prop)
    {i j : Nat} (hi : First n K i) (hj : First n K j) : i = j := by
  rcases lt_trichotomy i j with lt | eq | gt
  · exact False.elim (hi.2.2.1 (hj.2.2.2 i hi.1 lt))
  · exact eq
  · exact False.elim (hj.2.2.1 (hi.2.2.2 j hj.1 gt))

theorem bounded_extensionality (n : Nat) (K L : Nat → Prop)
    (agree : ∀ j, 1 ≤ j → j ≤ n → (K j ↔ L j)) (i : Nat) :
    First n K i ↔ First n L i := by
  have forward : ∀ (K L : Nat → Prop),
      (∀ j, 1 ≤ j → j ≤ n → (K j ↔ L j)) → First n K i → First n L i := by
    intro K L a h
    refine ⟨h.1,h.2.1,fun bad => h.2.2.1 ((a i h.1 h.2.1).mpr bad),?_⟩
    intro j hj ji
    exact (a j hj (Nat.le_trans (Nat.le_of_lt ji) h.2.1)).mp (h.2.2.2 j hj ji)
  exact ⟨forward K L agree, forward L K (fun j hj hn => (agree j hj hn).symm)⟩

theorem empty_sequence (K : Nat → Prop) : ¬ ∃ i, First 0 K i := by
  rintro ⟨i,h⟩
  have h1:=h.1
  have h2:=h.2.1
  omega

theorem minimum_index (n : Nat) (K : Nat → Prop) {i : Nat} (h : First n K i) :
    ∀ j, 1 ≤ j → j ≤ n → ¬ K j → i ≤ j := by
  intro j hj _ nf
  by_contra hle
  exact nf (h.2.2.2 j hj (Nat.lt_of_not_ge hle))

def WithoutPrefix (n : Nat) (K : Nat → Prop) (i : Nat) : Prop :=
  1 ≤ i ∧ i ≤ n ∧ ¬ K i

theorem omitted_prefix_not_unique :
    ∃ i j : Nat, i ≠ j ∧ WithoutPrefix 2 (fun _ => False) i ∧
      WithoutPrefix 2 (fun _ => False) j := by
  exact ⟨1,2,by decide,by simp [WithoutPrefix],by simp [WithoutPrefix]⟩

theorem injection_is_necessary :
    ¬ ∃ g : Unit → Bool, ∀ b : Bool, g () = b := by
  rintro ⟨g,h⟩
  have bad := (h false).symm.trans (h true)
  cases bad

#print axioms tagged_card
#print axioms tagged_finite
#print axioms tagged_partition
#print axioms classification_on_generator
#print axioms classification_bijective
#print axioms first_failure_unique
#print axioms first_failure_partition
#print axioms first_failure_sets
#print axioms first_failure_components_disjoint
#print axioms bounded_extensionality
#print axioms empty_sequence
#print axioms minimum_index
#print axioms omitted_prefix_not_unique
#print axioms injection_is_necessary
end LCTR.CoreFinitePartitions
