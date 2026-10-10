import Mathlib.Logic.Equiv.Set

namespace LCTR.CoreTaggedLifts
open Set
universe u v w z
set_option autoImplicit false
variable {U : Type u} {A : Type v} {B : Type w} {C : Type z}

def TaggedAt (i : U) (X : Type v) := {p : U × X // p.1 = i}

def untag (i : U) (X : Type v) : TaggedAt i X ≃ X where
  toFun := fun p => p.val.2
  invFun := fun x => ⟨(i,x),rfl⟩
  left_inv := by
    intro p
    apply Subtype.ext
    exact Prod.ext p.property.symm rfl
  right_inv := fun _ => rfl

def tagLift (i j : U) (e : A ≃ B) : TaggedAt i A ≃ TaggedAt j B :=
  ((untag i A).trans e).trans (untag j B).symm

theorem tagLift_value (i j : U) (e : A ≃ B) (p : TaggedAt i A) :
    (tagLift i j e p).val = (j,e p.val.2) := rfl

theorem tagLift_inverse (i j : U) (e : A ≃ B) :
    (tagLift i j e).symm = tagLift j i e.symm := by
  apply Equiv.ext
  intro p
  rfl

theorem tagLift_left_inverse (i j : U) (e : A ≃ B) (p : TaggedAt i A) :
    tagLift j i e.symm (tagLift i j e p) = p := by
  rw [← tagLift_inverse]
  exact (tagLift i j e).symm_apply_apply p

theorem tagLift_right_inverse (i j : U) (e : A ≃ B) (p : TaggedAt j B) :
    tagLift i j e (tagLift j i e.symm p) = p := by
  rw [← tagLift_inverse]
  exact (tagLift i j e).apply_symm_apply p

theorem tagLift_injective (i j : U) (e : A ≃ B) : Function.Injective (tagLift i j e) :=
  (tagLift i j e).injective

theorem tagLift_composition (i j k : U) (e : A ≃ B) (f : B ≃ C) :
    (tagLift i j e).trans (tagLift j k f) = tagLift i k (e.trans f) := by
  apply Equiv.ext
  intro p
  rfl

structure PartialInjection (A : Type v) (B : Type w) where
  domain : Set A
  value : domain → B
  injective : Function.Injective value

noncomputable def imageEquiv (f : PartialInjection A B) : f.domain ≃ range f.value :=
  Equiv.ofInjective f.value f.injective

noncomputable def partialLift (i j : U) (f : PartialInjection A B) :
    TaggedAt i f.domain ≃ TaggedAt j (range f.value) := tagLift i j (imageEquiv f)

theorem partialLift_value (i j : U) (f : PartialInjection A B) (p : TaggedAt i f.domain) :
    (partialLift i j f p).val.1 = j ∧ (partialLift i j f p).val.2.val = f.value p.val.2 :=
  ⟨rfl,rfl⟩

theorem partialLift_inverse_value (i j : U) (f : PartialInjection A B)
    (p : TaggedAt j (range f.value)) :
    ((partialLift i j f).symm p).val = (i,(imageEquiv f).symm p.val.2) := rfl

theorem partialLift_inverse (i j : U) (f : PartialInjection A B) :
    (partialLift i j f).symm = tagLift j i (imageEquiv f).symm :=
  tagLift_inverse i j (imageEquiv f)

theorem partialLift_both_identities (i j : U) (f : PartialInjection A B) :
    (∀ p, tagLift j i (imageEquiv f).symm (partialLift i j f p) = p) ∧
    (∀ p, partialLift i j f (tagLift j i (imageEquiv f).symm p) = p) :=
  ⟨tagLift_left_inverse i j (imageEquiv f),tagLift_right_inverse i j (imageEquiv f)⟩

theorem equal_value_different_tags (i j : U) (different : i ≠ j) (a : A) :
    (i,a) ≠ (j,a) := fun eq => different (congrArg Prod.fst eq)

end LCTR.CoreTaggedLifts
