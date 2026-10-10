import CoreSourceLoops
import Mathlib.Logic.Equiv.Set

namespace LCTR.CoreQuotientInterface
open Set
universe u v w
set_option autoImplicit false
variable {A : Type u} {B : Type v}

def eqClass (s : Setoid A) (a : A) : Set A := {b | s.r a b}
abbrev ClassQuotient (s : Setoid A) := range (eqClass s)
def classProjection (s : Setoid A) (a : A) : ClassQuotient s := ⟨eqClass s a,⟨a,rfl⟩⟩

theorem class_kernel (s : Setoid A) (a b : A) : eqClass s a = eqClass s b ↔ s.r a b := by
  constructor
  · intro eq
    have self : b ∈ eqClass s b := s.refl b
    change b ∈ eqClass s a
    rw [eq]
    exact self
  · intro same
    ext x
    exact ⟨fun h => s.trans (s.symm same) h,fun h => s.trans same h⟩

theorem class_projection_kernel (s : Setoid A) (a b : A) :
    classProjection s a = classProjection s b ↔ s.r a b := by
  constructor
  · exact fun h => (class_kernel s a b).mp (congrArg Subtype.val h)
  · exact fun h => Subtype.ext ((class_kernel s a b).mpr h)

theorem class_projection_surjective (s : Setoid A) : Function.Surjective (classProjection s) := by
  rintro ⟨_,a,rfl⟩
  exact ⟨a,rfl⟩

noncomputable def classToNative (s : Setoid A) (c : ClassQuotient s) : Quotient s :=
  Quotient.mk s c.property.choose

theorem class_native_commutes (s : Setoid A) (a : A) :
    classToNative s (classProjection s a) = Quotient.mk s a := by
  apply Quotient.sound
  exact (class_kernel s _ a).mp (classProjection s a).property.choose_spec

theorem class_native_bijective (s : Setoid A) : Function.Bijective (classToNative s) := by
  constructor
  · intro c d h
    obtain ⟨a,rfl⟩ := class_projection_surjective s c
    obtain ⟨b,rfl⟩ := class_projection_surjective s d
    rw [class_native_commutes,class_native_commutes] at h
    exact (class_projection_kernel s a b).mpr (Quotient.exact h)
  · intro q
    obtain ⟨a,rfl⟩ := Quotient.mk_surjective q
    exact ⟨classProjection s a,class_native_commutes s a⟩

theorem class_native_unique (s : Setoid A) (f : ClassQuotient s → Quotient s)
    (h : ∀ a, f (classProjection s a) = Quotient.mk s a) : f = classToNative s := by
  funext c
  obtain ⟨a,rfl⟩ := class_projection_surjective s c
  exact (h a).trans (class_native_commutes s a).symm

def Saturated (E : A → A → Prop) (P : Set A) : Prop :=
  ∀ a b, E a b → (a ∈ P ↔ b ∈ P)

theorem image_pullback (E : A → A → Prop) (p : A → B)
    (kernel : ∀ a b, p a = p b ↔ E a b) (P : Set A) (sat : Saturated E P) (a : A) :
    p a ∈ p '' P ↔ a ∈ P := by
  constructor
  · rintro ⟨b,hb,eq⟩
    exact (sat b a ((kernel b a).mp eq)).mp hb
  · exact fun ha => ⟨a,ha,rfl⟩

theorem image_least (p : A → B) (P : Set A) (T : Set B)
    (contains : ∀ a ∈ P, p a ∈ T) : p '' P ⊆ T := by
  rintro _ ⟨a,ha,rfl⟩
  exact contains a ha

theorem image_unique_least (p : A → B) (P : Set A) :
    ∃! T : Set B, (∀ a ∈ P, p a ∈ T) ∧
      (∀ R : Set B, (∀ a ∈ P, p a ∈ R) → T ⊆ R) := by
  refine ⟨p '' P,⟨fun a ha => ⟨a,ha,rfl⟩,image_least p P⟩,?_⟩
  intro T h
  exact Set.Subset.antisymm (h.2 _ (fun a ha => ⟨a,ha,rfl⟩)) (image_least p P T h.1)

theorem exact_pullback_requires_saturation (E : A → A → Prop) (p : A → B)
    (kernel : ∀ a b, p a = p b ↔ E a b) (P : Set A) (T : Set B)
    (pullback : ∀ a, p a ∈ T ↔ a ∈ P) : Saturated E P := by
  intro a b same
  rw [← pullback a,← pullback b,(kernel a b).mpr same]

theorem native_comparison_projection {U : Type u} {S : Type v} {V : U → Type w}
    (d : LCTR.CoreSourceLoops.Data U S V) :
    Function.Surjective (Quotient.mk (LCTR.CoreTypedWords.orbitSetoid (LCTR.CoreSourceLoops.system d))) ∧
    (∀ a b, Quotient.mk (LCTR.CoreTypedWords.orbitSetoid (LCTR.CoreSourceLoops.system d)) a =
      Quotient.mk (LCTR.CoreTypedWords.orbitSetoid (LCTR.CoreSourceLoops.system d)) b ↔
      LCTR.CoreTypedWords.Orbit (LCTR.CoreSourceLoops.system d) a b) :=
  ⟨Quotient.mk_surjective,fun a b => ⟨Quotient.exact,
    fun h => @Quotient.sound _ (LCTR.CoreTypedWords.orbitSetoid
      (LCTR.CoreSourceLoops.system d)) a b h⟩⟩

theorem empty_class_quotient (s : Setoid Empty) : IsEmpty (ClassQuotient s) := by
  constructor
  rintro ⟨_,a,_⟩
  exact Empty.elim a

end LCTR.CoreQuotientInterface
