import CoreAuditStateTransport
import Mathlib.Logic.Equiv.Set

namespace LCTR.CoreAuditTags
set_option autoImplicit false
open Set LCTR.CoreAuditStateTransport
universe u v w z

abbrev UndefinedStatus := {q : AuditStatus // q=.blocked ∨ q=.unformed ∨ q=.indeterminate}
abbrev Reason (A : Type u) := A × UndefinedStatus

def reasons {A : Type u} (s : A → AuditStatus) : Set (Reason A) :=
  {p | s p.1=p.2.val}

def groupReasons {A : Type u} (s : A → AuditStatus) (G : Set A) : Set (Reason A) :=
  {p | p.1 ∈ G ∧ s p.1=p.2.val}

def reasonEquiv {A : Type u} {B : Type v} (c : A ≃ B) : Reason A ≃ Reason B :=
  c.prodCongr (Equiv.refl _)

theorem reasons_transport {A : Type u} {B : Type v} (c : A ≃ B)
    (s : A → AuditStatus) (t : B → AuditStatus) (hs : ∀ a, t (c a)=s a) :
    reasonEquiv c '' reasons s = reasons t := by
  ext p
  constructor
  · rintro ⟨⟨a,q⟩,ha,rfl⟩
    exact (hs a).trans ha
  · intro hp
    refine ⟨(c.symm p.1,p.2),?_,?_⟩
    · change s (c.symm p.1)=p.2.val
      rw [← hs,Equiv.apply_symm_apply]
      exact hp
    · exact Prod.ext (c.apply_symm_apply p.1) rfl

theorem group_reasons_transport {A : Type u} {B : Type v} (c : A ≃ B)
    (s : A → AuditStatus) (t : B → AuditStatus) (hs : ∀ a, t (c a)=s a) (G : Set A) :
    reasonEquiv c '' groupReasons s G = groupReasons t (c '' G) := by
  ext p
  constructor
  · rintro ⟨⟨a,q⟩,⟨ha,hq⟩,rfl⟩
    exact ⟨⟨a,ha,rfl⟩,(hs a).trans hq⟩
  · rintro ⟨⟨a,ha,he⟩,hq⟩
    refine ⟨(a,p.2),⟨ha,?_⟩,Prod.ext he rfl⟩
    exact (hs a).symm.trans (he.symm ▸ hq)

abbrev NonemptySet (A : Type u) := {R : Set A // R.Nonempty}

def nonemptySetEquiv {A : Type u} {B : Type v} (e : A ≃ B) : NonemptySet A ≃ NonemptySet B where
  toFun R := ⟨e '' R.val,Set.image_nonempty.mpr R.property⟩
  invFun R := ⟨e.symm '' R.val,Set.image_nonempty.mpr R.property⟩
  left_inv R := Subtype.ext (e.symm_image_image R.val)
  right_inv R := Subtype.ext (e.symm.symm_image_image R.val)

abbrev Tagged (Y : Type u) (A : Type v) := Y ⊕ NonemptySet (Reason A)

noncomputable def tagged {Y : Type u} {A : Type v} (y : Y) (R : Set (Reason A)) : Tagged Y A := by
  classical
  exact if h : R=∅ then .inl y else .inr ⟨R,Set.nonempty_iff_ne_empty.mpr h⟩

def taggedEquiv {Y : Type u} {Z : Type v} {A : Type w} {B : Type z}
    (values : Y ≃ Z) (tokens : A ≃ B) : Tagged Y A ≃ Tagged Z B :=
  values.sumCongr (nonemptySetEquiv (reasonEquiv tokens))

theorem tagged_transport {Y : Type u} {Z : Type v} {A : Type w} {B : Type z}
    (values : Y ≃ Z) (tokens : A ≃ B) (y : Y) (R : Set (Reason A)) :
    taggedEquiv values tokens (tagged y R) = tagged (values y) (reasonEquiv tokens '' R) := by
  classical
  by_cases h : R=∅
  · subst R
    simp [tagged,taggedEquiv]
  · have hi : reasonEquiv tokens '' R ≠ ∅ := by
      intro empty
      exact h (Set.image_eq_empty.mp empty)
    simp only [tagged,dif_neg h,dif_neg hi]
    rfl

theorem generated_tagged_transport {Y : Type u} {Z : Type v} {A : Type w} {B : Type z}
    (values : Y ≃ Z) (tokens : A ≃ B) (y : Y) (z : Z) (hy : values y=z)
    (s : A → AuditStatus) (t : B → AuditStatus) (hs : ∀ a, t (tokens a)=s a) :
    taggedEquiv values tokens (tagged y (reasons s)) = tagged z (reasons t) := by
  rw [tagged_transport,hy,reasons_transport tokens s t hs]

theorem nonempty_reasons_hide_payload {Y : Type u} {A : Type v}
    (y z : Y) (R : Set (Reason A)) (h : R.Nonempty) : tagged y R = tagged z R := by
  classical
  simp only [tagged,dif_neg h.ne_empty]

theorem empty_reasons_preserve_payload {Y : Type u} {A : Type v} (y : Y) :
    tagged y (∅ : Set (Reason A)) = .inl y := by
  classical
  simp [tagged]

theorem no_empty_reason_tag {A : Type u} (R : NonemptySet (Reason A)) : R.val ≠ ∅ :=
  R.property.ne_empty

end LCTR.CoreAuditTags
