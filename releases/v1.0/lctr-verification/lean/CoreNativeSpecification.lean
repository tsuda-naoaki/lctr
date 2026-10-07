import CoreTokenGraph

namespace LCTR.CoreNativeSpecification
set_option autoImplicit false
open Set LCTR.CoreTokenGraph
universe u v

def Spec (E : Type u) (L : Type v) : Bool → Type (max u v)
  | false => ULift.{v} E
  | true => E × L
def specAt {E : Type u} {L : Type v} : (a : Bool) → E → L → Spec E L a
  | false,e,_ => ULift.up e
  | true,e,l => (e,l)
def restriction {E : Type u} {L : Type v} :
    (p q : Bool) → (p = true → q = true) → Spec E L q → Spec E L p
  | false,false,_,x => x
  | false,true,_,x => ULift.up x.1
  | true,true,_,x => x
  | true,false,h,_ => False.elim (Bool.noConfusion (h rfl))

theorem strict_specification {E : Type u} {L : Type v} (e : E) (l : L) :
    specAt false e l = ULift.up e := rfl
theorem approximate_specification {E : Type u} {L : Type v} (e : E) (l : L) :
    specAt true e l = (e,l) := rfl
theorem strict_scale_independent {E : Type u} {L : Type v} (e : E) (l m : L) :
    specAt false e l = specAt false e m := rfl
theorem strict_restriction_identity {E : Type u} {L : Type v}
    (h : false = true → false = true) (x : Spec E L false) : restriction false false h x = x := rfl
theorem approximate_restriction_identity {E : Type u} {L : Type v}
    (h : true = true → true = true) (x : Spec E L true) : restriction true true h x = x := rfl
theorem approximation_to_strict_projection {E : Type u} {L : Type v}
    (h : false = true → true = true) (x : Spec E L true) :
    restriction false true h x = ULift.up x.1 := rfl
theorem restriction_coherent {E : Type u} {L : Type v} (p q : Bool)
    (h : p = true → q = true) (e : E) (l : L) :
    restriction p q h (specAt q e l) = specAt p e l := by
  cases p <;> cases q
  · rfl
  · rfl
  · exact False.elim (Bool.noConfusion (h rfl))
  · rfl

def kind (t : Token) : Bool := decide (series t = 3)
theorem edge_kind (a b : Token) (h : Edge a b) : kind a = true → kind b = true := by
  intro ha
  have eq : a.1.val = 3 := of_decide_eq_true ha
  have hb := edge_allowed a b h
  have eb : b.1.val = 3 := by simpa [allowed,eq] using hb
  exact decide_eq_true eb

abbrev EvalArg (E : Type u) (L : Type v) := (t : Token) × Spec E L (kind t)
def argAt {E : Type u} {L : Type v} (e : E) (l : L) (t : Token) : EvalArg E L :=
  ⟨t,specAt (kind t) e l⟩
def predArg {E : Type u} {L : Type v} (a b : Token) (h : Edge a b)
    (x : Spec E L (kind b)) : EvalArg E L := ⟨a,restriction (kind a) (kind b) (edge_kind a b h) x⟩
theorem predecessor_section_coherent {E : Type u} {L : Type v} (a b : Token)
    (h : Edge a b) (e : E) (l : L) :
    predArg a b h (specAt (kind b) e l) = argAt e l a := by
  simp only [predArg,argAt,restriction_coherent]
def evaluate {E : Type u} {L : Type v}
    (K : (t : Token) → Spec E L (kind t) → Prop) (a : EvalArg E L) : Prop := K a.1 a.2
theorem evaluation_exact {E : Type u} {L : Type v}
    (K : (t : Token) → Spec E L (kind t) → Prop) (t : Token) (x : Spec E L (kind t)) :
    evaluate K ⟨t,x⟩ ↔ K t x := Iff.rfl

def totalized {E : Type u} (D : Set E) (P : D → Prop) (x : E) : Prop :=
  ∃ h : x ∈ D, P ⟨x,h⟩
theorem totalization_on_domain {E : Type u} (D : Set E) (P : D → Prop) (x : D) :
    totalized D P x.val ↔ P x := by simp [totalized]
theorem totalization_off_domain {E : Type u} (D : Set E) (P : D → Prop) (x : E)
    (h : x ∉ D) : ¬ totalized D P x := by simp [totalized,h]
theorem totalization_original_exists {E : Type u} (D : Set E) (P : D → Prop) (x : E) :
    totalized D P x ↔ ∃ y : D, x = y.val ∧ P y := by
  constructor
  · rintro ⟨h,hp⟩; exact ⟨⟨x,h⟩,rfl,hp⟩
  · rintro ⟨y,rfl,hp⟩; exact ⟨y.property,hp⟩

theorem restriction_unique_on_image {E : Type u} {L : Type v} (p q : Bool)
    (h : p = true → q = true) (f : Spec E L q → Spec E L p)
    (coh : ∀ e l, f (specAt q e l) = specAt p e l) (e : E) (l : L) :
    f (specAt q e l) = restriction p q h (specAt q e l) := by
  rw [coh,restriction_coherent]
theorem strict_restriction_unique_with_scale {E : Type u} {L : Type v} (l : L)
    (f : Spec E L false → Spec E L false)
    (coh : ∀ e m, f (specAt false e m) = specAt false e m) : f = id := by
  funext x
  exact coh x.down l
theorem empty_scale_uniqueness_control :
    (∀ e : Bool, ∀ _l : Empty, id e = e ∧ (!e) = e) ∧ (id : Bool → Bool) ≠ Bool.not := by
  constructor
  · intro e l; exact nomatch l
  · intro h
    have bad := congrFun h false
    cases bad

end LCTR.CoreNativeSpecification
