import Mathlib.Order.Basic
import Mathlib.Data.Quot

namespace LCTR.CorePreorderQuotient

universe u v
set_option autoImplicit false

abbrev ReflRel {A : Type u} (r : A → A → Prop) := ∀ a, r a a
abbrev TransRel {A : Type u} (r : A → A → Prop) := ∀ ⦃a b c⦄, r a b → r b c → r a c
abbrev AntiRel {A : Type u} (r : A → A → Prop) := ∀ ⦃a b⦄, r a b → r b a → a = b

def Pullback {A : Type u} {T : Type v} (f : A → T) (r : T → T → Prop) : A → A → Prop :=
  fun a b => r (f a) (f b)

theorem preorder_pullback {A : Type u} {T : Type v} (f : A → T)
    (r : T → T → Prop) (hr : ReflRel r) (ht : TransRel r) :
    ReflRel (Pullback f r) ∧ TransRel (Pullback f r) := by
  exact ⟨fun a => hr (f a), fun _ _ _ hab hbc => ht hab hbc⟩

theorem source_induced_preorder {A : Type u} {T : Type v} [Preorder T]
    (recover : A → T) :
    ReflRel (Pullback recover (· ≤ ·)) ∧ TransRel (Pullback recover (· ≤ ·)) :=
  preorder_pullback recover (· ≤ ·) le_refl (fun _ _ _ => le_trans)

def OrdDesc {A : Type u} (s : Setoid A) (r : A → A → Prop) : Prop :=
  ∀ a a' b b', s.r a a' → s.r b b' → (r a b ↔ r a' b')

def OrdSep {A : Type u} (s : Setoid A) (r : A → A → Prop) : Prop :=
  ∀ a b, r a b → r b a → s.r a b

def QuotientRel {A : Type u} (s : Setoid A) (r : A → A → Prop)
    (hd : OrdDesc s r) : Quotient s → Quotient s → Prop :=
  Quotient.lift₂ r (fun a b a' b' haa hbb => propext (hd a a' b b' haa hbb))

theorem quotient_on_representatives {A : Type u} (s : Setoid A) (r : A → A → Prop)
    (hd : OrdDesc s r) (a b : A) :
    QuotientRel s r hd (Quotient.mk s a) (Quotient.mk s b) ↔ r a b := Iff.rfl

theorem quotient_preorder {A : Type u} (s : Setoid A) (r : A → A → Prop)
    (hd : OrdDesc s r) (hr : ReflRel r) (ht : TransRel r) :
    ReflRel (QuotientRel s r hd) ∧ TransRel (QuotientRel s r hd) := by
  constructor
  · intro x
    induction x using Quotient.ind with
    | _ a => exact hr a
  · intro x y z
    induction x, y, z using Quotient.inductionOn₃ with
    | _ a b c => exact fun hab hbc => ht hab hbc

theorem quotient_partial_order {A : Type u} (s : Setoid A) (r : A → A → Prop)
    (hd : OrdDesc s r) (hs : OrdSep s r) (hr : ReflRel r) (ht : TransRel r) :
    ReflRel (QuotientRel s r hd) ∧ TransRel (QuotientRel s r hd) ∧
      AntiRel (QuotientRel s r hd) := by
  refine ⟨(quotient_preorder s r hd hr ht).1, (quotient_preorder s r hd hr ht).2, ?_⟩
  intro x y
  induction x, y using Quotient.inductionOn₂ with
  | _ a b => exact fun hab hba => Quotient.sound (hs a b hab hba)

theorem quotient_relation_unique {A : Type u} (s : Setoid A) (r : A → A → Prop)
    (hd : OrdDesc s r) (q : Quotient s → Quotient s → Prop)
    (hq : ∀ a b, q (Quotient.mk s a) (Quotient.mk s b) ↔ r a b) :
    q = QuotientRel s r hd := by
  funext x y
  induction x, y using Quotient.inductionOn₂ with
  | _ a b => exact propext (hq a b)

theorem descent_is_necessary {A : Type u} (s : Setoid A) (r : A → A → Prop)
    (q : Quotient s → Quotient s → Prop)
    (hq : ∀ a b, q (Quotient.mk s a) (Quotient.mk s b) ↔ r a b) : OrdDesc s r := by
  intro a a' b b' haa hbb
  rw [← hq a b, ← hq a' b', Quotient.sound haa, Quotient.sound hbb]

theorem empty_quotient {A : Type u} [IsEmpty A] (s : Setoid A) : IsEmpty (Quotient s) := by
  refine ⟨?_⟩
  intro q
  induction q using Quotient.ind with
  | _ a => exact isEmptyElim a

def UniversalBool : Setoid Bool := ⟨fun _ _ => True, ⟨fun _ => trivial,
  fun _ => trivial, fun _ _ => trivial⟩⟩

def EqualityBool : Setoid Bool := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩

theorem missing_descent_counterexample :
    ReflRel (Eq (α := Bool)) ∧ TransRel (Eq (α := Bool)) ∧
    OrdSep UniversalBool Eq ∧ ¬ OrdDesc UniversalBool Eq := by
  refine ⟨Eq.refl, fun _ _ _ => Eq.trans, fun _ _ _ _ => trivial, ?_⟩
  intro hd
  have h := (hd false true false false trivial trivial).mp rfl
  cases h

theorem missing_separation_counterexample :
    ReflRel (fun (_ _ : Bool) => True) ∧ TransRel (fun (_ _ : Bool) => True) ∧
    OrdDesc EqualityBool (fun _ _ => True) ∧
    ¬ OrdSep EqualityBool (fun _ _ => True) := by
  refine ⟨fun _ => trivial, fun _ _ _ _ _ => trivial,
    fun _ _ _ _ _ _ => Iff.rfl, ?_⟩
  intro hs
  have h : false = true := hs false true trivial trivial
  cases h

end LCTR.CorePreorderQuotient
