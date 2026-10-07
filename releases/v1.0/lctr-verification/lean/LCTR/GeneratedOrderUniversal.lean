import Std



namespace LCTR.GeneratedOrderUniversal

set_option autoImplicit false
universe u v

inductive Reach {Q : Type u} (E : Q → Q → Prop) : Q → Q → Prop where
  | refl (q : Q) : Reach E q q
  | step {x y z : Q} : E x y → Reach E y z → Reach E x z

def Edge {S : Type u} (s : Setoid S) (r : S → S → Prop)
    (a b : Quotient s) : Prop :=
  ∃ x y, Quotient.mk s x = a ∧ Quotient.mk s y = b ∧ r x y

def Order {S : Type u} (s : Setoid S) (r : S → S → Prop) := Reach (Edge s r)

theorem reflexive {S : Type u} (s : Setoid S) (r : S → S → Prop)
    (a : Quotient s) : Order s r a a := .refl a

theorem transitive {S : Type u} (s : Setoid S) (r : S → S → Prop)
    {a b c : Quotient s} (ab : Order s r a b) (bc : Order s r b c) :
    Order s r a c := by
  induction ab with
  | refl => exact bc
  | step h _ ih => exact .step h (ih bc)

theorem source_monotone {S : Type u} (s : Setoid S) (r : S → S → Prop)
    {x y : S} (h : r x y) : Order s r (Quotient.mk s x) (Quotient.mk s y) :=
  .step ⟨x,y,rfl,rfl,h⟩ (.refl _)

theorem least_preorder {S : Type u} (s : Setoid S) (r : S → S → Prop)
    (l : Quotient s → Quotient s → Prop)
    (refl : ∀ x, l x x)
    (trans : ∀ x y z, l x y → l y z → l x z)
    (contains : ∀ x y, r x y → l (Quotient.mk s x) (Quotient.mk s y))
    {a b : Quotient s} (h : Order s r a b) : l a b := by
  induction h with
  | refl x => exact refl x
  | @step x y z edge _ ih =>
    obtain ⟨a,b,ha,hb,hab⟩ := edge
    exact trans x y z (by simpa [ha,hb] using contains a b hab) ih

def Factor {S : Type u} {P : Type v} (s : Setoid S) (g : S → P)
    (constant : ∀ x y, s.r x y → g x = g y) : Quotient s → P :=
  Quotient.lift g constant

theorem factor_on_source {S : Type u} {P : Type v} (s : Setoid S) (g : S → P)
    (constant : ∀ x y, s.r x y → g x = g y) (x : S) :
    Factor s g constant (Quotient.mk s x) = g x := rfl

theorem factor_surjective {S : Type u} {P : Type v} (s : Setoid S) (g : S → P)
    (constant : ∀ x y, s.r x y → g x = g y)
    (onto : ∀ p, ∃ x, g x = p) : ∀ p, ∃ a, Factor s g constant a = p := by
  intro p
  obtain ⟨x,hx⟩ := onto p
  exact ⟨Quotient.mk s x,hx⟩

theorem factor_unique {S : Type u} {P : Type v} (s : Setoid S) (g : S → P)
    (constant : ∀ x y, s.r x y → g x = g y)
    (f : Quotient s → P) (commutes : ∀ x, f (Quotient.mk s x) = g x) :
    f = Factor s g constant := by
  funext a
  induction a using Quotient.inductionOn with
  | _ x => exact commutes x

theorem factor_monotone {S : Type u} {P : Type v} (s : Setoid S)
    (r : S → S → Prop) (g : S → P)
    (constant : ∀ x y, s.r x y → g x = g y)
    (l : P → P → Prop) (refl : ∀ p, l p p)
    (trans : ∀ x y z, l x y → l y z → l x z)
    (mono : ∀ x y, r x y → l (g x) (g y))
    {a b : Quotient s} (h : Order s r a b) :
    l (Factor s g constant a) (Factor s g constant b) :=
  least_preorder s r (fun a b => l (Factor s g constant a) (Factor s g constant b))
    (fun a => refl _) (fun a b c => trans _ _ _)
    (fun x y => mono x y) h

theorem partial_order_iff_antisymmetric {S : Type u} (s : Setoid S)
    (r : S → S → Prop) :
    ((∀ a, Order s r a a) ∧
     (∀ a b c, Order s r a b → Order s r b c → Order s r a c) ∧
     (∀ a b, Order s r a b → Order s r b a → a = b)) ↔
    (∀ a b, Order s r a b → Order s r b a → a = b) := by
  constructor
  · exact fun h => h.2.2
  · intro h
    exact ⟨reflexive s r, fun _ _ _ => transitive s r, h⟩

theorem direct_invariance_forces_identity {S : Type u} (s : Setoid S)
    (r : S → S → Prop) (refl : ∀ x, r x x)
    (anti : ∀ x y, r x y → r y x → x = y)
    (invariant : ∀ x x' y y', s.r x x' → s.r y y' → (r x y ↔ r x' y'))
    {x y : S} (eqv : s.r x y) : x = y := by
  have xy := (invariant x x x y (s.refl x) eqv).mp (refl x)
  have yx := (invariant x y x x eqv (s.refl x)).mp (refl x)
  exact anti x y xy yx

#print axioms reflexive
#print axioms transitive
#print axioms source_monotone
#print axioms least_preorder
#print axioms factor_on_source
#print axioms factor_surjective
#print axioms factor_unique
#print axioms factor_monotone
#print axioms partial_order_iff_antisymmetric
#print axioms direct_invariance_forces_identity

end LCTR.GeneratedOrderUniversal
