import CoreSourceMatch
import CoreTypedWords
import CorePreorderQuotient

namespace LCTR.CoreComparisonIntegration
open LCTR.Chapter03SourceOrderRecovery LCTR.CoreSourceMatch
universe u v w
set_option autoImplicit false
variable {U : Type u} {S : Type v} {V : U → Type w}

def reverseKind : Kind → Kind
  | .src => .src
  | .trPlus => .trMinus
  | .trMinus => .trPlus

theorem reverse_admissible (adm : U → U → Prop) (k : Kind) (i j : U)
    (h : Admissible adm k i j) : Admissible adm (reverseKind k) j i := by
  cases k <;> exact h

def TransportPartialInjection (A : ∀ i, PartialArrival S (V i))
    (tr : ∀ i j, ImageAt A i → ImageAt A j → Prop) (adm : U → U → Prop) : Prop :=
  ∀ i j, adm i j →
    (∀ a b c, tr i j a b → tr i j a c → b=c) ∧
    (∀ a b c, tr i j a c → tr i j b c → a=b)

noncomputable def comparisonSystem (A : ∀ i, PartialArrival S (V i)) (h : L1 A)
    (tr : ∀ i j, ImageAt A i → ImageAt A j → Prop) (adm : U → U → Prop)
    (ht : TransportPartialInjection A tr adm) : LCTR.CoreTypedWords.System U (fun i => ↥(ImageAt A i)) where
  Atom i j := {k : Kind // Admissible adm k i j}
  reverse := fun e => ⟨reverseKind e.val,reverse_admissible adm _ _ _ e.property⟩
  reverse_reverse := by
    intro i j e
    obtain ⟨k,hk⟩ := e
    apply Subtype.ext
    cases k <;> rfl
  act := fun e => Atom A h tr e.val _ _
  functional := by
    intro i j e a b c hb hc
    obtain ⟨k,hk⟩ := e
    cases k with
    | src => exact source_match_functional A h i j a b c hb hc
    | trPlus => exact (ht i j hk).1 a b c hb hc
    | trMinus => exact (ht j i hk).2 b c a hb hc
  reverse_graph := by
    intro i j e a b
    obtain ⟨k,hk⟩ := e
    cases k with
    | src => exact source_match_inverse_graph A h j i b a
    | trPlus => exact Iff.rfl
    | trMinus => exact Iff.rfl

theorem comparison_equivalence (A : ∀ i, PartialArrival S (V i)) (h : L1 A)
    (tr : ∀ i j, ImageAt A i → ImageAt A j → Prop) (adm : U → U → Prop)
    (ht : TransportPartialInjection A tr adm) :
    Equivalence (LCTR.CoreTypedWords.Orbit (comparisonSystem A h tr adm ht)) :=
  LCTR.CoreTypedWords.orbit_equivalence _

theorem equal_recovery_comparison (A : ∀ i, PartialArrival S (V i)) (h : L1 A)
    (tr : ∀ i j, ImageAt A i → ImageAt A j → Prop) (adm : U → U → Prop)
    (ht : TransportPartialInjection A tr adm) (p q : Tagged A)
    (heq : recover A h p = recover A h q) :
    LCTR.CoreTypedWords.Orbit (comparisonSystem A h tr adm ht) p q := by
  let W := comparisonSystem A h tr adm ht
  let e : W.Atom p.1 q.1 := ⟨.src,trivial⟩
  refine ⟨.cons e (.nil q.1), q.2, ?_, rfl⟩
  exact same_source_native_match A h p.1 q.1 p.2 q.2 heq

theorem comparison_order_separation (A : ∀ i, PartialArrival S (V i)) (h : L1 A)
    (tr : ∀ i j, ImageAt A i → ImageAt A j → Prop) (adm : U → U → Prop)
    (ht : TransportPartialInjection A tr adm) (r : S → S → Prop)
    (anti : ∀ {a b}, r a b → r b a → a=b) :
    LCTR.CorePreorderQuotient.OrdSep
      (LCTR.CoreTypedWords.orbitSetoid (comparisonSystem A h tr adm ht))
      (LCTR.CorePreorderQuotient.Pullback (recover A h) r) := by
  intro p q hp hq
  exact equal_recovery_comparison A h tr adm ht p q (anti hp hq)

theorem canonical_comparison_partial_order (A : ∀ i, PartialArrival S (V i)) (h : L1 A)
    (tr : ∀ i j, ImageAt A i → ImageAt A j → Prop) (adm : U → U → Prop)
    (ht : TransportPartialInjection A tr adm) (r : S → S → Prop)
    (refl : ∀ s, r s s) (trans : ∀ {a b c}, r a b → r b c → r a c)
    (anti : ∀ {a b}, r a b → r b a → a=b)
    (desc : LCTR.CorePreorderQuotient.OrdDesc
      (LCTR.CoreTypedWords.orbitSetoid (comparisonSystem A h tr adm ht))
      (LCTR.CorePreorderQuotient.Pullback (recover A h) r)) :
    let q := LCTR.CorePreorderQuotient.QuotientRel
      (LCTR.CoreTypedWords.orbitSetoid (comparisonSystem A h tr adm ht))
      (LCTR.CorePreorderQuotient.Pullback (recover A h) r) desc
    LCTR.CorePreorderQuotient.ReflRel q ∧ LCTR.CorePreorderQuotient.TransRel q ∧
      LCTR.CorePreorderQuotient.AntiRel q := by
  apply LCTR.CorePreorderQuotient.quotient_partial_order
  · exact comparison_order_separation A h tr adm ht r anti
  · exact (LCTR.CorePreorderQuotient.preorder_pullback (recover A h) r refl (fun _ _ _ hab hbc => trans hab hbc)).1
  · exact (LCTR.CorePreorderQuotient.preorder_pullback (recover A h) r refl (fun _ _ _ hab hbc => trans hab hbc)).2

theorem comparison_loop_projection_criterion (A : ∀ i, PartialArrival S (V i)) (h : L1 A)
    (tr : ∀ i j, ImageAt A i → ImageAt A j → Prop) (adm : U → U → Prop)
    (ht : TransportPartialInjection A tr adm) :
    LCTR.CoreTypedWords.LoopIdentity (comparisonSystem A h tr adm ht) ↔
      ∀ i, Function.Injective (fun a : ImageAt A i =>
        Quotient.mk (LCTR.CoreTypedWords.orbitSetoid (comparisonSystem A h tr adm ht)) ⟨i,a⟩) :=
  LCTR.CoreTypedWords.loop_identity_iff_local_projection_injective _

end LCTR.CoreComparisonIntegration
