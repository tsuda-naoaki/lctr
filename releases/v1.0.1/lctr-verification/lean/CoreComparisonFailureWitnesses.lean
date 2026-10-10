import CoreComparisonStage
import CorePairTransportFactorization

namespace LCTR.CoreComparisonFailureWitnesses
open Set CoreSourceMatch CoreSourceLoops CoreLocalLoopRealization CorePairedComparison
open CorePairTransportFactorization
set_option autoImplicit false
universe u v w z

theorem unique_failure_cases {A : Type u} (P : A → Prop) :
    (¬ ∃! a, P a) ↔ (¬ ∃ a, P a) ∨ ∃ a b, P a ∧ P b ∧ a ≠ b := by
  classical
  constructor
  · intro h
    by_cases he : ∃ a, P a
    · obtain ⟨a, ha⟩ := he
      right
      by_contra hn
      apply h
      refine ⟨a, ha, ?_⟩
      intro b hb
      by_contra hba
      exact hn ⟨a, b, ha, hb, Ne.symm hba⟩
    · exact Or.inl he
  · rintro (hn | ⟨a, b, ha, hb, hab⟩) ⟨c, hc, hu⟩
    · exact hn ⟨c, hc⟩
    · exact hab ((hu a ha).trans (hu b hb).symm)

theorem source_collision {U : Type u} {S : Type v} {V : U → Type w}
    (A : ∀ i, Chapter03SourceOrderRecovery.PartialArrival S (V i)) :
    (¬ CoreSourceMatch.L1 A) ↔
      ∃ i, ∃ x y : {s // s ∈ (A i).dom},
        x ≠ y ∧ (A i).val x.val x.property = (A i).val y.val y.property := by
  classical
  rw [l1_iff_injective]
  simp only [Function.Injective, not_forall, exists_prop]
  constructor
  · rintro ⟨i, x, y, he, hn⟩
    exact ⟨i, x, y, hn, he⟩
  · rintro ⟨i, x, y, hn, he⟩
    exact ⟨i, x, y, he, hn⟩

theorem factorization_failure {I : Type u} {X : I → Type v} {Y : I → Type w}
    (R : ((i : I) → X i) → ((i : I) → Y i) → Prop) :
    (¬ ∃! _f : Factorization R, True) ↔ ¬ Nonempty (Factorization R) := by
  exact not_congr (existence_unique_iff R).symm

variable {U : Type u} {S : Type v} {V : U → Type w}

theorem unrealizable_witness (d : Data U S V) (s : Spec d) :
    (¬ Realizable d s) ↔ ∃ a ∈ s.domain, ¬ s.word.domain a := by
  classical
  simp only [Realizable, not_forall, exists_prop]

theorem unrealizable_no_realization (d : Data U S V) (s : Spec d)
    (h : ¬ Realizable d s) :
    ¬ ∃ f : s.domain → ImageAt d.arrival s.base,
      ∀ a, s.word.action a.val (f a) := by
  exact fun hf => h ((realizable_iff_total_realization d s).mpr hf)

theorem specified_nonfixed (d : Data U S V) (s : Spec d) (h : Realizable d s) :
    (¬ IdOnSpecified d s) ↔ ∃ a : s.domain, realize d s h a ≠ a.val := by
  classical
  rw [specified_identity_iff d s h]
  exact not_forall

theorem set_equality_failure {A : Type u} (B C : Set A) :
    B ≠ C ↔ ∃ a, (a ∈ B ∧ a ∉ C) ∨ (a ∈ C ∧ a ∉ B) := by
  classical
  constructor
  · intro hn
    by_contra hw
    apply hn
    ext a
    constructor
    · intro hb
      by_contra hc
      exact hw ⟨a, Or.inl ⟨hb, hc⟩⟩
    · intro hc
      by_contra hb
      exact hw ⟨a, Or.inr ⟨hc, hb⟩⟩
  · rintro ⟨a, h⟩ rfl
    rcases h with ⟨hb, hc⟩ | ⟨hc, hb⟩
    · exact hc hb
    · exact hb hc

theorem pullback_mismatch {S : Fin 2 → Type v} {V : Fin 2 → U → Type w}
    (x : CoreComparisonStage.Input U S V) :
    (¬ CoreComparisonStage.L5 x) ↔ ∃ i a,
      ¬ (a ∈ x.localRel i ↔
        (fun r => (localRecovery (x.data r).arrival (x.data r).unique i (a r)).val)
          ∈ x.sourceRel) := by
  classical
  simp only [CoreComparisonStage.L5, not_forall]

theorem unsaturated_witness {S : Fin 2 → Type v} {V : Fin 2 → U → Type w}
    (d : RoleData (U := U) (S := S) (V := V)) (rel : ∀ i, Set (LocalPair d i)) :
    (¬ Saturated d rel) ↔ ∃ p q : Synchronized d, Same d p q ∧
      ¬ (p ∈ pairRelation d rel ↔ q ∈ pairRelation d rel) := by
  classical
  simp only [Saturated, not_forall, exists_prop]

theorem unsaturated_no_pullback {S : Fin 2 → Type v} {V : Fin 2 → U → Type w}
    (d : RoleData (U := U) (S := S) (V := V)) (rel : ∀ i, Set (LocalPair d i))
    (h : ¬ Saturated d rel) :
    ¬ ∃ target : Set (QuotientPair d), ∀ p : Synchronized d,
      projection d p ∈ target ↔ p.2 ∈ rel p.1 := by
  rintro ⟨target, hp⟩
  exact h (saturation_necessary_for_pullback d rel target hp)

theorem mixed_nonfixed (d : Data U S V) :
    (¬ IrreducibleMixedIdentity d) ↔
      ∃ i, ∃ p : Path d i i, Irreducible p ∧ ¬ SourceOnly p ∧ ¬ TransportOnly p ∧
        ∃ a b, p.action a b ∧ a ≠ b := by
  classical
  simp only [IrreducibleMixedIdentity, not_forall, exists_prop]

theorem pure_nonfixed (d : Data U S V) :
    (¬ PureLoopIdentity d) ↔
      ∃ i, ∃ p : Path d i i, TransportOnly p ∧ ∃ a b, p.action a b ∧ a ≠ b := by
  classical
  simp only [PureLoopIdentity, not_forall, exists_prop]

end LCTR.CoreComparisonFailureWitnesses
