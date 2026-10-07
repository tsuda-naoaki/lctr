import CorePairedComparison
import CoreLocalLoopRealization

namespace LCTR.CoreComparisonStage
open Set LCTR.CoreSourceMatch LCTR.CoreSourceLoops LCTR.CorePairedComparison
open LCTR.CoreLocalLoopRealization
universe u v w
set_option autoImplicit false

structure Input (U : Type u) (S : Fin 2 → Type v) (V : Fin 2 → U → Type w) where
  data : RoleData (U := U) (S := S) (V := V)
  specs : (r : Fin 2) → Set (Spec (data r))
  localRel : ∀ i, Set (LocalPair data i)
  sourceRel : Set ((r : Fin 2) → S r)

variable {U : Type u} {S : Fin 2 → Type v} {V : Fin 2 → U → Type w}

def L3 (x : Input U S V) : Prop := ∀ r (s : x.specs r), Realizable (x.data r) s.val
def L4 (x : Input U S V) : Prop := ∀ r (s : x.specs r), IdOnSpecified (x.data r) s.val
def L5 (x : Input U S V) : Prop := ∀ i a, a ∈ x.localRel i ↔
  (fun r => (localRecovery (x.data r).arrival (x.data r).unique i (a r)).val) ∈ x.sourceRel
def L6 (x : Input U S V) : Prop := Saturated x.data x.localRel
def L7 (x : Input U S V) : Prop := ∀ r, IrreducibleMixedIdentity (x.data r)
def G (x : Input U S V) : Prop := ∀ r, PureLoopIdentity (x.data r)

 
def ResidualOperative (x : Input U S V) : Prop :=
  (L3 x ∧ L4 x ∧ L5 x ∧ L6 x ∧ L7 x) ∧ G x

abbrev RoleQuotient (x : Input U S V) (r : Fin 2) :=
  Quotient (LCTR.CoreTypedWords.orbitSetoid (system (x.data r)))

noncomputable def roleProjection (x : Input U S V) (r : Fin 2) (i : U)
    (a : ImageAt (x.data r).arrival i) : RoleQuotient x r :=
  Quotient.mk (LCTR.CoreTypedWords.orbitSetoid (system (x.data r))) ⟨i,a⟩

structure Output (x : Input U S V) where
  loops : ∀ r (s : x.specs r), s.val.domain → ImageAt (x.data r).arrival s.val.base
  localProjection : ∀ r i, ImageAt (x.data r).arrival i → RoleQuotient x r
  relation : Set (QuotientPair x.data)

def Valid (x : Input U S V) (o : Output x) : Prop :=
  (∀ r (s : x.specs r) a, s.val.word.action a.val (o.loops r s a)) ∧
  (∀ r i a, o.localProjection r i a = roleProjection x r i a) ∧
  (∀ p : Synchronized x.data, p.2 ∈ x.localRel p.1 → projection x.data p ∈ o.relation) ∧
  (∀ other : Set (QuotientPair x.data),
    (∀ p : Synchronized x.data, p.2 ∈ x.localRel p.1 → projection x.data p ∈ other) →
    o.relation ⊆ other)

noncomputable def generate (x : Input U S V) (h : L3 x) : Output x where
  loops := fun r s => realize (x.data r) s.val (h r s)
  localProjection := roleProjection x
  relation := canonicalRelation x.data x.localRel

theorem generated_valid (x : Input U S V) (h : L3 x) : Valid x (generate x h) := by
  refine ⟨?_,?_,?_,?_⟩
  · exact fun r s a => realization_correct (x.data r) s.val (h r s) a
  · exact fun _ _ _ => rfl
  · exact fun p hp => ⟨p,hp,rfl⟩
  · exact canonical_relation_least x.data x.localRel

theorem output_unique (x : Input U S V) (h : L3 x) (o : Output x) (valid : Valid x o) :
    o = generate x h := by
  have loops : o.loops = (generate x h).loops := by
    funext r s
    exact realization_unique (x.data r) s.val (h r s) (o.loops r s) (valid.1 r s)
  have proj : o.localProjection = (generate x h).localProjection := by
    funext r i a
    exact valid.2.1 r i a
  have rel : o.relation = (generate x h).relation :=
    Set.Subset.antisymm
      (valid.2.2.2 _ (fun p hp => ⟨p,hp,rfl⟩))
      (canonical_relation_least x.data x.localRel o.relation valid.2.2.1)
  have ext : ∀ a b : Output x, a.loops = b.loops → a.localProjection = b.localProjection →
      a.relation = b.relation → a = b := by
    intro a b
    cases a
    cases b
    intro h1 h2 h3
    cases h1
    cases h2
    cases h3
    rfl
  exact ext o (generate x h) loops proj rel

theorem unique_generated_output (x : Input U S V) (h : ResidualOperative x) :
    ∃! o : Output x, Valid x o :=
  ⟨generate x h.1.1,generated_valid x h.1.1,fun o valid => output_unique x h.1.1 o valid⟩

theorem generated_local_injective (x : Input U S V) (h : ResidualOperative x)
    (r : Fin 2) (i : U) : Function.Injective ((generate x h.1.1).localProjection r i) :=
  (gluing_iff_local_injectivity (x.data r) (h.1.2.2.2.2 r)).mp (h.2 r) i

theorem generated_pair_injective (x : Input U S V) (h : ResidualOperative x) (i : U) :
    Function.Injective (fun a : LocalPair x.data i => projection x.data ⟨i,a⟩) :=
  local_pair_projection_injective x.data h.1.2.2.2.2 h.2 i

theorem generated_local_pullback (x : Input U S V) (h : ResidualOperative x)
    (p : Synchronized x.data) :
    projection x.data p ∈ (generate x h.1.1).relation ↔ p.2 ∈ x.localRel p.1 :=
  canonical_relation_pullback x.data x.localRel h.1.2.2.2.1 p

theorem generated_source_pullback (x : Input U S V) (h : ResidualOperative x)
    (p : Synchronized x.data) :
    projection x.data p ∈ (generate x h.1.1).relation ↔
      (fun r => (localRecovery (x.data r).arrival (x.data r).unique p.1 (p.2 r)).val) ∈ x.sourceRel :=
  source_relation_pullback x.data x.localRel h.1.2.2.2.1 x.sourceRel h.1.2.2.1 p

theorem generated_loop_identity (x : Input U S V) (h : ResidualOperative x)
    (r : Fin 2) (s : x.specs r) (a : s.val.domain) :
    (generate x h.1.1).loops r s a = a.val :=
  (specified_identity_iff (x.data r) s.val (h.1.1 r s)).mp (h.1.2.1 r s) a

theorem generated_relation_least (x : Input U S V) (h : ResidualOperative x)
    (other : Set (QuotientPair x.data))
    (contains : ∀ p : Synchronized x.data, p.2 ∈ x.localRel p.1 → projection x.data p ∈ other) :
    (generate x h.1.1).relation ⊆ other :=
  canonical_relation_least x.data x.localRel other contains

theorem valid_output_requires_realizability (x : Input U S V) (o : Output x)
    (valid : Valid x o) : L3 x := by
  intro r s
  exact (realizable_iff_total_realization (x.data r) s.val).mpr ⟨o.loops r s,valid.1 r s⟩

theorem faithful_relation_requires_saturation (x : Input U S V) (o : Output x)
    (pullback : ∀ p : Synchronized x.data, projection x.data p ∈ o.relation ↔ p.2 ∈ x.localRel p.1) :
    L6 x := saturation_necessary_for_pullback x.data x.localRel o.relation pullback

end LCTR.CoreComparisonStage
