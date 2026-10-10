import CoreSourceLoops
import CoreRepresentationImages

namespace LCTR.CorePairedComparison
open Set LCTR.CoreSourceMatch LCTR.CoreSourceLoops
universe u v w
set_option autoImplicit false

variable {U : Type u} {S : Fin 2 → Type v} {V : Fin 2 → U → Type w}

abbrev RoleData := (r : Fin 2) → Data U (S r) (V r)
abbrev LocalPair (d : RoleData (U := U) (S := S) (V := V)) (i : U) :=
  (r : Fin 2) → ImageAt (d r).arrival i
abbrev Synchronized (d : RoleData (U := U) (S := S) (V := V)) := Sigma (LocalPair d)
abbrev QuotientPair (d : RoleData (U := U) (S := S) (V := V)) :=
  (r : Fin 2) → Quotient (LCTR.CoreTypedWords.orbitSetoid (system (d r)))

noncomputable def projection (d : RoleData (U := U) (S := S) (V := V))
    (p : Synchronized d) : QuotientPair d :=
  fun r => Quotient.mk (LCTR.CoreTypedWords.orbitSetoid (system (d r))) ⟨p.1,p.2 r⟩

def Same (d : RoleData (U := U) (S := S) (V := V)) (p q : Synchronized d) : Prop :=
  ∀ r, LCTR.CoreTypedWords.Orbit (system (d r)) ⟨p.1,p.2 r⟩ ⟨q.1,q.2 r⟩

theorem paired_equivalence (d : RoleData (U := U) (S := S) (V := V)) : Equivalence (Same d) :=
  ⟨fun p r => (LCTR.CoreTypedWords.orbit_equivalence (system (d r))).refl ⟨p.1,p.2 r⟩,
    fun h r => (LCTR.CoreTypedWords.orbit_equivalence (system (d r))).symm (h r),
    fun h k r => (LCTR.CoreTypedWords.orbit_equivalence (system (d r))).trans (h r) (k r)⟩

theorem projection_kernel (d : RoleData (U := U) (S := S) (V := V)) (p q : Synchronized d) :
    projection d p = projection d q ↔ Same d p q := by
  constructor
  · intro h r
    exact Quotient.exact (congrFun h r)
  · intro h
    exact funext (fun r => Quotient.sound (h r))

def pairRelation (d : RoleData (U := U) (S := S) (V := V))
    (localRel : ∀ i, Set (LocalPair d i)) : Set (Synchronized d) :=
  {p | p.2 ∈ localRel p.1}

def Saturated (d : RoleData (U := U) (S := S) (V := V))
    (localRel : ∀ i, Set (LocalPair d i)) : Prop :=
  ∀ p q, Same d p q → (p ∈ pairRelation d localRel ↔ q ∈ pairRelation d localRel)

noncomputable def canonicalRelation (d : RoleData (U := U) (S := S) (V := V))
    (localRel : ∀ i, Set (LocalPair d i)) : Set (QuotientPair d) :=
  projection d '' pairRelation d localRel

theorem canonical_relation_typed (d : RoleData (U := U) (S := S) (V := V))
    (localRel : ∀ i, Set (LocalPair d i)) : canonicalRelation d localRel ⊆ range (projection d) := by
  rintro x ⟨p,_,rfl⟩
  exact ⟨p,rfl⟩

theorem canonical_relation_pullback (d : RoleData (U := U) (S := S) (V := V))
    (localRel : ∀ i, Set (LocalPair d i)) (sat : Saturated d localRel) (p : Synchronized d) :
    projection d p ∈ canonicalRelation d localRel ↔ p.2 ∈ localRel p.1 := by
  constructor
  · rintro ⟨q,hq,eq⟩
    exact (sat q p ((projection_kernel d q p).mp eq)).mp hq
  · exact fun hp => ⟨p,hp,rfl⟩

theorem source_relation_pullback (d : RoleData (U := U) (S := S) (V := V))
    (localRel : ∀ i, Set (LocalPair d i)) (sat : Saturated d localRel)
    (sourceRel : Set ((r : Fin 2) → S r))
    (compatible : ∀ i a, a ∈ localRel i ↔
      (fun r => (localRecovery (d r).arrival (d r).unique i (a r)).val) ∈ sourceRel)
    (p : Synchronized d) :
    projection d p ∈ canonicalRelation d localRel ↔
      (fun r => (localRecovery (d r).arrival (d r).unique p.1 (p.2 r)).val) ∈ sourceRel :=
  (canonical_relation_pullback d localRel sat p).trans (compatible p.1 p.2)

theorem canonical_relation_least (d : RoleData (U := U) (S := S) (V := V))
    (localRel : ∀ i, Set (LocalPair d i)) (target : Set (QuotientPair d))
    (contains : ∀ p : Synchronized d, p.2 ∈ localRel p.1 → projection d p ∈ target) :
    canonicalRelation d localRel ⊆ target := by
  rintro x ⟨p,hp,rfl⟩
  exact contains p hp

theorem canonical_relation_unique_minimal (d : RoleData (U := U) (S := S) (V := V))
    (localRel : ∀ i, Set (LocalPair d i)) :
    ∃! target : Set (QuotientPair d),
      (∀ p : Synchronized d, p.2 ∈ localRel p.1 → projection d p ∈ target) ∧
      (∀ other : Set (QuotientPair d),
        (∀ p : Synchronized d, p.2 ∈ localRel p.1 → projection d p ∈ other) → target ⊆ other) := by
  have contains : ∀ p : Synchronized d, p.2 ∈ localRel p.1 →
      projection d p ∈ canonicalRelation d localRel := fun p hp => ⟨p,hp,rfl⟩
  refine ⟨canonicalRelation d localRel, ⟨contains,canonical_relation_least d localRel⟩, ?_⟩
  intro target h
  exact Set.Subset.antisymm (h.2 _ contains) (canonical_relation_least d localRel target h.1)

theorem saturation_necessary_for_pullback (d : RoleData (U := U) (S := S) (V := V))
    (localRel : ∀ i, Set (LocalPair d i)) (target : Set (QuotientPair d))
    (pullback : ∀ p : Synchronized d, projection d p ∈ target ↔ p.2 ∈ localRel p.1) :
    Saturated d localRel := by
  intro p q same
  change p.2 ∈ localRel p.1 ↔ q.2 ∈ localRel q.1
  rw [← pullback p,← pullback q,(projection_kernel d p q).mpr same]

theorem local_pair_projection_injective (d : RoleData (U := U) (S := S) (V := V))
    (mixed : ∀ r, IrreducibleMixedIdentity (d r)) (pure : ∀ r, PureLoopIdentity (d r)) (i : U) :
    Function.Injective (fun a : LocalPair d i => projection d ⟨i,a⟩) := by
  intro a b same
  funext r
  exact ((gluing_iff_local_injectivity (d r) (mixed r)).mp (pure r) i) (congrFun same r)

theorem empty_relation (d : RoleData (U := U) (S := S) (V := V)) :
    canonicalRelation d (fun _ => ∅) = ∅ := by
  ext x
  constructor
  · rintro ⟨p,hp,_⟩
    exact hp
  · exact False.elim

end LCTR.CorePairedComparison
