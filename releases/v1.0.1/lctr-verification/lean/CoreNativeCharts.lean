import CoreExactStructure

namespace LCTR.CoreNativeCharts
open Set LCTR.CoreExactStructure LCTR.CoreOrderAtlas
open LCTR.TransitiveIncomparabilityQuotientCore LCTR.OrderEmbeddingBridgeV1
open LCTR.CoreRepresentationImages
universe u v w z
set_option autoImplicit false
variable {U : Type u} {S : Type v} {V : U → Type w}

theorem local_inc_equivalence (d : Input U S V) (i : U) (h : LocalInc d i) :
    Equivalence (fun x y : localCarrier d i => Inc (strictData d).lt x.val y.val) :=
  (incSetoid (restricted (strictData d) (localDomain d i h))
    (fun x => (strictData d).irrefl x.val) h).iseqv

theorem local_strict_invariance (d : Input U S V) (i : U) (h : LocalInc d i)
    (a a' b b' : localCarrier d i)
    (ha : Inc (strictData d).lt a.val a'.val) (hb : Inc (strictData d).lt b.val b'.val) :
    (strictData d).lt a.val b.val ↔ (strictData d).lt a'.val b'.val :=
  representative_invariance (restricted (strictData d) (localDomain d i h))
    (fun hxy hyz => (strictData d).trans hxy hyz) h ha hb

theorem local_global_inc_restriction (d : Input U S V) (i : U)
    (a b : localCarrier d i) :
    Inc (fun x y : localCarrier d i => (strictData d).lt x.val y.val) a b ↔
      Inc (strictData d).lt a.val b.val := Iff.rfl

theorem global_inc_equivalence (d : Input U S V) (h : GlobalInc d) :
    Equivalence (Inc (strictData d).lt) :=
  (incSetoid (strictData d).lt (strictData d).irrefl h).iseqv

theorem global_strict_invariance (d : Input U S V) (h : GlobalInc d)
    (a a' b b' : Canonical d)
    (ha : Inc (strictData d).lt a a') (hb : Inc (strictData d).lt b b') :
    (strictData d).lt a b ↔ (strictData d).lt a' b' :=
  representative_invariance (strictData d).lt (strictData d).trans h ha hb

 
def reverseInput {X : Type u} (s : StrictData X) (A B : Domain s)
    (p : range (rightProjection s A B)) : range (leftProjection s B A) :=
  ⟨p.val, by
    obtain ⟨x,hx⟩ := p.property
    exact ⟨⟨x.val,x.property.2,x.property.1⟩,hx⟩⟩

theorem reverse_input_commutes {X : Type u} (s : StrictData X) (A B : Domain s)
    (x : Overlap A B) :
    reverseInput s A B (imageProjection (rightProjection s A B) x) =
      imageProjection (leftProjection s B A) ⟨x.val,x.property.2,x.property.1⟩ := rfl

theorem reversed_chart_is_inverse {X : Type u} (s : StrictData X) (A B : Domain s)
    (p : range (leftProjection s A B)) :
    (overlapChange s B A (reverseInput s A B (overlapChange s A B p))).val = p.val := by
  obtain ⟨x,rfl⟩ := imageProjection_surjective (leftProjection s A B) p
  rw [overlap_change_commutes,reverse_input_commutes,overlap_change_commutes]
  rfl

theorem actual_chart_change_order (d : Input U S V) (i j : U)
    (hi : LocalInc d i) (hj : LocalInc d j)
    (a b : range (leftProjection (strictData d) (localDomain d i hi) (localDomain d j hj))) :
    order (strictData d) (localDomain d j hj)
      (overlapChange (strictData d) (localDomain d i hi) (localDomain d j hj) a).val
      (overlapChange (strictData d) (localDomain d i hi) (localDomain d j hj) b).val ↔
    order (strictData d) (localDomain d i hi) a.val b.val :=
  overlap_order (strictData d) (localDomain d i hi) (localDomain d j hj) a b

theorem actual_chart_change_inverse (d : Input U S V) (i j : U)
    (hi : LocalInc d i) (hj : LocalInc d j)
    (p : range (leftProjection (strictData d) (localDomain d i hi) (localDomain d j hj))) :
    (overlapChange (strictData d) (localDomain d j hj) (localDomain d i hi)
      (reverseInput (strictData d) (localDomain d i hi) (localDomain d j hj)
        (overlapChange (strictData d) (localDomain d i hi) (localDomain d j hj) p))).val = p.val :=
  reversed_chart_is_inverse (strictData d) (localDomain d i hi) (localDomain d j hj) p

theorem actual_chart_change_identity (d : Input U S V) (i : U) (hi : LocalInc d i)
    (p : range (leftProjection (strictData d) (localDomain d i hi) (localDomain d i hi))) :
    (overlapChange (strictData d) (localDomain d i hi) (localDomain d i hi) p).val = p.val :=
  self_change_identity (strictData d) (localDomain d i hi) p

theorem actual_triple_cocycle (d : Input U S V) (i j k : U)
    (hi : LocalInc d i) (hj : LocalInc d j) (hk : LocalInc d k)
    (x : Canonical d) (xi : x ∈ localCarrier d i) (xj : x ∈ localCarrier d j)
    (xk : x ∈ localCarrier d k) :
    (overlapChange (strictData d) (localDomain d j hj) (localDomain d k hk)
      (continueOverlap (strictData d) (localDomain d i hi) (localDomain d j hj)
        (localDomain d k hk) x xi xj xk)).val =
    (overlapChange (strictData d) (localDomain d i hi) (localDomain d k hk)
      (imageProjection (leftProjection (strictData d) (localDomain d i hi) (localDomain d k hk))
        ⟨x,xi,xk⟩)).val :=
  triple_overlap_cocycle (strictData d) (localDomain d i hi) (localDomain d j hj)
    (localDomain d k hk) x xi xj xk

theorem quotient_embedding_composition {X : Type u} {Q : Type v} {Y : Type w}
    (p : X → Q) (e : Q → Y) (inj : Function.Injective e)
    (same strict : X → X → Prop) (ltQ : Q → Q → Prop) (ltY : Y → Y → Prop)
    (ker : ∀ x y, p x = p y ↔ same x y)
    (ord : ∀ x y, ltQ (p x) (p y) ↔ strict x y)
    (emb : ∀ a b, ltY (e a) (e b) ↔ ltQ a b) :
    (∀ x y, e (p x) = e (p y) ↔ same x y) ∧
    (∀ x y, ltY (e (p x)) (e (p y)) ↔ strict x y) :=
  ⟨fun x y => inj.eq_iff.trans (ker x y),fun x y => (emb _ _).trans (ord x y)⟩

theorem actual_representation_contract (d : Input U S V) (h : GlobalInc d) {Y : Type z}
    (e : GlobalQ d h → Y) (inj : Function.Injective e) (lt : Y → Y → Prop)
    (emb : ∀ a b, lt (e a) (e b) ↔ globalOrder d h a b) :
    (∀ x y, represented d h e x = represented d h e y ↔ Inc (strictData d).lt x y) ∧
    (∀ x y, lt (represented d h e x) (represented d h e y) ↔ (strictData d).lt x y) :=
  ⟨represented_kernel d h e inj,represented_order_pullback d h e lt emb⟩

theorem actual_chart_composition (d : Input U S V) (i : U) (h : LocalInc d i) :
    chart d i h = projection (strictData d) (localDomain d i h) ∘ receive d i ∧
    Function.Surjective (chart d i h) ∧
    (∀ a b, chart d i h a = chart d i h b ↔
      Inc (strictData d).lt (canonicalProjection d ⟨i,a⟩) (canonicalProjection d ⟨i,b⟩)) ∧
    (∀ a b, order (strictData d) (localDomain d i h) (chart d i h a) (chart d i h b) ↔
      (strictData d).lt (canonicalProjection d ⟨i,a⟩) (canonicalProjection d ⟨i,b⟩)) :=
  ⟨rfl,actual_local_chart_contract d i h⟩

end LCTR.CoreNativeCharts
