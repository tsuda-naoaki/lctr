import CoreComparisonIntegration
import CoreOrderAtlas

namespace LCTR.CoreExactStructure
open Set LCTR.Chapter03SourceOrderRecovery LCTR.CoreSourceMatch
open LCTR.CoreComparisonIntegration LCTR.CorePreorderQuotient
open LCTR.OrderEmbeddingBridgeV1 LCTR.TransitiveIncomparabilityQuotientCore
open LCTR.CoreRepresentationImages
universe u v w z
set_option autoImplicit false

structure Input (U : Type u) (S : Type v) (V : U → Type w) where
  arrival : ∀ i, PartialArrival S (V i)
  unique : L1 arrival
  transport : ∀ i j, ImageAt arrival i → ImageAt arrival j → Prop
  admissible : U → U → Prop
  transportInjective : TransportPartialInjection arrival transport admissible
  sourceOrder : S → S → Prop
  refl : ReflRel sourceOrder
  trans : TransRel sourceOrder
  anti : AntiRel sourceOrder
  descent : OrdDesc
    (LCTR.CoreTypedWords.orbitSetoid
      (comparisonSystem arrival unique transport admissible transportInjective))
    (Pullback (recover arrival unique) sourceOrder)

variable {U : Type u} {S : Type v} {V : U → Type w}

noncomputable abbrev canonicalSetoid (d : Input U S V) :=
  LCTR.CoreTypedWords.orbitSetoid
    (comparisonSystem d.arrival d.unique d.transport d.admissible d.transportInjective)

abbrev Canonical (d : Input U S V) := Quotient (canonicalSetoid d)

noncomputable def canonicalProjection (d : Input U S V) (x : Tagged d.arrival) : Canonical d :=
  Quotient.mk (canonicalSetoid d) x

noncomputable def canonicalOrder (d : Input U S V) : Canonical d → Canonical d → Prop :=
  QuotientRel (canonicalSetoid d) (Pullback (recover d.arrival d.unique) d.sourceOrder) d.descent

theorem canonical_partial_order (d : Input U S V) :
    ReflRel (canonicalOrder d) ∧ TransRel (canonicalOrder d) ∧ AntiRel (canonicalOrder d) :=
  canonical_comparison_partial_order d.arrival d.unique d.transport d.admissible d.transportInjective
    d.sourceOrder d.refl (fun hxy hyz => d.trans hxy hyz) (fun hxy hyx => d.anti hxy hyx) d.descent

theorem canonical_order_representatives (d : Input U S V) (x y : Tagged d.arrival) :
    canonicalOrder d (canonicalProjection d x) (canonicalProjection d y) ↔
      d.sourceOrder (recover d.arrival d.unique x) (recover d.arrival d.unique y) := Iff.rfl

noncomputable def strictData (d : Input U S V) : LCTR.CoreOrderAtlas.StrictData (Canonical d) where
  lt x y := canonicalOrder d x y ∧ x ≠ y
  irrefl := fun _ h => h.2 rfl
  trans := by
    intro x y z hxy hyz
    refine ⟨(canonical_partial_order d).2.1 hxy.1 hyz.1, ?_⟩
    intro eqxz
    apply hxy.2
    exact (canonical_partial_order d).2.2 hxy.1 (eqxz.symm ▸ hyz.1)

theorem strict_part_contract (d : Input U S V) :
    (∀ x, ¬ (strictData d).lt x x) ∧ TransRel (strictData d).lt :=
  ⟨(strictData d).irrefl, fun _ _ _ hxy hyz => (strictData d).trans hxy hyz⟩

noncomputable def localCarrier (d : Input U S V) (i : U) : Set (Canonical d) :=
  range (fun a : ImageAt d.arrival i => canonicalProjection d ⟨i,a⟩)

noncomputable def receive (d : Input U S V) (i : U) :
    ImageAt d.arrival i → localCarrier d i :=
  imageProjection (fun a => canonicalProjection d ⟨i,a⟩)

theorem receive_onto (d : Input U S V) (i : U) : Function.Surjective (receive d i) :=
  imageProjection_surjective (fun a => canonicalProjection d ⟨i,a⟩)

abbrev LocalInc (d : Input U S V) (i : U) : Prop :=
  ∀ {x y z : localCarrier d i},
    Inc (fun a b : localCarrier d i => (strictData d).lt a.val b.val) x y →
    Inc (fun a b : localCarrier d i => (strictData d).lt a.val b.val) y z →
    Inc (fun a b : localCarrier d i => (strictData d).lt a.val b.val) x z

noncomputable def localDomain (d : Input U S V) (i : U) (h : LocalInc d i) :
    LCTR.CoreOrderAtlas.Domain (strictData d) := ⟨localCarrier d i, h⟩

abbrev LocalQ (d : Input U S V) (i : U) (h : LocalInc d i) :=
  LCTR.CoreOrderAtlas.Q (strictData d) (localDomain d i h)

noncomputable def chart (d : Input U S V) (i : U) (h : LocalInc d i) :
    ImageAt d.arrival i → LocalQ d i h :=
  LCTR.CoreOrderAtlas.projection (strictData d) (localDomain d i h) ∘ receive d i

theorem actual_local_chart_contract (d : Input U S V) (i : U) (h : LocalInc d i) :
    Function.Surjective (chart d i h) ∧
    (∀ a b, chart d i h a = chart d i h b ↔
      Inc (strictData d).lt (canonicalProjection d ⟨i,a⟩) (canonicalProjection d ⟨i,b⟩)) ∧
    (∀ a b, LCTR.CoreOrderAtlas.order (strictData d) (localDomain d i h)
      (chart d i h a) (chart d i h b) ↔
      (strictData d).lt (canonicalProjection d ⟨i,a⟩) (canonicalProjection d ⟨i,b⟩)) :=
  LCTR.CoreOrderAtlas.composite_chart_contract (strictData d) (localDomain d i h)
    (receive d i) (receive_onto d i)

theorem actual_local_quotient_linear (d : Input U S V) (i : U) (h : LocalInc d i) :
    let r := LCTR.CoreOrderAtlas.order (strictData d) (localDomain d i h)
    (∀ q, ¬ r q q) ∧ (∀ {x y z}, r x y → r y z → r x z) ∧
      (∀ {x y}, x ≠ y → r x y ∨ r y x) :=
  LCTR.CoreOrderAtlas.quotient_strict_linear (strictData d) (localDomain d i h)

abbrev GlobalInc (d : Input U S V) : Prop :=
  ∀ {x y z : Canonical d}, Inc (strictData d).lt x y → Inc (strictData d).lt y z →
    Inc (strictData d).lt x z

theorem global_implies_local_inc (d : Input U S V) (h : GlobalInc d) (i : U) : LocalInc d i :=
  fun hxy hyz => h hxy hyz

abbrev GlobalQ (d : Input U S V) (h : GlobalInc d) :=
  IncQuotient (strictData d).lt (strictData d).irrefl h

noncomputable def globalProjection (d : Input U S V) (h : GlobalInc d) : Canonical d → GlobalQ d h :=
  proj (strictData d).lt (strictData d).irrefl h

noncomputable def globalOrder (d : Input U S V) (h : GlobalInc d) : GlobalQ d h → GlobalQ d h → Prop :=
  quotientLt (strictData d).lt (strictData d).irrefl h

noncomputable def localGlobal (d : Input U S V) (i : U) (hl : LocalInc d i) (hg : GlobalInc d) :
    LocalQ d i hl → GlobalQ d hg :=
  Quotient.map (fun x : localCarrier d i => x.val) (fun _ _ hxy => hxy)

theorem local_global_commutes (d : Input U S V) (i : U) (hl : LocalInc d i) (hg : GlobalInc d)
    (x : localCarrier d i) :
    localGlobal d i hl hg (LCTR.CoreOrderAtlas.projection (strictData d) (localDomain d i hl) x) =
      globalProjection d hg x.val := rfl

theorem local_global_injective (d : Input U S V) (i : U) (hl : LocalInc d i) (hg : GlobalInc d) :
    Function.Injective (localGlobal d i hl hg) := by
  intro a b same
  obtain ⟨x,rfl⟩ := LCTR.CoreOrderAtlas.projection_onto (strictData d) (localDomain d i hl) a
  obtain ⟨y,rfl⟩ := LCTR.CoreOrderAtlas.projection_onto (strictData d) (localDomain d i hl) b
  exact (LCTR.CoreOrderAtlas.projection_kernel (strictData d) (localDomain d i hl) x y).mpr
    ((proj_eq_iff_inc (strictData d).lt (strictData d).irrefl hg x.val y.val).mp same)

theorem local_global_order (d : Input U S V) (i : U) (hl : LocalInc d i) (hg : GlobalInc d)
    (a b : LocalQ d i hl) :
    globalOrder d hg (localGlobal d i hl hg a) (localGlobal d i hl hg b) ↔
      LCTR.CoreOrderAtlas.order (strictData d) (localDomain d i hl) a b := by
  obtain ⟨x,rfl⟩ := LCTR.CoreOrderAtlas.projection_onto (strictData d) (localDomain d i hl) a
  obtain ⟨y,rfl⟩ := LCTR.CoreOrderAtlas.projection_onto (strictData d) (localDomain d i hl) b
  exact (quotientLt_proj_iff (strictData d).lt (strictData d).irrefl
    (strictData d).trans hg x.val y.val).trans
    (LCTR.CoreOrderAtlas.projection_order (strictData d) (localDomain d i hl) x y).symm

theorem actual_global_quotient_linear (d : Input U S V) (h : GlobalInc d) :
    (∀ q, ¬ globalOrder d h q q) ∧
    (∀ {x y z}, globalOrder d h x y → globalOrder d h y z → globalOrder d h x z) ∧
    (∀ {x y}, x ≠ y → globalOrder d h x y ∨ globalOrder d h y x) :=
  quotient_strict_linear_components (strictData d).lt (strictData d).irrefl (strictData d).trans h

theorem local_global_chart_commutes (d : Input U S V) (i : U) (hl : LocalInc d i) (hg : GlobalInc d)
    (a : ImageAt d.arrival i) :
    localGlobal d i hl hg (chart d i hl a) = globalProjection d hg (canonicalProjection d ⟨i,a⟩) := rfl

noncomputable def represented (d : Input U S V) (hg : GlobalInc d) {Y : Type z}
    (embedding : GlobalQ d hg → Y) : Canonical d → Y := embedding ∘ globalProjection d hg

theorem chosen_representation_compatibility (d : Input U S V) (i : U)
    (hl : LocalInc d i) (hg : GlobalInc d) {Y : Type z} (embedding : GlobalQ d hg → Y)
    (a : ImageAt d.arrival i) :
    represented d hg embedding (canonicalProjection d ⟨i,a⟩) =
      embedding (localGlobal d i hl hg (chart d i hl a)) := rfl

theorem represented_order_pullback (d : Input U S V) (hg : GlobalInc d) {Y : Type z}
    (embedding : GlobalQ d hg → Y) (lt : Y → Y → Prop)
    (orderEmbedding : ∀ a b, lt (embedding a) (embedding b) ↔ globalOrder d hg a b)
    (x y : Canonical d) :
    lt (represented d hg embedding x) (represented d hg embedding y) ↔ (strictData d).lt x y :=
  (orderEmbedding _ _).trans
    (quotientLt_proj_iff (strictData d).lt (strictData d).irrefl (strictData d).trans hg x y)

theorem represented_kernel (d : Input U S V) (hg : GlobalInc d) {Y : Type z}
    (embedding : GlobalQ d hg → Y) (injective : Function.Injective embedding) (x y : Canonical d) :
    represented d hg embedding x = represented d hg embedding y ↔ Inc (strictData d).lt x y :=
  injective.eq_iff.trans (proj_eq_iff_inc (strictData d).lt (strictData d).irrefl hg x y)

end LCTR.CoreExactStructure
