import CoreComparisonStage
import CoreRepresentationStages

namespace LCTR.CoreExactCompletion
open Set LCTR.CoreExactStructure LCTR.CoreRepresentationImages
open LCTR.CoreUniversalFactorization LCTR.CorePreorderQuotient LCTR.CoreSourceMatch
open LCTR.OrderEmbeddingBridgeV1 LCTR.TransitiveIncomparabilityQuotientCore
universe u v w z
set_option autoImplicit false
noncomputable section

def residualStageSeven {U : Type u} {S : Fin 2 → Type v} {V : Fin 2 → U → Type w}
    (x : LCTR.CoreComparisonStage.Input U S V) : Prop :=
  LCTR.CoreComparisonStage.L3 x ∧ LCTR.CoreComparisonStage.L4 x ∧
  LCTR.CoreComparisonStage.L5 x ∧ LCTR.CoreComparisonStage.L6 x ∧ LCTR.CoreComparisonStage.L7 x

theorem native_master_condition {U : Type u} {S : Fin 2 → Type v} {V : Fin 2 → U → Type w}
    (x : LCTR.CoreComparisonStage.Input U S V) :
    LCTR.CoreComparisonStage.ResidualOperative x ↔ residualStageSeven x ∧
      LCTR.CoreComparisonStage.G x := Iff.rfl

theorem native_conditions_give_comparison_output
    {U : Type u} {S : Fin 2 → Type v} {V : Fin 2 → U → Type w}
    (x : LCTR.CoreComparisonStage.Input U S V)
    (hs : residualStageSeven x) (hg : LCTR.CoreComparisonStage.G x) :
    LCTR.CoreComparisonStage.ResidualOperative x ∧
      ∃! o : LCTR.CoreComparisonStage.Output x, LCTR.CoreComparisonStage.Valid x o :=
  ⟨⟨hs,hg⟩,LCTR.CoreComparisonStage.unique_generated_output x ⟨hs,hg⟩⟩

variable {U : Type u} {S : Type v} {V : U → Type w}

theorem canonical_order_unique (d : Input U S V) (r : Canonical d → Canonical d → Prop)
    (on_representatives : ∀ x y : Tagged d.arrival,
      r (canonicalProjection d x) (canonicalProjection d y) ↔
        d.sourceOrder (recover d.arrival d.unique x) (recover d.arrival d.unique y)) :
    r = canonicalOrder d := by
  funext x y
  induction x using Quotient.inductionOn with
  | _ a =>
    induction y using Quotient.inductionOn with
    | _ b => exact propext ((on_representatives a b).trans (canonical_order_representatives d a b).symm)

def nativeLocalDomain (d : Input U S V) (g : GlobalInc d) (i : U) :=
  localDomain d i (global_implies_local_inc d g i)

abbrev NativeLocalQ (d : Input U S V) (g : GlobalInc d) (i : U) :=
  LCTR.CoreOrderAtlas.Q (strictData d) (nativeLocalDomain d g i)

abbrev ChangeDomain (d : Input U S V) (g : GlobalInc d) (i j : U) :=
  range (LCTR.CoreOrderAtlas.leftProjection (strictData d)
    (nativeLocalDomain d g i) (nativeLocalDomain d g j))

abbrev ChangeRange (d : Input U S V) (g : GlobalInc d) (i j : U) :=
  range (LCTR.CoreOrderAtlas.rightProjection (strictData d)
    (nativeLocalDomain d g i) (nativeLocalDomain d g j))

structure OrderedOutput (d : Input U S V) (g : GlobalInc d) where
  order : Canonical d → Canonical d → Prop
  localChart : ∀ i, ImageAt d.arrival i → NativeLocalQ d g i
  change : ∀ i j, ChangeDomain d g i j → ChangeRange d g i j
  global : Canonical d → GlobalQ d g
  localGlobalMap : ∀ i, NativeLocalQ d g i → GlobalQ d g

def generatedOrdered (d : Input U S V) (g : GlobalInc d) : OrderedOutput d g where
  order := canonicalOrder d
  localChart i := chart d i (global_implies_local_inc d g i)
  change i j := LCTR.CoreOrderAtlas.overlapChange (strictData d)
    (nativeLocalDomain d g i) (nativeLocalDomain d g j)
  global := globalProjection d g
  localGlobalMap i := localGlobal d i (global_implies_local_inc d g i) g

def OrderedValid (d : Input U S V) (g : GlobalInc d) (o : OrderedOutput d g) : Prop :=
  (∀ x y : Tagged d.arrival,
    o.order (canonicalProjection d x) (canonicalProjection d y) ↔
      d.sourceOrder (recover d.arrival d.unique x) (recover d.arrival d.unique y)) ∧
  (∀ i a, o.localChart i a = LCTR.CoreOrderAtlas.projection (strictData d)
    (nativeLocalDomain d g i) (receive d i a)) ∧
  (∀ i j x, o.change i j (imageProjection
    (LCTR.CoreOrderAtlas.leftProjection (strictData d) (nativeLocalDomain d g i) (nativeLocalDomain d g j)) x) =
      imageProjection
        (LCTR.CoreOrderAtlas.rightProjection (strictData d) (nativeLocalDomain d g i) (nativeLocalDomain d g j)) x) ∧
  (∀ x : Tagged d.arrival, o.global (canonicalProjection d x) =
    globalProjection d g (canonicalProjection d x)) ∧
  (∀ i x, o.localGlobalMap i (LCTR.CoreOrderAtlas.projection (strictData d)
    (nativeLocalDomain d g i) x) = globalProjection d g x.val)

theorem generated_ordered_valid (d : Input U S V) (g : GlobalInc d) :
    OrderedValid d g (generatedOrdered d g) :=
  ⟨canonical_order_representatives d,fun _ _ => rfl,
   fun i j => LCTR.CoreOrderAtlas.overlap_change_commutes (strictData d)
     (nativeLocalDomain d g i) (nativeLocalDomain d g j),
   fun _ => rfl,fun i => local_global_commutes d i (global_implies_local_inc d g i) g⟩

theorem ordered_output_unique (d : Input U S V) (g : GlobalInc d)
    (o : OrderedOutput d g) (valid : OrderedValid d g o) : o = generatedOrdered d g := by
  have horder : o.order = (generatedOrdered d g).order := canonical_order_unique d o.order valid.1
  have hlocal : o.localChart = (generatedOrdered d g).localChart := by
    funext i a
    exact valid.2.1 i a
  have hchange : o.change = (generatedOrdered d g).change := by
    funext i j a
    obtain ⟨x,rfl⟩ := imageProjection_surjective
      (LCTR.CoreOrderAtlas.leftProjection (strictData d) (nativeLocalDomain d g i) (nativeLocalDomain d g j)) a
    exact (valid.2.2.1 i j x).trans
      (LCTR.CoreOrderAtlas.overlap_change_commutes (strictData d)
        (nativeLocalDomain d g i) (nativeLocalDomain d g j) x).symm
  have hglobal : o.global = (generatedOrdered d g).global := by
    funext a
    induction a using Quotient.inductionOn with
    | _ x => exact valid.2.2.2.1 x
  have hmap : o.localGlobalMap = (generatedOrdered d g).localGlobalMap := by
    funext i q
    obtain ⟨x,rfl⟩ := LCTR.CoreOrderAtlas.projection_onto (strictData d) (nativeLocalDomain d g i) q
    exact (valid.2.2.2.2 i x).trans
      (local_global_commutes d i (global_implies_local_inc d g i) g x).symm
  have ext : ∀ a b : OrderedOutput d g, a.order=b.order → a.localChart=b.localChart →
      a.change=b.change → a.global=b.global → a.localGlobalMap=b.localGlobalMap → a=b := by
    intro a b
    cases a
    cases b
    intro h1 h2 h3 h4 h5
    cases h1
    cases h2
    cases h3
    cases h4
    cases h5
    rfl
  exact ext o (generatedOrdered d g) horder hlocal hchange hglobal hmap

theorem canonical_ordered_bundle_exists_unique (d : Input U S V) (g : GlobalInc d) :
    ∃! o : OrderedOutput d g, OrderedValid d g o :=
  ⟨generatedOrdered d g,generated_ordered_valid d g,fun o h => ordered_output_unique d g o h⟩

theorem conventional_time_factor (d : Input U S V) (g : GlobalInc d)
    {Y : Type z} [LinearOrder Y] (time : Canonical d → Y)
    (kernel : ∀ x y, time x = time y ↔ Inc (strictData d).lt x y)
    (strict : ∀ x y, time x < time y ↔ (strictData d).lt x y) :
    ∃! F : GlobalQ d g ≃ range time,
      (∀ x, F (globalProjection d g x) = imageProjection time x) ∧
      (∀ a b, (F a).val < (F b).val ↔ globalOrder d g a b) :=
  quotient_factor_exists_unique (strictData d).lt (strictData d).irrefl
    (strictData d).trans g time kernel (fun a b => a < b) strict

theorem conventional_time_coordinate_freedom (d : Input U S V)
    {Y : Type z} {Z : Type w} [LinearOrder Y] [LinearOrder Z]
    (time : Canonical d → Y) (other : Canonical d → Z)
    (kernel : ∀ x y, time x = time y ↔ Inc (strictData d).lt x y)
    (otherKernel : ∀ x y, other x = other y ↔ Inc (strictData d).lt x y)
    (strict : ∀ x y, time x < time y ↔ (strictData d).lt x y)
    (otherStrict : ∀ x y, other x < other y ↔ (strictData d).lt x y) :
    ∃! F : range time ≃o range other,
      ∀ x, F (imageProjection time x) = imageProjection other x :=
  reparametrization_unique (Inc (strictData d).lt) (strictData d).lt time other
    kernel otherKernel strict otherStrict

end
end LCTR.CoreExactCompletion
