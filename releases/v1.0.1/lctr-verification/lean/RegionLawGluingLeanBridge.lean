import Mathlib.Data.Set.Basic
import LCTR.LawCandidateRelationPartialOutputMapCurrentPaper
import LCTR.GenerationClosure

namespace LCTR.RegionLawGluingLeanBridgeV1

open LCTR

universe u v w z

namespace Law










structure LawEvalDat (T : Type u) where
  LawIdx : Type v
  InValSp : LawIdx → Type w
  OutValSp : LawIdx → Type z
  EvalDom : (a : LawIdx) → Set (T × InValSp a)
  CandRel :
    (a : LawIdx) →
      Set ({p : T × InValSp a // p ∈ EvalDom a} × OutValSp a)

abbrev EvalPoint {T : Type u} (d : LawEvalDat T) (a : d.LawIdx) :=
  {p : T × d.InValSp a // p ∈ d.EvalDom a}

def relation {T : Type u} (d : LawEvalDat T) (a : d.LawIdx)
    (x : EvalPoint d a) (y : d.OutValSp a) : Prop :=
  (x, y) ∈ d.CandRel a

 
def CandRelRightUnique {T : Type u} (d : LawEvalDat T) : Prop :=
  ∀ a x y₀ y₁,
    relation d a x y₀ →
    relation d a x y₁ →
    y₀ = y₁





abbrev CandRelDom {T : Type u} (d : LawEvalDat T) (a : d.LawIdx) :=
  {x : EvalPoint d a // ∃ y, relation d a x y}

 
def PointwiseGraph {T : Type u} (d : LawEvalDat T) (a : d.LawIdx)
    (f : CandRelDom d a → d.OutValSp a) : Prop :=
  ∀ pair : CandRelDom d a × d.OutValSp a,
    relation d a pair.1.1 pair.2 ↔ pair.2 = f pair.1

 
def GraphSet {T : Type u} (d : LawEvalDat T) (a : d.LawIdx)
    (f : CandRelDom d a → d.OutValSp a) :
    Set (EvalPoint d a × d.OutValSp a) :=
  {pair | ∃ x : CandRelDom d a, pair = (x.1, f x)}

theorem evalPoint_is_in_actual_evalDom
    {T : Type u} (d : LawEvalDat T) (a : d.LawIdx)
    (x : EvalPoint d a) :
    x.1 ∈ d.EvalDom a :=
  x.2

theorem candRelDom_is_exact_relation_domain
    {T : Type u} (d : LawEvalDat T) (a : d.LawIdx)
    (x : EvalPoint d a) :
    (∃ y, relation d a x y) ↔
      ∃ dx : CandRelDom d a, dx.1 = x := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨⟨x, y, hy⟩, rfl⟩
  · rintro ⟨dx, rfl⟩
    exact dx.2

theorem graph_set_equality_of_pointwise
    {T : Type u} (d : LawEvalDat T) (a : d.LawIdx)
    (f : CandRelDom d a → d.OutValSp a)
    (hGraph : PointwiseGraph d a f) :
    d.CandRel a = GraphSet d a f := by
  ext pair
  constructor
  · intro hRel
    let dx : CandRelDom d a :=
      ⟨pair.1, ⟨pair.2, by simpa [relation] using hRel⟩⟩
    have hy : pair.2 = f dx :=
      (hGraph (dx, pair.2)).mp (by simpa [relation, dx] using hRel)
    refine ⟨dx, ?_⟩
    apply Prod.ext
    · rfl
    · exact hy
  · rintro ⟨dx, rfl⟩
    have hRel : relation d a dx.1 (f dx) :=
      (hGraph (dx, f dx)).mpr rfl
    simpa [relation] using hRel







theorem law_candidate_relation_partial_output_map
    {T : Type u} (d : LawEvalDat T)
    (hK : CandRelRightUnique d)
    (a : d.LawIdx) :
    ∃ outputMap : CandRelDom d a → d.OutValSp a,
      PointwiseGraph d a outputMap ∧
      ∀ competingMap,
        PointwiseGraph d a competingMap →
        competingMap = outputMap := by
  exact
    LCTR.CurrentPaperCorrespondence.law_candidate_relation_partial_output_map
      (relation d a) (hK a)

 
theorem law_candidate_relation_literal_graph
    {T : Type u} (d : LawEvalDat T)
    (hK : CandRelRightUnique d)
    (a : d.LawIdx) :
    ∃ outputMap : CandRelDom d a → d.OutValSp a,
      d.CandRel a = GraphSet d a outputMap ∧
      ∀ competingMap,
        PointwiseGraph d a competingMap →
        competingMap = outputMap := by
  rcases law_candidate_relation_partial_output_map d hK a with
    ⟨outputMap, hGraph, hUnique⟩
  exact ⟨outputMap, graph_set_equality_of_pointwise d a outputMap hGraph, hUnique⟩

 
theorem empty_relation_has_empty_domain
    {T : Type u} (d : LawEvalDat T) (a : d.LawIdx)
    (hEmpty : d.CandRel a = ∅) :
    ∀ x : CandRelDom d a, False := by
  intro x
  rcases x.2 with ⟨y, hy⟩
  have hmem : (x.1, y) ∈ d.CandRel a := by
    simpa [relation] using hy
  rw [hEmpty] at hmem
  exact hmem





theorem no_graph_if_right_uniqueness_fails
    {T : Type u} (d : LawEvalDat T) (a : d.LawIdx)
    (x : EvalPoint d a) (y₀ y₁ : d.OutValSp a)
    (h₀ : relation d a x y₀)
    (h₁ : relation d a x y₁)
    (hne : y₀ ≠ y₁) :
    ¬ ∃ f : CandRelDom d a → d.OutValSp a, PointwiseGraph d a f := by
  rintro ⟨f, hGraph⟩
  let dx : CandRelDom d a := ⟨x, ⟨y₀, h₀⟩⟩
  have e₀ : y₀ = f dx := (hGraph (dx, y₀)).mp h₀
  have e₁ : y₁ = f dx := (hGraph (dx, y₁)).mp h₁
  exact hne (e₀.trans e₁.symm)

end Law

namespace Gluing





structure PaperData (Expr : Type u) where
  componentInput : Set Expr
  operativeExpr : Expr
  local7Expr : Expr
  notGlobalGluingExpr : Expr
  notOperativeExpr : Expr
  representationCondition : Fin 4 → Expr
  Out : Fin 4 → Set Expr

def PriorOut {Expr : Type u} (d : PaperData Expr) (k : Fin 4) : Set Expr :=
  fun e => ∃ j : Fin 4, j.val < k.val ∧ d.Out j e






def Req {Expr : Type u} (d : PaperData Expr) (k : Fin 4) : Set Expr :=
  fun e =>
    d.componentInput e ∨
    e = d.operativeExpr ∨
    (0 < k.val ∧
      (e = d.representationCondition k ∨ PriorOut d k e))

 
def Dep {Expr : Type u} (d : PaperData Expr) :
    LCTR.GenerationClosure.Family (LCTR.GenerationClosure.Rule Expr) :=
  LCTR.GenerationClosure.LayerRules (Req d) d.Out

 
def OutNotG {Expr : Type u} (d : PaperData Expr) : Set Expr :=
  fun e => ∃ k : Fin 4, d.Out k e





def Context {Expr : Type u} (d : PaperData Expr) : Set Expr :=
  fun e =>
    d.componentInput e ∨
    e = d.local7Expr ∨
    e = d.notGlobalGluingExpr ∨
    e = d.notOperativeExpr





def SafeSet {Expr : Type u} (d : PaperData Expr) : Set Expr :=
  fun e => ¬ OutNotG d e ∧ e ≠ d.operativeExpr








def ContextTyping {Expr : Type u} (d : PaperData Expr) : Prop :=
  ∀ e, Context d e → SafeSet d e

 
def GenDef {Expr : Type u} (d : PaperData Expr) (y : Expr) : Prop :=
  LCTR.GenerationClosure.Closure (Dep d) (Context d) y





def OperativePredicateDefinition
    (local7 globalGluing operative : Prop) : Prop :=
  (local7 ∧ globalGluing) ↔ operative

theorem req_contains_operative
    {Expr : Type u} (d : PaperData Expr) (k : Fin 4) :
    Req d k d.operativeExpr := by
  exact Or.inr (Or.inl rfl)

theorem dep_rule_iff
    {Expr : Type u} (d : PaperData Expr)
    (r : LCTR.GenerationClosure.Rule Expr) :
    Dep d r ↔
      ∃ k : Fin 4, r.premises = Req d k ∧ d.Out k r.conclusion := by
  rfl

theorem genDef_is_least_closure_membership
    {Expr : Type u} (d : PaperData Expr) (y : Expr) :
    GenDef d y ↔
      ∀ s : LCTR.GenerationClosure.Family Expr,
        (∀ x, Context d x → s x) →
        LCTR.GenerationClosure.Closed (Dep d) s →
        s y := by
  rfl

 
theorem safeSet_closed
    {Expr : Type u} (d : PaperData Expr) :
    LCTR.GenerationClosure.Closed (Dep d) (SafeSet d) := by
  intro r hr hPrem
  rcases (dep_rule_iff d r).mp hr with ⟨k, hReq, _⟩
  have hGatePrem : r.premises d.operativeExpr := by
    rw [hReq]
    exact req_contains_operative d k
  have hGateSafe := hPrem d.operativeExpr hGatePrem
  exact False.elim (hGateSafe.2 rfl)

 
theorem closure_subset_safeSet
    {Expr : Type u} (d : PaperData Expr)
    (hTyped : ContextTyping d) :
    ∀ y, GenDef d y → SafeSet d y := by
  exact LCTR.GenerationClosure.least_closed
    (Dep d) (Context d) (SafeSet d) hTyped (safeSet_closed d)

theorem canonical_output_not_generated
    {Expr : Type u} (d : PaperData Expr)
    (hTyped : ContextTyping d)
    (k : Fin 4) (y : Expr) (hy : d.Out k y) :
    ¬ GenDef d y := by
  intro hGen
  have hSafe := closure_subset_safeSet d hTyped y hGen
  exact hSafe.1 ⟨k, hy⟩

 
theorem operative_failure_from_definition
    (local7 globalGluing operative : Prop)
    (hDef : OperativePredicateDefinition local7 globalGluing operative)
    (hLocal : local7) (hFailure : ¬ globalGluing) :
    ¬ operative := by
  intro hOperative
  exact hFailure ((hDef.mpr hOperative).2)








theorem global_gluing_failure_blocks_representation_entry
    {Expr : Type u} (d : PaperData Expr)
    (local7 globalGluing operative : Prop)
    (hDef : OperativePredicateDefinition local7 globalGluing operative)
    (hLocal : local7)
    (hFailure : ¬ globalGluing)
    (hTyped : ContextTyping d) :
    ¬ operative ∧
      ∀ k : Fin 4, ∀ y : Expr, d.Out k y → ¬ GenDef d y := by
  constructor
  · exact operative_failure_from_definition local7 globalGluing operative
      hDef hLocal hFailure
  · intro k y hy
    exact canonical_output_not_generated d hTyped k y hy





theorem supplied_output_remains_generated
    {Expr : Type u} (d : PaperData Expr)
    (k : Fin 4) (y : Expr) (hy : d.Out k y) :
    LCTR.GenerationClosure.Closure
      (Dep d)
      (fun e => Context d e ∨ e = y)
      y := by
  have _ := hy
  exact LCTR.GenerationClosure.input_mem
    (Dep d) (fun e => Context d e ∨ e = y) (Or.inr rfl)

end Gluing

#print axioms Law.law_candidate_relation_partial_output_map
#print axioms Law.law_candidate_relation_literal_graph
#print axioms Law.empty_relation_has_empty_domain
#print axioms Law.no_graph_if_right_uniqueness_fails
#print axioms Gluing.closure_subset_safeSet
#print axioms Gluing.global_gluing_failure_blocks_representation_entry
#print axioms Gluing.supplied_output_remains_generated

end LCTR.RegionLawGluingLeanBridgeV1
