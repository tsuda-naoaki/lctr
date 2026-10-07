import CoreRecordCells
import CoreRepresentationStages
import Mathlib.Topology.Order.Basic

namespace LCTR.CoreContinuumInput
open Set LCTR.CoreExactStructure LCTR.CoreRepresentationStages LCTR.CoreRecordCells
open LCTR.CoreAffineFrequency
universe u v w z a b t
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

structure Granularity (KC : Type u) (KD : Type v) (Stab : Type w)
    (Disc : Type z) (Coupl : Type a) [Zero KC] [LE KC] [Zero KD] [LE KD] where
  countStep : {x : KC // 0 ≤ x}
  stability : Stab
  cellWidth : {x : KD // 0 ≤ x}
  discrimination : Disc
  coupling : Coupl

variable {KC : Type u} {KD : Type v} {Stab : Type w} {Disc : Type z} {Coupl : Type a}
variable [Field KC] [LinearOrder KC] [IsStrictOrderedRing KC]
variable [Field KD] [LinearOrder KD] [IsStrictOrderedRing KD]

def granularityTuple (g : Granularity KC KD Stab Disc Coupl) :=
  (g.countStep,g.stability,g.cellWidth,g.discrimination,g.coupling)

omit [IsStrictOrderedRing KC] [IsStrictOrderedRing KD] in
theorem granularity_components (g : Granularity KC KD Stab Disc Coupl) :
    0 ≤ g.countStep.val ∧ 0 ≤ g.cellWidth.val ∧ Nonempty Stab ∧ Nonempty Disc ∧ Nonempty Coupl :=
  ⟨g.countStep.property,g.cellWidth.property,⟨g.stability⟩,⟨g.discrimination⟩,⟨g.coupling⟩⟩

omit [IsStrictOrderedRing KC] [IsStrictOrderedRing KD] in
theorem granularity_tuple_components (g : Granularity KC KD Stab Disc Coupl) :
    (granularityTuple g).1 = g.countStep ∧ (granularityTuple g).2.1 = g.stability ∧
    (granularityTuple g).2.2.1 = g.cellWidth ∧
    (granularityTuple g).2.2.2.1 = g.discrimination ∧ (granularityTuple g).2.2.2.2 = g.coupling :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

abbrev StepWindow {Q : Type b} (r : Q → Q → Prop) := {x : Window Q r // x.k1 = x.k0+1}

omit [LinearOrder KC] [IsStrictOrderedRing KC] in
theorem step_count_one {Q : Type b} {r : Q → Q → Prop} (x : StepWindow r) :
    (countDifference x.val : KC) = 1 := by
  simp only [countDifference,x.property,Nat.add_sub_cancel_left,Nat.cast_one]

theorem step_width_positive {Q : Type b} {PC : Type t} [LinearOrder PC]
    {r : Q → Q → Prop} (A : AffineData KC PC) (embed : Q → PC)
    (strict : ∀ x y, r x y ↔ embed x < embed y) (x : StepWindow r) :
    0 < coordinateDifference A embed x.val := coordinate_difference_positive A embed strict x.val

def countEvaluationSource {Q : Type b} {PC : Type t} [LinearOrder PC]
    {r : Q → Q → Prop} (A : AffineData KC PC) (embed : Q → PC)
    (g : Granularity KC KD Stab Disc Coupl) :=
  ((fun x : StepWindow r => coordinateDifference A embed x.val),g.countStep)

omit [IsStrictOrderedRing KD] in
theorem count_evaluation_source_exact {Q : Type b} {PC : Type t} [LinearOrder PC]
    {r : Q → Q → Prop} (A : AffineData KC PC) (embed : Q → PC)
    (g : Granularity KC KD Stab Disc Coupl) :
    (countEvaluationSource (r:=r) A embed g).1 =
      (fun x : StepWindow r => coordinateDifference A embed x.val) ∧
    (countEvaluationSource (r:=r) A embed g).2 = g.countStep := ⟨rfl,rfl⟩

inductive EvalIndex where
  | countStep | stability | cellWidth | discrimination | coupling | orderStability
  deriving DecidableEq

theorem evaluation_indices_exhaustive (k : EvalIndex) :
    k = .countStep ∨ k = .stability ∨ k = .cellWidth ∨ k = .discrimination ∨
      k = .coupling ∨ k = .orderStability := by cases k <;> simp

structure Evaluation where
  Carrier : Type u
  order : PartialOrder Carrier
  least : Carrier
  least_bound : ∀ x, order.le least x
  value : Carrier
  tolerance : Carrier

def evaluationPass (e : Evaluation) : Prop := e.order.le e.value e.tolerance

theorem evaluation_component_contract (e : Evaluation) :
    Nonempty e.Carrier ∧
    (∀ x, e.order.le e.least x) ∧
    (evaluationPass e ↔ e.order.le e.value e.tolerance) :=
  ⟨⟨e.least⟩,e.least_bound,Iff.rfl⟩

def evaluationFromSource {X : Type v} (source : X) (carrier : Type u)
    (order : PartialOrder carrier) (least : carrier) (least_bound : ∀ x, order.le least x)
    (evaluate : X → carrier) (tolerance : carrier) : Evaluation :=
  ⟨carrier,order,least,least_bound,evaluate source,tolerance⟩

theorem evaluation_uses_source {X : Type v} (source : X) (carrier : Type u)
    (order : PartialOrder carrier) (least : carrier) (least_bound : ∀ x, order.le least x)
    (evaluate : X → carrier) (tolerance : carrier) :
    (evaluationFromSource source carrier order least least_bound evaluate tolerance).value =
      evaluate source := rfl

def evaluationFamily (count : Evaluation.{u}) (remaining : EvalIndex → Evaluation.{u}) :
    EvalIndex → Evaluation.{u}
  | .countStep => count
  | k => remaining k

theorem evaluation_family_count (count : Evaluation.{u}) (remaining : EvalIndex → Evaluation.{u}) :
    evaluationFamily count remaining .countStep = count := rfl

theorem evaluation_family_other (count : Evaluation.{u}) (remaining : EvalIndex → Evaluation.{u})
    (k : EvalIndex) (h : k ≠ .countStep) : evaluationFamily count remaining k = remaining k := by
  cases k <;> simp_all [evaluationFamily]

variable {U : Type u} {C : Type v} {D : Type w} {VC VD : U → Type z}
variable {PC : Type a} {PD : Type b} [LinearOrder PC] [LinearOrder PD]

def representationFromStage (p : Base U C VC) (h : Third p)
    (embed : GlobalQ (atFirst p h.second.first) h.globalInc → PC)
    (strict : ∀ x y, embed x < embed y ↔ globalOrder (atFirst p h.second.first) h.globalInc x y) :
    Representation (atFirst p h.second.first) PC := ⟨h.globalInc,embed,strict⟩

theorem stage_to_coordinate_factorization (p : Base U C VC) (h : Third p)
    (embed : GlobalQ (atFirst p h.second.first) h.globalInc → PC)
    (strict : ∀ x y, embed x < embed y ↔ globalOrder (atFirst p h.second.first) h.globalInc x y)
    (x : Canonical (atFirst p h.second.first)) :
    represented (atFirst p h.second.first) (representationFromStage p h embed strict).globalInc
      (representationFromStage p h embed strict).embedding x =
        embed (globalProjection (atFirst p h.second.first) h.globalInc x) := rfl

def coordinateCandidate (d : Input U D VD) (r : Representation d PD) :=
  (Preorder.topology PD, represented d r.globalInc r.embedding)

theorem coordinate_candidate_topology (d : Input U D VD) (r : Representation d PD) :
    (coordinateCandidate d r).1 =
      TopologicalSpace.generateFrom {s | ∃ a : PD, s = Ioi a ∨ s = Iio a} := rfl

theorem coordinate_candidate_map (d : Input U D VD) (r : Representation d PD) :
    (coordinateCandidate d r).2 = r.embedding ∘ globalProjection d r.globalInc := rfl

def generatedInput (c : Input U C VC) (cr : Representation c PC)
    (d : Input U D VD) (dr : Representation d PD) (W : D → Set D) (rel : C → D → Prop)
    (AC : AffineData KC PC) (AD : AffineData KD PD)
    (g : Granularity KC KD Stab Disc Coupl) (e : EvalIndex → Evaluation.{t}) :=
  ((AC,AD),g,e,
    (decide (widthAdmissible d dr W AD g.cellWidth),decide (separates c cr.globalInc d dr W rel)),
    (coordinateCandidate c cr,coordinateCandidate d dr))

theorem generated_input_retains_inputs (c : Input U C VC) (cr : Representation c PC)
    (d : Input U D VD) (dr : Representation d PD) (W : D → Set D) (rel : C → D → Prop)
    (AC : AffineData KC PC) (AD : AffineData KD PD)
    (g : Granularity KC KD Stab Disc Coupl) (e : EvalIndex → Evaluation.{t}) :
    (generatedInput c cr d dr W rel AC AD g e).1 = (AC,AD) ∧
    (generatedInput c cr d dr W rel AC AD g e).2.1 = g ∧
    (generatedInput c cr d dr W rel AC AD g e).2.2.1 = e := ⟨rfl,rfl,rfl⟩

theorem generated_record_truths_exact (c : Input U C VC) (cr : Representation c PC)
    (d : Input U D VD) (dr : Representation d PD) (W : D → Set D) (rel : C → D → Prop)
    (AC : AffineData KC PC) (AD : AffineData KD PD)
    (g : Granularity KC KD Stab Disc Coupl) (e : EvalIndex → Evaluation.{t}) :
    ((generatedInput c cr d dr W rel AC AD g e).2.2.2.1.1 = true ↔
      widthAdmissible d dr W AD g.cellWidth) ∧
    ((generatedInput c cr d dr W rel AC AD g e).2.2.2.1.2 = true ↔
      separates c cr.globalInc d dr W rel) := by
  simp only [generatedInput,decide_eq_true_eq,and_self]

theorem generated_coordinate_candidates_exact (c : Input U C VC) (cr : Representation c PC)
    (d : Input U D VD) (dr : Representation d PD) (W : D → Set D) (rel : C → D → Prop)
    (AC : AffineData KC PC) (AD : AffineData KD PD)
    (g : Granularity KC KD Stab Disc Coupl) (e : EvalIndex → Evaluation.{t}) :
    (generatedInput c cr d dr W rel AC AD g e).2.2.2.2 =
      (coordinateCandidate c cr,coordinateCandidate d dr) := rfl

variable {Expr : Type u}

def ClosedUnder (dep : Set (Set Expr × Expr)) (S : Set Expr) : Prop :=
  ∀ rule ∈ dep, rule.1 ⊆ S → rule.2 ∈ S

def generationClosure (dep : Set (Set Expr × Expr)) (inputs : Set Expr) : Set Expr :=
  ⋂₀ {S | inputs ⊆ S ∧ ClosedUnder dep S}

theorem closure_contains_inputs (dep : Set (Set Expr × Expr)) (inputs : Set Expr) :
    inputs ⊆ generationClosure dep inputs := by
  intro x hx S hS
  exact hS.1 hx

theorem closure_is_closed (dep : Set (Set Expr × Expr)) (inputs : Set Expr) :
    ClosedUnder dep (generationClosure dep inputs) := by
  intro rule hr hs S hS
  exact hS.2 rule hr (fun x hx => hs hx S hS)

theorem closure_is_least (dep : Set (Set Expr × Expr)) (inputs S : Set Expr)
    (includes : inputs ⊆ S) (closed : ClosedUnder dep S) : generationClosure dep inputs ⊆ S :=
  fun _ hx => hx S ⟨includes,closed⟩

theorem tuple_generation_export (inputs : Set Expr) (tuple : Expr) :
    tuple ∈ generationClosure {(inputs,tuple)} inputs :=
  closure_is_closed {(inputs,tuple)} inputs (inputs,tuple) (Set.mem_singleton _) 
    (closure_contains_inputs {(inputs,tuple)} inputs)

theorem no_rule_adds_nothing (inputs : Set Expr) : generationClosure ∅ inputs = inputs := by
  apply Set.Subset.antisymm
  · exact closure_is_least ∅ inputs inputs (Set.Subset.rfl) (fun _ h => False.elim h)
  · exact closure_contains_inputs ∅ inputs

inductive TupleExpr (I : Type u) (Val : I → Type v) where
  | component (i : I) (value : Val i)
  | tuple (value : (i : I) → Val i)

def tupleInputs {I : Type u} {Val : I → Type v} (value : (i : I) → Val i) :
    Set (TupleExpr I Val) := Set.range (fun i => TupleExpr.component i (value i))

theorem tuple_inputs_exact {I : Type u} {Val : I → Type v} (value : (i : I) → Val i)
    (x : TupleExpr I Val) : x ∈ tupleInputs value ↔
      ∃ i, TupleExpr.component i (value i) = x := Iff.rfl

theorem typed_tuple_generation_export {I : Type u} {Val : I → Type v}
    (value : (i : I) → Val i) :
    TupleExpr.tuple value ∈ generationClosure {(tupleInputs value,TupleExpr.tuple value)}
      (tupleInputs value) := tuple_generation_export (tupleInputs value) (TupleExpr.tuple value)

end
end LCTR.CoreContinuumInput
