import CoreOperationalConfiguration
import CoreComparisonStage
import CorePairTransportFactorization

namespace LCTR.CoreConfigurationComparison
set_option autoImplicit false
open Set LCTR.CoreOperationalConfiguration LCTR.CoreSourceMatch
open LCTR.CoreSourceLoops LCTR.CorePairedComparison LCTR.CoreLocalLoopRealization
open LCTR.CorePairTransportFactorization

def role (r : Fin 2) : SourceRole := if r=0 then .clock else .detector
abbrev Node (x : Configuration) := x.1.reception.Node
abbrev Source (x : Configuration) (r : Fin 2) := Token x.2.schema (role r)
abbrev Received (x : Configuration) (r : Fin 2) (i : Node x) :=
  x.1.reception.receive i (role r)
abbrev arrival (x : Configuration) (r : Fin 2) (i : Node x) :=
  x.2.arrival i (role r)
abbrev PairAt (x : Configuration) (i : Node x) :=
  (r : Fin 2) → ImageAt (arrival x r) i
def L1 (x : Configuration) : Prop := ∀ r, CoreSourceMatch.L1 (arrival x r)

structure PairDatum (x : Configuration) where
  admissible : Node x → Node x → Prop
  joint : ∀ i j, PairAt x i → PairAt x j → Prop

variable (x : Configuration) (d : PairDatum x)

def L2 : Prop := L1 x → ∀ i j, d.admissible i j →
  ∃! _f : Factorization (d.joint i j), True

theorem l2_exact : L2 x d ↔
    (L1 x → ∀ i j, d.admissible i j → Nonempty (Factorization (d.joint i j))) := by
  constructor
  · intro h h1 i j hij
    exact (existence_unique_iff _).mpr (h h1 i j hij)
  · intro h h1 i j hij
    exact (existence_unique_iff _).mp (h h1 i j hij)

variable (h1 : L1 x) (h2 : L2 x d)
noncomputable def factor (i j : Node x) (hij : d.admissible i j) :
    Factorization (d.joint i j) :=
  Classical.choice ((l2_exact x d).mp h2 h1 i j hij)

theorem joint_graph_exact (i j : Node x) (hij : d.admissible i j)
    (a : PairAt x i) (b : PairAt x j) :
    d.joint i j a b ↔ ∃ ha : a ∈ (factor x d h1 h2 i j hij).domain,
      ∀ r, b r = (factor x d h1 h2 i j hij).map r ⟨a r,⟨a,ha,rfl⟩⟩ :=
  (factor x d h1 h2 i j hij).graph a b

def transport (r : Fin 2) (i j : Node x) := component (d.joint i j) r

include h1 h2 in
theorem transport_partial_injection (r : Fin 2) :
    CoreComparisonIntegration.TransportPartialInjection (arrival x r) (transport x d r)
      d.admissible := by
  intro i j hij
  exact ⟨fun a b c hb hc => component_functional _ (factor x d h1 h2 i j hij) r a b c hb hc,
    fun a b c ha hb => component_injective _ (factor x d h1 h2 i j hij) r a b c ha hb⟩

noncomputable def data : RoleData (U:=Node x) (S:=Source x) (V:=Received x) :=
  fun r => {
    arrival := arrival x r
    unique := h1 r
    transport := transport x d r
    admissible := d.admissible
    transportInjective := transport_partial_injection x d h1 h2 r
  }

variable (specs : (r : Fin 2) → Set (Spec (data x d h1 h2 r)))
noncomputable def input : CoreComparisonStage.Input (Node x) (Source x) (Received x) where
  data := data x d h1 h2
  specs := specs
  localRel := fun i => {a | ((a 0).val,(a 1).val) ∈ x.2.comparisonRelation i}
  sourceRel := {a | (a 0,a 1) ∈ x.2.sourceRelation}

theorem arrival_preserved (r : Fin 2) :
    ((input x d h1 h2 specs).data r).arrival = arrival x r := rfl

theorem transport_preserved (r : Fin 2) :
    ((input x d h1 h2 specs).data r).transport = transport x d r := rfl

theorem relations_preserved :
    (∀ i a, a ∈ (input x d h1 h2 specs).localRel i ↔
      ((a 0).val,(a 1).val) ∈ x.2.comparisonRelation i) ∧
    (∀ a, a ∈ (input x d h1 h2 specs).sourceRel ↔ (a 0,a 1) ∈ x.2.sourceRelation) :=
  ⟨fun _ _ => Iff.rfl,fun _ => Iff.rfl⟩

theorem l5_from_configuration : CoreComparisonStage.L5 (input x d h1 h2 specs) := by
  intro i a
  let c := localRecovery (arrival x 0) (h1 0) i (a 0)
  let e := localRecovery (arrival x 1) (h1 1) i (a 1)
  change ((a 0).val,(a 1).val) ∈ x.2.comparisonRelation i ↔
    (c.val,e.val) ∈ x.2.sourceRelation
  have hc := arrival_recovery (arrival x 0) (h1 0) i (a 0)
  have he := arrival_recovery (arrival x 1) (h1 1) i (a 1)
  have compatible := x.2.relationCompatibility i c.val e.val c.property e.property
  change (c.val,e.val) ∈ x.2.sourceRelation ↔
    ((arrival x 0 i).val c.val c.property,(arrival x 1 i).val e.val e.property)
      ∈ x.2.comparisonRelation i at compatible
  rw [hc,he] at compatible
  exact compatible.symm

def RemainingConditions : Prop :=
  CoreComparisonStage.L3 (input x d h1 h2 specs) ∧
  CoreComparisonStage.L4 (input x d h1 h2 specs) ∧
  CoreComparisonStage.L6 (input x d h1 h2 specs) ∧
  CoreComparisonStage.L7 (input x d h1 h2 specs) ∧
  CoreComparisonStage.G (input x d h1 h2 specs)

theorem remaining_iff_operative : RemainingConditions x d h1 h2 specs ↔
    CoreComparisonStage.ResidualOperative (input x d h1 h2 specs) := by
  constructor
  · rintro ⟨a,b,c,e,f⟩
    exact ⟨⟨a,b,l5_from_configuration x d h1 h2 specs,c,e⟩,f⟩
  · rintro ⟨⟨a,b,_,c,e⟩,f⟩
    exact ⟨a,b,c,e,f⟩

variable (h : RemainingConditions x d h1 h2 specs)
include h in
theorem native_output_unique :
    ∃! o : CoreComparisonStage.Output (input x d h1 h2 specs),
      CoreComparisonStage.Valid (input x d h1 h2 specs) o :=
  CoreComparisonStage.unique_generated_output _ ((remaining_iff_operative x d h1 h2 specs).mp h)

theorem native_source_relation_pullback (p : Synchronized (data x d h1 h2)) :
    CorePairedComparison.projection (data x d h1 h2) p ∈
      (CoreComparisonStage.generate (input x d h1 h2 specs) h.1).relation ↔
    ((localRecovery (arrival x 0) (h1 0) p.1 (p.2 0)).val,
     (localRecovery (arrival x 1) (h1 1) p.1 (p.2 1)).val) ∈ x.2.sourceRelation :=
  CoreComparisonStage.generated_source_pullback _
    ((remaining_iff_operative x d h1 h2 specs).mp h) p

include h in
theorem native_local_injective (r : Fin 2) (i : Node x) :
    Function.Injective (CoreComparisonStage.roleProjection (input x d h1 h2 specs) r i) :=
  CoreComparisonStage.generated_local_injective _
    ((remaining_iff_operative x d h1 h2 specs).mp h) r i

end LCTR.CoreConfigurationComparison
