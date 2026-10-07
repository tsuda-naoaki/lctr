import CoreContinuumFailure
import Mathlib.Topology.ContinuousOn

namespace LCTR.CoreContinuumDatum
set_option autoImplicit false
open Set LCTR.CoreTokenGraph LCTR.CoreEvaluation LCTR.CoreContinuumIntegration
open LCTR.CoreContinuumFailure LCTR.CoreContinuumEncoding LCTR.SelectedInputEvaluation
open scoped ENNReal
noncomputable section

 
 
structure MapDatum where
  Domain : Type
  Codomain : Type
  domainTopology : TopologicalSpace Domain
  codomainTopology : TopologicalSpace Codomain
  interval : Set Domain
  samples : Finset interval
  sampleValue : {x : interval // x ∈ samples} → Codomain
  candidate : interval → Codomain
  deviation : Codomain → Codomain → ℝ≥0∞
  tolerance : ℝ≥0∞

def ContinuousMap (m : MapDatum) : Prop :=
  letI := m.domainTopology
  letI := m.codomainTopology
  Continuous m.candidate
def SampleFit (m : MapDatum) : Prop :=
  ∀ x : {x : m.interval // x ∈ m.samples},
    m.deviation (m.candidate x.val) (m.sampleValue x) ≤ m.tolerance
def Extension (maps : Fin 5 → MapDatum) : Prop :=
  ∀ t, ContinuousMap (maps t) ∧ SampleFit (maps t)

structure OrderDatum (m : MapDatum) where
  before : m.Domain → m.Domain → Prop
  after : m.Codomain → m.Codomain → Prop
  strictBefore : IsStrictOrder m.Domain before
  strictAfter : IsStrictOrder m.Codomain after
def ordTag (i : Fin 4) : Fin 5 := ⟨i.val, by omega⟩
def OrderCondition (maps : Fin 5 → MapDatum)
    (orders : (i : Fin 4) → OrderDatum (maps (ordTag i))) : Prop :=
  ∀ i, ∀ x y : (maps (ordTag i)).interval,
    (orders i).before x.val y.val →
      (orders i).after ((maps (ordTag i)).candidate x) ((maps (ordTag i)).candidate y)

 
structure RelationDatum where
  arity : ℕ
  positiveArity : 0 < arity
  Domain : Fin arity → Type
  Codomain : Fin arity → Type
  source : Set ((k : Fin arity) → Domain k)
  candidate : Set ((k : Fin arity) → Codomain k)
  mapping : (k : Fin arity) → Domain k → Codomain k
def RelationCondition (rels : Fin 5 → RelationDatum) : Prop :=
  ∀ t, ∀ x : (k : Fin (rels t).arity) → (rels t).Domain k,
    x ∈ (rels t).source ↔ (fun k => (rels t).mapping k (x k)) ∈ (rels t).candidate

theorem extension_failure_witness (maps : Fin 5 → MapDatum) :
    ¬ Extension maps ↔ ∃ t, ¬ ContinuousMap (maps t) ∨
      ∃ x : {x : (maps t).interval // x ∈ (maps t).samples},
        (maps t).tolerance < (maps t).deviation ((maps t).candidate x.val) ((maps t).sampleValue x) := by
  classical
  simp only [Extension,SampleFit,not_forall,not_and_or,not_le]

theorem order_failure_witness (maps : Fin 5 → MapDatum)
    (orders : (i : Fin 4) → OrderDatum (maps (ordTag i))) :
    ¬ OrderCondition maps orders ↔ ∃ i, ∃ x y : (maps (ordTag i)).interval,
      (orders i).before x.val y.val ∧
        ¬ (orders i).after ((maps (ordTag i)).candidate x) ((maps (ordTag i)).candidate y) := by
  classical
  simp only [OrderCondition,not_forall,exists_prop]

theorem relation_failure_witness (rels : Fin 5 → RelationDatum) :
    ¬ RelationCondition rels ↔ ∃ t, ∃ x : (k : Fin (rels t).arity) → (rels t).Domain k,
      (x ∈ (rels t).source ∧ (fun k => (rels t).mapping k (x k)) ∉ (rels t).candidate) ∨
      (x ∉ (rels t).source ∧ (fun k => (rels t).mapping k (x k)) ∈ (rels t).candidate) := by
  classical
  simp only [RelationCondition,not_forall]
  apply exists_congr
  intro t
  apply exists_congr
  intro x
  tauto

def diameter {Y : Type} (deviation : Y → Y → ℝ≥0∞) (A : Set Y) : ℝ≥0∞ :=
  sSup {r | ∃ x ∈ A, ∃ y ∈ A, r = deviation x y}

theorem diameter_empty {Y : Type} (dev : Y → Y → ℝ≥0∞) : diameter dev ∅ = 0 := by
  simp [diameter]

theorem diameter_bound {Y : Type} (dev : Y → Y → ℝ≥0∞) (A : Set Y) (eps : ℝ≥0∞) :
    diameter dev A ≤ eps ↔ ∀ x ∈ A, ∀ y ∈ A, dev x y ≤ eps := by
  constructor
  · intro h x hx y hy
    have mem : dev x y ∈ {r | ∃ a ∈ A, ∃ b ∈ A, r = dev a b} := ⟨x,hx,y,hy,rfl⟩
    exact le_trans (le_sSup mem) h
  · intro h
    apply sSup_le
    rintro r ⟨x,hx,y,hy,rfl⟩
    exact h x hx y hy

theorem diameter_excess {Y : Type} (dev : Y → Y → ℝ≥0∞) (A : Set Y) (eps : ℝ≥0∞) :
    eps < diameter dev A ↔ ∃ x ∈ A, ∃ y ∈ A, eps < dev x y := by
  classical
  rw [← not_le,diameter_bound]
  simp only [not_forall,not_le,exists_prop]

 
def cellTag (i : Fin 2) : Fin 5 := ⟨i.val+1, by omega⟩
structure CellDatum (maps : Fin 5 → MapDatum) where
  Index : Fin 2 → Type
  cell : (t : Fin 2) → Index t → Set (maps (cellTag t)).interval

def cellImage (maps : Fin 5 → MapDatum) (cells : CellDatum maps)
    (t : Fin 2) (x : cells.Index t) : Set (maps (cellTag t)).Codomain :=
  (maps (cellTag t)).candidate '' cells.cell t x
def cellWidth (maps : Fin 5 → MapDatum) (cells : CellDatum maps) : ℝ≥0∞ :=
  ⨆ t, ⨆ x, diameter (maps (cellTag t)).deviation (cellImage maps cells t x)

theorem cell_width_bound (maps : Fin 5 → MapDatum) (cells : CellDatum maps) (eps : ℝ≥0∞) :
    cellWidth maps cells ≤ eps ↔ ∀ t x, ∀ a ∈ cellImage maps cells t x,
      ∀ b ∈ cellImage maps cells t x, (maps (cellTag t)).deviation a b ≤ eps := by
  simp only [cellWidth,iSup_le_iff,diameter_bound]

theorem cell_width_excess (maps : Fin 5 → MapDatum) (cells : CellDatum maps) (eps : ℝ≥0∞) :
    eps < cellWidth maps cells ↔ ∃ t x, ∃ a ∈ cellImage maps cells t x,
      ∃ b ∈ cellImage maps cells t x, eps < (maps (cellTag t)).deviation a b := by
  classical
  rw [← not_le,cell_width_bound]
  simp only [not_forall,not_le,exists_prop]

theorem width_equals_source_supremum (maps : Fin 5 → MapDatum) (cells : CellDatum maps) :
    cellWidth maps cells = sSup ({0} ∪ {r | ∃ t x,
      r = diameter (maps (cellTag t)).deviation (cellImage maps cells t x)}) := by
  apply le_antisymm
  · apply iSup_le
    intro t
    apply iSup_le
    intro x
    exact le_sSup (Or.inr ⟨t,x,rfl⟩)
  · apply sSup_le
    intro r hr
    rcases hr with hr | ⟨t,x,rfl⟩
    · exact hr ▸ bot_le
    · exact le_iSup_of_le t (le_iSup_of_le x le_rfl)

 
structure RecordDatum where
  Domain : Fin 3 → Type
  Code : Type
  Value : Type
  codeRelation : (t : Fin 3) → Domain t → Code → Prop
  mapping : Code → Value
def recordImage (r : RecordDatum) (t : Fin 3) (x : r.Domain t) : Set r.Value :=
  r.mapping '' {z | r.codeRelation t x z}
def Collision (r : RecordDatum) : Prop :=
  ∃ t, ∃ x y : r.Domain t, x ≠ y ∧ (recordImage r t x ∩ recordImage r t y).Nonempty
def separationDefect (r : RecordDatum) : ℝ≥0∞ := by
  classical
  exact if Collision r then 1 else 0

theorem collision_witness (r : RecordDatum) : Collision r ↔
    ∃ t, ∃ x y : r.Domain t, x ≠ y ∧ ∃ a b : r.Code,
      r.codeRelation t x a ∧ r.codeRelation t y b ∧ r.mapping a = r.mapping b := by
  constructor
  · rintro ⟨t,x,y,ne,v,⟨a,ha,ea⟩,⟨b,hb,eb⟩⟩
    exact ⟨t,x,y,ne,a,b,ha,hb,ea.trans eb.symm⟩
  · rintro ⟨t,x,y,ne,a,b,ha,hb,eq⟩
    exact ⟨t,x,y,ne,r.mapping a,⟨a,ha,rfl⟩,⟨b,hb,eq.symm⟩⟩

theorem separation_defect_excess (r : RecordDatum) (eps : ℝ≥0∞) :
    eps < separationDefect r ↔ Collision r ∧ eps < 1 := by
  classical
  by_cases h : Collision r <;> simp [separationDefect,h]

 
 
 
structure ScalarDatum where
  Carrier : Fin 4 → Type
  order : (i : Fin 4) → PartialOrder (Carrier i)
  value : (i : Fin 4) → Carrier i
  evaluation : (i : Fin 4) → Carrier i → ℝ≥0∞
  monotone : ∀ i, @Monotone (Carrier i) ℝ≥0∞ (order i).toPreorder _ (evaluation i)
def scalar (q : ScalarDatum) (i : Fin 4) : ℝ≥0∞ := q.evaluation i (q.value i)

structure Packet where
  maps : Fin 5 → MapDatum
  orders : (i : Fin 4) → OrderDatum (maps (ordTag i))
  relations : Fin 5 → RelationDatum
  cells : CellDatum maps
  records : RecordDatum
  evaluations : ScalarDatum
  tolerance : Fin 6 → ℝ≥0∞

def firstDefect (p : Packet) (i : Fin 6) : ℝ≥0∞ :=
  ![scalar p.evaluations 0,scalar p.evaluations 1,cellWidth p.maps p.cells,
    separationDefect p.records,scalar p.evaluations 2,scalar p.evaluations 3] i
def Actual (p : Packet) (i : Fin 9) : Prop :=
  if h : i.val < 6 then firstDefect p ⟨i.val,h⟩ ≤ p.tolerance ⟨i.val,h⟩
  else if i.val = 6 then Extension p.maps
  else if i.val = 7 then OrderCondition p.maps p.orders else RelationCondition p.relations
def condition (p : Packet) (i : Fin 9) : Bool := by classical exact decide (Actual p i)

theorem condition_true (p : Packet) (i : Fin 9) : condition p i = true ↔ Actual p i := by
  classical
  simp [condition]

theorem three_record_defects (p : Packet) :
    firstDefect p 1 = scalar p.evaluations 1 ∧
    firstDefect p 2 = cellWidth p.maps p.cells ∧
    firstDefect p 3 = separationDefect p.records := ⟨rfl,rfl,rfl⟩

theorem actual_failure (p : Packet) (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) (matching : ∀ i, c (approxToken i) = condition p i)
    (i : Fin 9) (ready : Ready f e s i) : FA s i ↔ ¬ Actual p i := by
  rw [ready_failure_iff f e c s rec i ready,matching i,← Bool.not_eq_true,condition_true]

theorem extension_failure (p : Packet) (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) (matching : ∀ i, c (approxToken i) = condition p i)
    (ready : Ready f e s 6) : FA s 6 ↔ ¬ Extension p.maps := by
  simpa [Actual] using actual_failure p f e c s rec matching 6 ready

theorem order_failure (p : Packet) (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) (matching : ∀ i, c (approxToken i) = condition p i)
    (ready : Ready f e s 7) : FA s 7 ↔ ¬ OrderCondition p.maps p.orders := by
  simpa [Actual] using actual_failure p f e c s rec matching 7 ready

theorem relation_failure (p : Packet) (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) (matching : ∀ i, c (approxToken i) = condition p i)
    (ready : Ready f e s 8) : FA s 8 ↔ ¬ RelationCondition p.relations := by
  simpa [Actual] using actual_failure p f e c s rec matching 8 ready

theorem width_failure (p : Packet) (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) (matching : ∀ i, c (approxToken i) = condition p i)
    (ready : Ready f e s 2) : FA s 2 ↔ p.tolerance 2 < cellWidth p.maps p.cells := by
  have h := actual_failure p f e c s rec matching 2 ready
  simpa [Actual,firstDefect,not_le] using h

theorem separation_failure (p : Packet) (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) (matching : ∀ i, c (approxToken i) = condition p i)
    (ready : Ready f e s 3) : FA s 3 ↔ Collision p.records ∧ p.tolerance 3 < 1 := by
  have h := actual_failure p f e c s rec matching 3 ready
  have k : FA s 3 ↔ p.tolerance 3 < separationDefect p.records := by
    simpa [Actual,firstDefect,not_le] using h
  exact k.trans (separation_defect_excess _ _)

theorem zero_separation_tolerance (p : Packet) (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) (matching : ∀ i, c (approxToken i) = condition p i)
    (ready : Ready f e s 3) (zero : p.tolerance 3 = 0) : FA s 3 ↔ Collision p.records := by
  rw [separation_failure p f e c s rec matching ready,zero]
  simp

theorem unit_separation_tolerance (p : Packet) (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s) (matching : ∀ i, c (approxToken i) = condition p i)
    (ready : Ready f e s 3) (unit : 1 ≤ p.tolerance 3) : ¬ FA s 3 := by
  rw [separation_failure p f e c s rec matching ready]
  exact fun h => (not_lt_of_ge unit) h.2

end
end LCTR.CoreContinuumDatum
