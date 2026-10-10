import CoreEngineeringDataInterfaces

namespace LCTR.CoreCommunicationDataInterfaces
set_option autoImplicit false
open Set
open LCTR.CoreEngineeringDataInterfaces
open scoped ENNReal

structure Graph (V E : Type) where
  vertices : Set V
  edges : Set E
  finiteVertices : vertices.Finite
  finiteEdges : edges.Finite
  src : E → V
  tgt : E → V
  endpoints : ∀ e ∈ edges, src e ∈ vertices ∧ tgt e ∈ vertices

variable {V E P WC WD : Type}

structure Walk (g : Graph V E) where
  length : ℕ
  positive : 0 < length
  edge : Fin length → E
  typed : ∀ i, edge i ∈ g.edges
  adjacent : ∀ (i : ℕ) (h : i + 1 < length),
    g.tgt (edge ⟨i, by omega⟩) = g.src (edge ⟨i + 1, h⟩)

def first (g : Graph V E) (w : Walk g) : V := g.src (w.edge ⟨0, w.positive⟩)
def last (g : Graph V E) (w : Walk g) : V :=
  g.tgt (w.edge ⟨w.length - 1, by have := w.positive; omega⟩)
def closed (g : Graph V E) (w : Walk g) : Prop := first g w = last g w
def reachable (g : Graph V E) (v u : V) : Prop :=
  ∃ w : Walk g, first g w = v ∧ last g w = u
def linked (g : Graph V E) (v u : V) : Prop := reachable g v u ∨ reachable g u v

theorem finite_graph (g : Graph V E) : g.vertices.Finite ∧ g.edges.Finite :=
  ⟨g.finiteVertices, g.finiteEdges⟩
theorem walk_positive (g : Graph V E) (w : Walk g) : 0 < w.length := w.positive
theorem walk_adjacent (g : Graph V E) (w : Walk g) (i : ℕ) (h : i + 1 < w.length) :
    g.tgt (w.edge ⟨i, by omega⟩) = g.src (w.edge ⟨i + 1, h⟩) := w.adjacent i h
theorem walk_endpoints (g : Graph V E) (w : Walk g) :
    first g w ∈ g.vertices ∧ last g w ∈ g.vertices :=
  ⟨(g.endpoints _ (w.typed _)).1, (g.endpoints _ (w.typed _)).2⟩
theorem closed_exact (g : Graph V E) (w : Walk g) :
    closed g w ↔ first g w = last g w := Iff.rfl
theorem linked_exact (g : Graph V E) (v u : V) :
    linked g v u ↔ ∃ w : Walk g,
      (first g w = v ∧ last g w = u) ∨ (first g w = u ∧ last g w = v) := by
  simp only [linked, reachable, exists_or]
theorem linked_symmetric (g : Graph V E) (v u : V) : linked g v u ↔ linked g u v :=
  or_comm
theorem linked_vertices (g : Graph V E) (v u : V) (h : linked g v u) :
    v ∈ g.vertices ∧ u ∈ g.vertices := by
  rcases h with ⟨w,hv,hu⟩ | ⟨w,hu,hv⟩
  · simpa [hv,hu] using walk_endpoints g w
  · exact ⟨hv ▸ (walk_endpoints g w).2, hu ▸ (walk_endpoints g w).1⟩

def singleWalk (g : Graph V E) (e : E) (h : e ∈ g.edges) : Walk g where
  length := 1
  positive := by decide
  edge := fun _ => e
  typed := fun _ => h
  adjacent := by intro i hi; omega
theorem single_edge_links (g : Graph V E) (e : E) (h : e ∈ g.edges) :
    linked g (g.src e) (g.tgt e) := Or.inl ⟨singleWalk g e h, rfl, rfl⟩
theorem empty_edges_no_links (g : Graph V E) (h : g.edges = ∅) (v u : V) :
    ¬ linked g v u := by
  intro hl
  rcases (linked_exact g v u).mp hl with ⟨w,_⟩
  have he := w.typed ⟨0,w.positive⟩
  simp [h] at he
theorem one_way_is_sufficient (g : Graph V E) (v u : V)
    (forward : reachable g v u) (backward : ¬ reachable g u v) :
    linked g v u ∧ ¬ (reachable g v u ∧ reachable g u v) :=
  ⟨Or.inl forward, fun h => backward h.2⟩

inductive EdgeKind where
  | sourceId | transport
  deriving DecidableEq
abbrev Probability := {x : ℝ // 0 ≤ x ∧ x ≤ 1}
structure Metric (E : Type) where
  distance : E → Interval ENNReal
  delay : E → Interval ENNReal
  loss : E → Interval Probability
  bandwidth : E → Interval ENNReal
  jitter : E → Interval ENNReal
  integrity : E → Interval Probability
structure Data (g : Graph V E) (P WC WD : Type) where
  carrier : E → P
  edgeKind : E → EdgeKind
  wordC : Walk g → Option WC
  wordD : Walk g → Option WD
  metric : Metric E
def wordDomain {g : Graph V E} {W : Type} (f : Walk g → Option W) : Set (Walk g) :=
  {w | ∃ x, f w = some x}
theorem word_domain_exact (g : Graph V E) (d : Data g P WC WD) (w : Walk g) :
    w ∈ wordDomain d.wordC ↔ ∃ x, d.wordC w = some x := Iff.rfl
theorem absent_word_allowed (g : Graph V E) (w : Walk g) :
    w ∉ wordDomain (fun _ : Walk g => (none : Option WC)) := by
  simp [wordDomain]
theorem word_single_valued (g : Graph V E) (d : Data g P WC WD) (w : Walk g) (x y : WC)
    (hx : d.wordC w = some x) (hy : d.wordC w = some y) : x = y :=
  Option.some.inj (hx.symm.trans hy)
theorem probability_bounds (x : Probability) : 0 ≤ x.val ∧ x.val ≤ 1 := x.property
theorem metric_intervals (m : Metric E) (e : E) :
    (m.distance e).lower ≤ (m.distance e).upper ∧
    (m.delay e).lower ≤ (m.delay e).upper ∧
    (m.loss e).lower ≤ (m.loss e).upper ∧
    (m.bandwidth e).lower ≤ (m.bandwidth e).upper ∧
    (m.jitter e).lower ≤ (m.jitter e).upper ∧
    (m.integrity e).lower ≤ (m.integrity e).upper :=
  ⟨(m.distance e).ordered, (m.delay e).ordered, (m.loss e).ordered,
    (m.bandwidth e).ordered, (m.jitter e).ordered, (m.integrity e).ordered⟩
theorem edge_kind_exhaustive (g : Graph V E) (d : Data g P WC WD) (e : E) :
    d.edgeKind e = .sourceId ∨ d.edgeKind e = .transport := by
  cases h : d.edgeKind e <;> simp

def distributed {X I O Z : Type} (inputOf : X → I) (operative : X → Prop) (carrierAt : Z → V)
    (pair : Fin 2 → I × O × Z) : Prop :=
  pairSpec inputOf operative (pair 0) (pair 1) ∧ carrierAt (pair 0).2.2 ≠ carrierAt (pair 1).2.2
theorem distributed_exact {X I O Z : Type} (inputOf : X → I) (operative : X → Prop) (carrierAt : Z → V)
    (pair : Fin 2 → I × O × Z) :
    distributed inputOf operative carrierAt pair ↔
    pairSpec inputOf operative (pair 0) (pair 1) ∧ carrierAt (pair 0).2.2 ≠ carrierAt (pair 1).2.2 := Iff.rfl

def communicationContext {X I O Z L : Type} (inputOf : X → I) (operative : X → Prop)
    (carrierAt : Z → V) (pair : Fin 2 → I × O × Z) (_scale : L) (g : Graph V E) : Prop :=
  distributed inputOf operative carrierAt pair ∧
  (∀ k, carrierAt (pair k).2.2 ∈ g.vertices) ∧
  linked g (carrierAt (pair 0).2.2) (carrierAt (pair 1).2.2)
theorem context_exact {X I O Z L : Type} (inputOf : X → I) (operative : X → Prop)
    (carrierAt : Z → V) (pair : Fin 2 → I × O × Z) (scale : L) (g : Graph V E) :
    communicationContext inputOf operative carrierAt pair scale g ↔
    distributed inputOf operative carrierAt pair ∧
    (∀ k, carrierAt (pair k).2.2 ∈ g.vertices) ∧
    linked g (carrierAt (pair 0).2.2) (carrierAt (pair 1).2.2) := Iff.rfl

end LCTR.CoreCommunicationDataInterfaces
