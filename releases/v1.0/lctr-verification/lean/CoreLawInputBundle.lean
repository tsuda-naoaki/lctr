import CoreRecordCodes
import CoreNativeObservables

namespace LCTR.CoreLawInputBundle
set_option autoImplicit false
open LCTR.CoreTrajectoryDescent LCTR.CoreObserverTime LCTR.CoreNativeCurves
open LCTR.CoreRecordCodes LCTR.CoreNativeObservables
universe u v w
variable {C : Type u} {D : Type v} {B : Type w}
variable {U L J V W P N : Type} {Arr : U → Type}

structure QuotientData (d : Input C D B) where
  projections : (C → Time d) × (B → State d)
  order : Time d → Time d → Prop
  relation : Time d → State d → Prop

def quotientData (d : Input C D B) : QuotientData d :=
  ⟨(timeProjection d, prj (genB d.relation d.binding)), generatedOrder d, trajectoryRelation d⟩

structure RecordData (d : Input C D B) (W P N : Type) where
  values : Set (W × P × N)
  code : D → W × P × N
  roleRelations : Set (Time d × (W × P × N)) × Set (State d × (W × P × N))
  pairRelation : Set ((Time d × State d) × (W × P × N))

def recordData (d : Input C D B) (code : Code D W P N) : RecordData d W P N :=
  ⟨code.Values, code.value, (timeRecords d code, stateRecords d code), pairRecords d code⟩

structure ObservableData (d : Input C D B) (J V : Type) where
  ranges : J → Set V
  values : J × State d → V

def ObservableSpec (d : Input C D B) (a : LocalDatum B U L J V Arr)
    (o : ObservableData d J V) : Prop :=
  (∀ l, o.ranges (a.index l) = a.range l) ∧
  (∀ i l (x : Arr i), o.values (a.index l, localState d a i x) =
    a.compare i l (a.localObs i l x))

noncomputable def observableData (d : Input C D B) (a : LocalDatum B U L J V Arr)
    (h : Descent d a) : ObservableData d J V :=
  ⟨canonicalRange a h.indexSurj, canonical d a h⟩

theorem observable_spec (d : Input C D B) (a : LocalDatum B U L J V Arr)
    (h : Descent d a) : ObservableSpec d a (observableData d a h) := by
  constructor
  · intro l
    exact (range_representative_independence d a h (a.index l) l rfl).symm
  · intro i l x
    exact canonical_representative_value d a h _ _ i l x rfl rfl

theorem observable_unique (d : Input C D B) (a : LocalDatum B U L J V Arr)
    (h : Descent d a) (o : ObservableData d J V) (ho : ObservableSpec d a o) :
    o = observableData d a h := by
  have hr : o.ranges = canonicalRange a h.indexSurj := by
    funext q
    obtain ⟨l, rfl⟩ := h.indexSurj q
    exact (ho.1 l).trans (range_representative_independence d a h _ l rfl)
  have hv := canonical_unique d a h o.values ho.2
  cases o
  simp_all [observableData]

structure LawInput (d : Input C D B) (J V W P N : Type) where
  quotient : QuotientData d
  domain : Set (Time d)
  trajectory : Domain d → State d
  observables : ObservableData d J V
  records : RecordData d W P N

def LawInputSpec (d : Input C D B) (a : LocalDatum B U L J V Arr)
    (code : Code D W P N) (x : LawInput d J V W P N) : Prop :=
  x.quotient = quotientData d ∧
  x.domain = {t | ∃ s, trajectoryRelation d t s} ∧
  (∀ p : Domain d × State d, trajectoryRelation d p.1.val p.2 ↔ p.2 = x.trajectory p.1) ∧
  ObservableSpec d a x.observables ∧ x.records = recordData d code

noncomputable def lawInput (d : Input C D B) (single : Single d)
    (a : LocalDatum B U L J V Arr) (h : Descent d a) (code : Code D W P N) :
    LawInput d J V W P N :=
  ⟨quotientData d, {t | ∃ s, trajectoryRelation d t s}, canonicalTrajectory d single,
    observableData d a h, recordData d code⟩

theorem law_input_spec (d : Input C D B) (single : Single d)
    (a : LocalDatum B U L J V Arr) (h : Descent d a) (code : Code D W P N) :
    LawInputSpec d a code (lawInput d single a h code) :=
  ⟨rfl, rfl, (canonical_graph_contract d single).1, observable_spec d a h, rfl⟩

theorem law_input_unique (d : Input C D B) (single : Single d)
    (a : LocalDatum B U L J V Arr) (h : Descent d a) (code : Code D W P N)
    (x : LawInput d J V W P N) (hx : LawInputSpec d a code x) :
    x = lawInput d single a h code := by
  obtain ⟨hq, hd, ht, ho, hr⟩ := hx
  have et := (canonical_graph_contract d single).2 x.trajectory ht
  have eo := observable_unique d a h x.observables ho
  cases x
  simp_all [lawInput]

theorem law_input_exists_unique (d : Input C D B) (single : Single d)
    (a : LocalDatum B U L J V Arr) (h : Descent d a) (code : Code D W P N) :
    ∃! x : LawInput d J V W P N, LawInputSpec d a code x :=
  ⟨lawInput d single a h code, law_input_spec d single a h code,
    law_input_unique d single a h code⟩

theorem record_pair_typed (d : Input C D B) (single : Single d)
    (a : LocalDatum B U L J V Arr) (h : Descent d a) (code : Code D W P N)
    (p : (Time d × State d) × (W × P × N))
    (hp : p ∈ (lawInput d single a h code).records.pairRelation) :
    (lawInput d single a h code).quotient.relation p.1.1 p.1.2 ∧
    p.2 ∈ (lawInput d single a h code).records.values :=
  pair_records_typed d code p hp

theorem role_record_projection (d : Input C D B) (single : Single d)
    (a : LocalDatum B U L J V Arr) (h : Descent d a) (code : Code D W P N) :
    (∀ t v, (t,v) ∈ (lawInput d single a h code).records.roleRelations.1 ↔
      ∃ s, ((t,s),v) ∈ (lawInput d single a h code).records.pairRelation) ∧
    (∀ s v, (s,v) ∈ (lawInput d single a h code).records.roleRelations.2 ↔
      ∃ t, ((t,s),v) ∈ (lawInput d single a h code).records.pairRelation) :=
  ⟨time_projection_exact d code, state_projection_exact d code⟩

theorem source_relation_exact (d : Input C D B)
    (desc : Desc (genC d.relation d.binding) (genB d.relation d.binding) d.relation)
    (single : Single d) (a : LocalDatum B U L J V Arr) (h : Descent d a)
    (code : Code D W P N) (c : C) (b : B) :
    (lawInput d single a h code).quotient.relation
      ((lawInput d single a h code).quotient.projections.1 c)
      ((lawInput d single a h code).quotient.projections.2 b) ↔ ∃ r, d.relation c r b :=
  image_membership_iff _ _ _ desc c b

theorem observable_value_typed (d : Input C D B) (single : Single d)
    (a : LocalDatum B U L J V Arr) (h : Descent d a) (code : Code D W P N)
    (q : J) (s : State d) :
    (lawInput d single a h code).observables.values (q,s) ∈
      (lawInput d single a h code).observables.ranges q :=
  canonical_value_typed d a h q s

theorem observable_change_preserved (d : Input C D B) (single : Single d)
    (a : LocalDatum B U L J V Arr) (h : Descent d a) (hc : ChangeCommutes a)
    (code : Code D W P N) (i j : U) (l : L) (x : Arr i)
    (hx : a.localObs i l x ∈ a.changeDom i j l) :
    (lawInput d single a h code).observables.values (a.index l, localState d a i x) =
      a.compare j l (a.change i j l ⟨a.localObs i l x,hx⟩) :=
  local_change_compatibility d a h hc i j l x hx

end LCTR.CoreLawInputBundle
