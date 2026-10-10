import CoreRecordCodes

namespace LCTR.CoreRawRecordCodes
set_option autoImplicit false
open LCTR.CoreTrajectoryDescent LCTR.CoreRecordCodes
universe u v w z
variable {C : Type u} {D : Type v} {B : Type w} {W P N : Type z}

variable (r : C → D → B → Prop) (bind : C × D × B → C × D × B → Prop)
abbrev Time := Q (genC r bind)
abbrev State := Q (genB r bind)

def pairRecords (code : Code D W P N) : Set ((Time r bind × State r bind) × (W × P × N)) :=
  {p | ∃ c d b, r c d b ∧
    ((prj (genC r bind) c, prj (genB r bind) b), code.value d) = p}
def timeRecords (code : Code D W P N) : Set (Time r bind × (W × P × N)) :=
  (fun p => (p.1.1, p.2)) '' pairRecords r bind code
def stateRecords (code : Code D W P N) : Set (State r bind × (W × P × N)) :=
  (fun p => (p.1.2, p.2)) '' pairRecords r bind code
def recordData (code : Code D W P N) :=
  (code.Values, code.value,
    (timeRecords r bind code, stateRecords r bind code), pairRecords r bind code)

theorem record_code_components (code : Code D W P N) (d : D) :
    code.value d = (code.window d, code.field d, code.sequence d) := rfl

theorem pair_source_membership (code : Code D W P N)
    (c : C) (d : D) (b : B) (src : r c d b) :
    ((prj (genC r bind) c, prj (genB r bind) b), code.value d) ∈ pairRecords r bind code :=
  ⟨c, d, b, src, rfl⟩

theorem pair_records_typed (code : Code D W P N)
    (p : (Time r bind × State r bind) × (W × P × N)) (hp : p ∈ pairRecords r bind code) :
    imageRelation (genC r bind) (genB r bind) r p.1.1 p.1.2 ∧ p.2 ∈ code.Values := by
  obtain ⟨c, d, b, src, rfl⟩ := hp
  exact ⟨⟨c, b, ⟨d, src⟩, rfl, rfl⟩, ⟨d, rfl⟩⟩

theorem time_projection_exact (code : Code D W P N) (t : Time r bind) (v : W × P × N) :
    (t, v) ∈ timeRecords r bind code ↔ ∃ s : State r bind, ((t, s), v) ∈ pairRecords r bind code := by
  constructor
  · rintro ⟨p, hp, eq⟩
    have ht := congrArg Prod.fst eq
    have hv := congrArg Prod.snd eq
    change p.1.1 = t at ht
    change p.2 = v at hv
    exact ⟨p.1.2, by simpa only [← ht, ← hv] using hp⟩
  · rintro ⟨s, hs⟩
    exact ⟨((t, s), v), hs, rfl⟩

theorem state_projection_exact (code : Code D W P N) (s : State r bind) (v : W × P × N) :
    (s, v) ∈ stateRecords r bind code ↔ ∃ t : Time r bind, ((t, s), v) ∈ pairRecords r bind code := by
  constructor
  · rintro ⟨p, hp, eq⟩
    have hs := congrArg Prod.fst eq
    have hv := congrArg Prod.snd eq
    change p.1.2 = s at hs
    change p.2 = v at hv
    exact ⟨p.1.1, by simpa only [← hs, ← hv] using hp⟩
  · rintro ⟨t, ht⟩
    exact ⟨((t, s), v), ht, rfl⟩

theorem projected_record_values_typed (code : Code D W P N) :
    (∀ p ∈ timeRecords r bind code, p.2 ∈ code.Values) ∧
    (∀ p ∈ stateRecords r bind code, p.2 ∈ code.Values) := by
  constructor
  · rintro p ⟨pair, hp, rfl⟩
    exact (pair_records_typed r bind code pair hp).2
  · rintro p ⟨pair, hp, rfl⟩
    exact (pair_records_typed r bind code pair hp).2

theorem record_values_not_forced_single (code : Code D W P N)
    (c : C) (b : B) (d e : D) (hd : r c d b) (he : r c e b)
    (different : code.value d ≠ code.value e) :
    ∃ p : Time r bind × State r bind, ∃ v w : W × P × N,
      (p, v) ∈ pairRecords r bind code ∧ (p, w) ∈ pairRecords r bind code ∧ v ≠ w :=
  ⟨(prj (genC r bind) c, prj (genB r bind) b), code.value d, code.value e,
    pair_source_membership r bind code c d b hd,
    pair_source_membership r bind code c e b he, different⟩

theorem empty_source_records (code : Code D W P N)
    (empty : ∀ c d b, ¬ r c d b) : pairRecords r bind code = ∅ := by
  ext p
  constructor
  · rintro ⟨c, d, b, src, _⟩
    exact False.elim (empty c d b src)
  · intro hp
    exact False.elim hp

end LCTR.CoreRawRecordCodes
