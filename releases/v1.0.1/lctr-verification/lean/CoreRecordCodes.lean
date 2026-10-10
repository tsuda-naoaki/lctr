import CoreNativeCurves

namespace LCTR.CoreRecordCodes
set_option autoImplicit false
open LCTR.CoreTrajectoryDescent LCTR.CoreObserverTime LCTR.CoreNativeCurves
universe u v w z
variable {C : Type u} {D : Type v} {B : Type w} {W P N : Type z}

structure Code (D : Type v) (W P N : Type z) where
  window : D → W
  field : D → P
  sequence : D → N
def Code.value (code : Code D W P N) (x : D) : W × P × N :=
  (code.window x, code.field x, code.sequence x)
abbrev Code.Values (code : Code D W P N) := Set.range code.value

def pairRecords (d : Input C D B) (code : Code D W P N) : Set ((Time d × State d) × (W × P × N)) :=
  {p | ∃ c r b, d.relation c r b ∧
    ((timeProjection d c, prj (genB d.relation d.binding) b),code.value r) = p}
def timeRecords (d : Input C D B) (code : Code D W P N) : Set (Time d × (W × P × N)) :=
  (fun p => (p.1.1,p.2)) '' pairRecords d code
def stateRecords (d : Input C D B) (code : Code D W P N) : Set (State d × (W × P × N)) :=
  (fun p => (p.1.2,p.2)) '' pairRecords d code

theorem record_code_components (code : Code D W P N) (r : D) :
    code.value r = (code.window r,code.field r,code.sequence r) := rfl

theorem pair_source_membership (d : Input C D B) (code : Code D W P N)
    (c : C) (r : D) (b : B) (src : d.relation c r b) :
    ((timeProjection d c, prj (genB d.relation d.binding) b),code.value r) ∈ pairRecords d code :=
  ⟨c,r,b,src,rfl⟩

theorem pair_records_typed (d : Input C D B) (code : Code D W P N)
    (p : (Time d × State d) × (W × P × N)) (hp : p ∈ pairRecords d code) :
    trajectoryRelation d p.1.1 p.1.2 ∧ p.2 ∈ code.Values := by
  obtain ⟨c,r,b,src,rfl⟩ := hp
  exact ⟨⟨c,b,⟨r,src⟩,rfl,rfl⟩,⟨r,rfl⟩⟩

theorem time_projection_exact (d : Input C D B) (code : Code D W P N) (t : Time d) (v : W × P × N) :
    (t,v) ∈ timeRecords d code ↔ ∃ s : State d, ((t,s),v) ∈ pairRecords d code := by
  constructor
  · rintro ⟨p,hp,eq⟩
    have ht := congrArg Prod.fst eq
    have hv := congrArg Prod.snd eq
    change p.1.1 = t at ht
    change p.2 = v at hv
    exact ⟨p.1.2, by simpa only [← ht, ← hv] using hp⟩
  · rintro ⟨s,hs⟩
    exact ⟨((t,s),v),hs,rfl⟩

theorem state_projection_exact (d : Input C D B) (code : Code D W P N) (s : State d) (v : W × P × N) :
    (s,v) ∈ stateRecords d code ↔ ∃ t : Time d, ((t,s),v) ∈ pairRecords d code := by
  constructor
  · rintro ⟨p,hp,eq⟩
    have hs := congrArg Prod.fst eq
    have hv := congrArg Prod.snd eq
    change p.1.2 = s at hs
    change p.2 = v at hv
    exact ⟨p.1.1, by simpa only [← hs, ← hv] using hp⟩
  · rintro ⟨t,ht⟩
    exact ⟨((t,s),v),ht,rfl⟩

theorem projected_record_values_typed (d : Input C D B) (code : Code D W P N) :
    (∀ p ∈ timeRecords d code, p.2 ∈ code.Values) ∧
    (∀ p ∈ stateRecords d code, p.2 ∈ code.Values) := by
  constructor
  · rintro p ⟨pair,hp,rfl⟩
    exact (pair_records_typed d code pair hp).2
  · rintro p ⟨pair,hp,rfl⟩
    exact (pair_records_typed d code pair hp).2

theorem record_values_not_forced_single (d : Input C D B) (code : Code D W P N)
    (c : C) (b : B) (r s : D) (hr : d.relation c r b) (hs : d.relation c s b)
    (different : code.value r ≠ code.value s) :
    ∃ p : Time d × State d, ∃ v w : W × P × N,
      (p,v) ∈ pairRecords d code ∧ (p,w) ∈ pairRecords d code ∧ v ≠ w :=
  ⟨(timeProjection d c,prj (genB d.relation d.binding) b),code.value r,code.value s,
    pair_source_membership d code c r b hr,pair_source_membership d code c s b hs,different⟩

theorem empty_source_records (d : Input C D B) (code : Code D W P N)
    (empty : ∀ c r b, ¬ d.relation c r b) : pairRecords d code = ∅ := by
  ext p
  constructor
  · rintro ⟨c,r,b,src,_⟩
    exact False.elim (empty c r b src)
  · intro hp
    exact False.elim hp

end LCTR.CoreRecordCodes
