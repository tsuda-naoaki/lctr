import CoreContinuumDatum
import CoreRecordCodes

namespace LCTR.CoreContinuumNativeRecords
set_option autoImplicit false
open Set LCTR.CoreTrajectoryDescent LCTR.CoreObserverTime LCTR.CoreNativeCurves
open LCTR.CoreRecordCodes LCTR.CoreContinuumDatum
open scoped ENNReal
variable {C D B W P N Y : Type}

abbrev Raw (d : Input C D B) := {x : C × D × B // d.relation x.1 x.2.1 x.2.2}
abbrev Pair (d : Input C D B) :=
  {p : Time d × LCTR.CoreNativeCurves.State d // trajectoryRelation d p.1 p.2}
def Object (d : Input C D B) : Fin 3 → Type :=
  ![Time d,LCTR.CoreNativeCurves.State d,Pair d]

def rawPair (d : Input C D B) (x : Raw d) : Pair d :=
  ⟨(timeProjection d x.val.1,prj (genB d.relation d.binding) x.val.2.2),
    ⟨x.val.1,x.val.2.2,⟨x.val.2.1,x.property⟩,rfl,rfl⟩⟩
def rawObject (d : Input C D B) : (i : Fin 3) → Raw d → Object d i :=
  Fin.cases (fun x => timeProjection d x.val.1)
    (Fin.cases (fun x => prj (genB d.relation d.binding) x.val.2.2)
      (Fin.cases (rawPair d) (fun i => Fin.elim0 i)))
def encoded (code : Code D W P N) (r : D) : code.Values := ⟨code.value r,⟨r,rfl⟩⟩

def nativeRecords (d : Input C D B) (code : Code D W P N) (mapping : code.Values → Y) : RecordDatum where
  Domain := Object d
  Code := code.Values
  Value := Y
  codeRelation i obj v := ∃ x : Raw d, rawObject d i x = obj ∧ encoded code x.val.2.1 = v
  mapping := mapping

theorem native_domains (d : Input C D B) (code : Code D W P N) (mapping : code.Values → Y) :
    (nativeRecords d code mapping).Domain 0 = Time d ∧
    (nativeRecords d code mapping).Domain 1 = LCTR.CoreNativeCurves.State d ∧
    (nativeRecords d code mapping).Domain 2 = Pair d ∧
    (nativeRecords d code mapping).Code = code.Values := ⟨rfl,rfl,rfl,rfl⟩

theorem native_time_records (d : Input C D B) (code : Code D W P N)
    (mapping : code.Values → Y) (t : Time d) (v : code.Values) :
    (nativeRecords d code mapping).codeRelation 0 t v ↔ (t,v.val) ∈ timeRecords d code := by
  constructor
  · rintro ⟨x,ht,hv⟩
    apply (time_projection_exact d code t v.val).mpr
    refine ⟨prj (genB d.relation d.binding) x.val.2.2,x.val.1,x.val.2.1,x.val.2.2,x.property,?_⟩
    have cv := congrArg Subtype.val hv
    change code.value x.val.2.1 = v.val at cv
    change timeProjection d x.val.1 = t at ht
    simp only [ht,cv]
  · intro h
    obtain ⟨s,c,r,b,src,eq⟩ := (time_projection_exact d code t v.val).mp h
    refine ⟨⟨(c,r,b),src⟩,congrArg (fun p => p.1.1) eq,?_⟩
    exact Subtype.ext (congrArg Prod.snd eq)

theorem native_state_records (d : Input C D B) (code : Code D W P N)
    (mapping : code.Values → Y) (s : LCTR.CoreNativeCurves.State d) (v : code.Values) :
    (nativeRecords d code mapping).codeRelation 1 s v ↔ (s,v.val) ∈ stateRecords d code := by
  constructor
  · rintro ⟨x,hs,hv⟩
    apply (state_projection_exact d code s v.val).mpr
    refine ⟨timeProjection d x.val.1,x.val.1,x.val.2.1,x.val.2.2,x.property,?_⟩
    have cv := congrArg Subtype.val hv
    change code.value x.val.2.1 = v.val at cv
    change prj (genB d.relation d.binding) x.val.2.2 = s at hs
    simp only [hs,cv]
  · intro h
    obtain ⟨t,c,r,b,src,eq⟩ := (state_projection_exact d code s v.val).mp h
    refine ⟨⟨(c,r,b),src⟩,congrArg (fun p => p.1.2) eq,?_⟩
    exact Subtype.ext (congrArg Prod.snd eq)

theorem native_pair_records (d : Input C D B) (code : Code D W P N)
    (mapping : code.Values → Y) (p : Pair d) (v : code.Values) :
    (nativeRecords d code mapping).codeRelation 2 p v ↔ (p.val,v.val) ∈ pairRecords d code := by
  constructor
  · rintro ⟨x,hp,hv⟩
    refine ⟨x.val.1,x.val.2.1,x.val.2.2,x.property,?_⟩
    exact Prod.ext (congrArg Subtype.val hp) (congrArg Subtype.val hv)
  · rintro ⟨c,r,b,src,eq⟩
    exact ⟨⟨(c,r,b),src⟩,Subtype.ext (congrArg Prod.fst eq),
      Subtype.ext (congrArg Prod.snd eq)⟩

theorem pair_domain_has_source (d : Input C D B) (p : Pair d) :
    ∃ x : Raw d, rawPair d x = p := by
  obtain ⟨c,b,⟨r,src⟩,hc,hb⟩ := p.property
  refine ⟨⟨(c,r,b),src⟩,Subtype.ext ?_⟩
  exact Prod.ext hc hb

theorem pair_record_nonempty (d : Input C D B) (code : Code D W P N)
    (mapping : code.Values → Y) (p : Pair d) :
    (recordImage (nativeRecords d code mapping) 2 p).Nonempty := by
  obtain ⟨x,hx⟩ := pair_domain_has_source d p
  exact ⟨mapping (encoded code x.val.2.1),encoded code x.val.2.1,⟨x,hx,rfl⟩,rfl⟩

theorem native_image (d : Input C D B) (code : Code D W P N)
    (mapping : code.Values → Y) (i : Fin 3) (obj : Object d i) :
    recordImage (nativeRecords d code mapping) i obj =
      {y | ∃ x : Raw d, rawObject d i x = obj ∧ mapping (encoded code x.val.2.1) = y} := by
  ext y
  constructor
  · rintro ⟨v,⟨x,hx,hv⟩,hy⟩
    exact ⟨x,hx,(congrArg mapping hv).trans hy⟩
  · rintro ⟨x,hx,hy⟩
    exact ⟨encoded code x.val.2.1,⟨x,hx,rfl⟩,hy⟩

theorem native_collision (d : Input C D B) (code : Code D W P N)
    (mapping : code.Values → Y) : Collision (nativeRecords d code mapping) ↔
    ∃ i : Fin 3, ∃ x y : Raw d, rawObject d i x ≠ rawObject d i y ∧
      mapping (encoded code x.val.2.1) = mapping (encoded code y.val.2.1) := by
  rw [collision_witness]
  constructor
  · rintro ⟨i,a,b,ne,v,w,⟨x,hx,hv⟩,⟨y,hy,hw⟩,eq⟩
    refine ⟨i,x,y,?_,?_⟩
    · exact fun h => ne (hx.symm.trans (h.trans hy))
    · exact (congrArg mapping hv).trans (eq.trans (congrArg mapping hw).symm)
  · rintro ⟨i,x,y,ne,eq⟩
    exact ⟨i,rawObject d i x,rawObject d i y,ne,
      encoded code x.val.2.1,encoded code y.val.2.1,⟨x,rfl,rfl⟩,⟨y,rfl,rfl⟩,eq⟩

theorem native_separation_defect (d : Input C D B) (code : Code D W P N)
    (mapping : code.Values → Y) (eps : ℝ≥0∞) :
    eps < separationDefect (nativeRecords d code mapping) ↔
      (∃ i : Fin 3, ∃ x y : Raw d, rawObject d i x ≠ rawObject d i y ∧
        mapping (encoded code x.val.2.1) = mapping (encoded code y.val.2.1)) ∧ eps < 1 := by
  rw [separation_defect_excess,native_collision]

theorem unmapped_codes_collision (d : Input C D B) (code : Code D W P N) :
    Collision (nativeRecords d code (fun v => v)) ↔
      ∃ i : Fin 3, ∃ x y : Raw d, rawObject d i x ≠ rawObject d i y ∧
        code.value x.val.2.1 = code.value y.val.2.1 := by
  rw [native_collision]
  simp only [Subtype.ext_iff,encoded]

theorem injective_mapping_preserves_collision (d : Input C D B) (code : Code D W P N)
    (mapping : code.Values → Y) (inj : Function.Injective mapping) :
    Collision (nativeRecords d code mapping) ↔ Collision (nativeRecords d code (fun v => v)) := by
  rw [native_collision,native_collision]
  simp only [inj.eq_iff]

theorem extra_collision_requires_identification (d : Input C D B) (code : Code D W P N)
    (mapping : code.Values → Y) (after : Collision (nativeRecords d code mapping))
    (before : ¬ Collision (nativeRecords d code (fun v => v))) :
    ∃ a b : code.Values, a ≠ b ∧ mapping a = mapping b := by
  obtain ⟨i,x,y,ne,eq⟩ := (native_collision d code mapping).mp after
  refine ⟨encoded code x.val.2.1,encoded code y.val.2.1,?_,eq⟩
  intro same
  exact before ((native_collision d code (fun v => v)).mpr ⟨i,x,y,ne,same⟩)

theorem empty_source_no_collision (d : Input C D B) (code : Code D W P N)
    (mapping : code.Values → Y) (empty : ∀ c r b, ¬ d.relation c r b) :
    ¬ Collision (nativeRecords d code mapping) := by
  rw [native_collision]
  rintro ⟨_,x,_,_,_⟩
  exact empty x.val.1 x.val.2.1 x.val.2.2 x.property

end LCTR.CoreContinuumNativeRecords
