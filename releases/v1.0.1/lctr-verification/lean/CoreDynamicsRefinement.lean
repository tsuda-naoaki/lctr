import CoreDynamicsFactors
import CorePreorderQuotient
import Mathlib.Logic.Equiv.Basic

namespace LCTR.CoreDynamicsRefinement
set_option autoImplicit false
universe u v w
variable {C : Type u} {B : Type v}

structure Presentation (C : Type u) (B : Type v) where
  Time : Type u
  State : Type v
  qC : C → Time
  qB : B → State
  ontoC : Function.Surjective qC
  ontoB : Function.Surjective qB
  order : PartialOrder Time
  trajectory : Time → State → Prop

instance (P : Presentation C B) : PartialOrder P.Time := P.order

structure Arrow (P Q : Presentation C B) where
  time : P.Time → Q.Time
  state : P.State → Q.State
  ontoTime : Function.Surjective time
  ontoState : Function.Surjective state
  commuteTime : ∀ c, time (P.qC c) = Q.qC c
  commuteState : ∀ b, state (P.qB b) = Q.qB b
  monotone : ∀ x y, x ≤ y → time x ≤ time y
  image : ∀ t s, Q.trajectory t s ↔
    ∃ x y, P.trajectory x y ∧ time x = t ∧ state y = s

def Arrow.identity (P : Presentation C B) : Arrow P P where
  time := id
  state := id
  ontoTime := Function.surjective_id
  ontoState := Function.surjective_id
  commuteTime := fun _ => rfl
  commuteState := fun _ => rfl
  monotone := fun _ _ h => h
  image := by
    intro t s
    constructor
    · exact fun h => ⟨t,s,h,rfl,rfl⟩
    · rintro ⟨x,y,h,rfl,rfl⟩
      exact h

def Arrow.comp {P Q R : Presentation C B} (g : Arrow Q R) (f : Arrow P Q) : Arrow P R where
  time := g.time ∘ f.time
  state := g.state ∘ f.state
  ontoTime := g.ontoTime.comp f.ontoTime
  ontoState := g.ontoState.comp f.ontoState
  commuteTime := fun c => (congrArg g.time (f.commuteTime c)).trans (g.commuteTime c)
  commuteState := fun b => (congrArg g.state (f.commuteState b)).trans (g.commuteState b)
  monotone := fun x y h => g.monotone _ _ (f.monotone x y h)
  image := by
    intro t s
    constructor
    · intro h
      obtain ⟨x,y,hxy,hxt,hys⟩ := (g.image t s).mp h
      obtain ⟨a,b,hab,hax,hby⟩ := (f.image x y).mp hxy
      exact ⟨a,b,hab,(congrArg g.time hax).trans hxt,(congrArg g.state hby).trans hys⟩
    · rintro ⟨a,b,hab,hat,hbs⟩
      exact (g.image t s).mpr ⟨f.time a,f.state b,
        (f.image _ _).mpr ⟨a,b,hab,rfl,rfl⟩,hat,hbs⟩

def Refines (P Q : Presentation C B) : Prop := Nonempty (Arrow Q P)

theorem refinement_refl (P : Presentation C B) : Refines P P := ⟨Arrow.identity P⟩
theorem refinement_trans {P Q R : Presentation C B} :
    Refines P Q → Refines Q R → Refines P R := by
  rintro ⟨f⟩ ⟨g⟩
  exact ⟨f.comp g⟩

theorem mutual_factor_inverse {P Q : Presentation C B} (f : Arrow P Q) (g : Arrow Q P) :
    (∀ x, g.time (f.time x) = x) ∧ (∀ y, f.time (g.time y) = y) ∧
    (∀ x, g.state (f.state x) = x) ∧ (∀ y, f.state (g.state y) = y) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro x
    obtain ⟨c,rfl⟩ := P.ontoC x
    rw [f.commuteTime,g.commuteTime]
  · intro y
    obtain ⟨c,rfl⟩ := Q.ontoC y
    rw [g.commuteTime,f.commuteTime]
  · intro x
    obtain ⟨b,rfl⟩ := P.ontoB x
    rw [f.commuteState,g.commuteState]
  · intro y
    obtain ⟨b,rfl⟩ := Q.ontoB y
    rw [g.commuteState,f.commuteState]

structure Iso (P Q : Presentation C B) where
  time : P.Time ≃ Q.Time
  state : P.State ≃ Q.State
  commuteTime : ∀ c, time (P.qC c) = Q.qC c
  commuteState : ∀ b, state (P.qB b) = Q.qB b
  order_iff : ∀ x y, time x ≤ time y ↔ x ≤ y
  trajectory_iff : ∀ x y, Q.trajectory (time x) (state y) ↔ P.trajectory x y

def isoOfMutual {P Q : Presentation C B} (f : Arrow P Q) (g : Arrow Q P) : Iso P Q := by
  have h := mutual_factor_inverse f g
  let ec : P.Time ≃ Q.Time := ⟨f.time,g.time,h.1,h.2.1⟩
  let eb : P.State ≃ Q.State := ⟨f.state,g.state,h.2.2.1,h.2.2.2⟩
  refine ⟨ec,eb,f.commuteTime,f.commuteState,?_,?_⟩
  · intro x y
    constructor
    · intro xy
      have hh := g.monotone _ _ xy
      change g.time (f.time x) ≤ g.time (f.time y) at hh
      simpa only [h.1] using hh
    · exact f.monotone x y
  · intro x y
    constructor
    · intro ht
      obtain ⟨a,b,hab,ha,hb⟩ := (f.image _ _).mp ht
      have ax : a=x := ec.injective ha
      have by' : b=y := eb.injective hb
      simpa only [ax,by'] using hab
    · exact fun ht => (f.image _ _).mpr ⟨x,y,ht,rfl,rfl⟩

def Iso.forward {P Q : Presentation C B} (e : Iso P Q) : Arrow P Q where
  time := e.time
  state := e.state
  ontoTime := e.time.surjective
  ontoState := e.state.surjective
  commuteTime := e.commuteTime
  commuteState := e.commuteState
  monotone := fun x y => (e.order_iff x y).mpr
  image := by
    intro t s
    obtain ⟨x,rfl⟩ := e.time.surjective t
    obtain ⟨y,rfl⟩ := e.state.surjective s
    constructor
    · exact fun h => ⟨x,y,(e.trajectory_iff x y).mp h,rfl,rfl⟩
    · rintro ⟨a,b,h,ha,hb⟩
      have := (e.trajectory_iff a b).mpr h
      simpa only [ha,hb] using this

def Iso.symm {P Q : Presentation C B} (e : Iso P Q) : Iso Q P where
  time := e.time.symm
  state := e.state.symm
  commuteTime := fun c => by rw [← e.commuteTime c]; exact e.time.symm_apply_apply _
  commuteState := fun b => by rw [← e.commuteState b]; exact e.state.symm_apply_apply _
  order_iff := fun x y => by
    have h := e.order_iff (e.time.symm x) (e.time.symm y)
    simpa only [Equiv.apply_symm_apply] using h.symm
  trajectory_iff := fun x y => by
    have h := e.trajectory_iff (e.time.symm x) (e.state.symm y)
    simpa only [Equiv.apply_symm_apply] using h.symm

theorem mutual_iff_iso (P Q : Presentation C B) :
    (Refines P Q ∧ Refines Q P) ↔ Nonempty (Iso P Q) := by
  constructor
  · rintro ⟨⟨g⟩,⟨f⟩⟩
    exact ⟨isoOfMutual f g⟩
  · rintro ⟨e⟩
    exact ⟨⟨e.symm.forward⟩,⟨e.forward⟩⟩

def isoSetoid : Setoid (Presentation C B) where
  r P Q := Refines P Q ∧ Refines Q P
  iseqv := ⟨fun P => ⟨refinement_refl P,refinement_refl P⟩,
    fun h => ⟨h.2,h.1⟩,fun h k => ⟨refinement_trans h.1 k.1,refinement_trans k.2 h.2⟩⟩

theorem refinement_descends :
    CorePreorderQuotient.OrdDesc (isoSetoid (C:=C) (B:=B)) Refines := by
  intro a a' b b' ha hb
  exact ⟨fun h => refinement_trans ha.2 (refinement_trans h hb.1),
    fun h => refinement_trans ha.1 (refinement_trans h hb.2)⟩

abbrev IsoClass (C : Type u) (B : Type v) := Quotient (isoSetoid (C:=C) (B:=B))
def classLE : IsoClass C B → IsoClass C B → Prop :=
  CorePreorderQuotient.QuotientRel isoSetoid Refines refinement_descends

theorem isomorphism_class_partial_order :
    ∃ p : PartialOrder (IsoClass C B), p.le = classLE := by
  have h := CorePreorderQuotient.quotient_partial_order (isoSetoid (C:=C) (B:=B)) Refines
    refinement_descends (fun _ _ hab hba => ⟨hab,hba⟩)
    refinement_refl (fun _ _ _ => refinement_trans)
  let p : PartialOrder (IsoClass C B) :=
    { le := classLE
      le_refl := h.1
      le_trans := fun _ _ _ hxy hyz => h.2.1 hxy hyz
      le_antisymm := fun _ _ hxy hyx => h.2.2 hxy hyx }
  exact ⟨p,rfl⟩

open CoreTrajectoryDescent CoreDynamicsFactors GeneratedOrderUniversal
variable {D : Type w}

def canonical (gc : C → C → Prop) (gb : B → B → Prop)
    (ord : C → C → Prop) (r : C → D → B → Prop)
    (anti : ∀ x y, Order (Relation.EqvGen.setoid gc) ord x y →
      Order (Relation.EqvGen.setoid gc) ord y x → x=y) : Presentation C B where
  Time := Q gc
  State := Q gb
  qC := prj gc
  qB := prj gb
  ontoC := canonical_projection_surjective gc
  ontoB := canonical_projection_surjective gb
  order :=
    { le := Order (Relation.EqvGen.setoid gc) ord
      le_refl := reflexive _ _
      le_trans := fun _ _ _ => transitive _ _
      le_antisymm := anti }
  trajectory := imageRelation gc gb r

def Admissible (gc : C → C → Prop) (gb : B → B → Prop)
    (ord : C → C → Prop) (r : C → D → B → Prop) (P : Presentation C B) : Prop :=
  (∀ x y, Relation.EqvGen gc x y → P.qC x = P.qC y) ∧
  (∀ x y, Relation.EqvGen gb x y → P.qB x = P.qB y) ∧
  (∀ x y, ord x y → P.qC x ≤ P.qC y) ∧
  (∀ t s, P.trajectory t s ↔ imageBy r P.qC P.qB t s)

theorem canonical_admissible (gc : C → C → Prop) (gb : B → B → Prop)
    (ord : C → C → Prop) (r : C → D → B → Prop) (anti) :
    Admissible gc gb ord r (canonical gc gb ord r anti) := by
  refine ⟨fun x y h => (canonical_projection_class gc x y).mpr h,
    fun x y h => (canonical_projection_class gb x y).mpr h,
    fun x y h => canonical_source_order_preserved gc ord x y h,fun _ _ => Iff.rfl⟩

theorem native_canonical_greatest (gc : C → C → Prop) (gb : B → B → Prop)
    (ord : C → C → Prop) (r : C → D → B → Prop) (anti)
    (P : Presentation C B) (hp : Admissible gc gb ord r P) :
    Refines P (canonical gc gb ord r anti) := by
  obtain ⟨f,hf,_⟩ := native_factor_pair_exists_unique gc gb ord r P.qC P.qB
    P.ontoC P.ontoB hp.1 hp.2.1 hp.2.2.1
  let a : Arrow (canonical gc gb ord r anti) P :=
    { time := f.1
      state := f.2
      ontoTime := hf.1
      ontoState := hf.2.1
      commuteTime := hf.2.2.1
      commuteState := hf.2.2.2.1
      monotone := hf.2.2.2.2.1
      image := fun t s => (hp.2.2.2 t s).trans (hf.2.2.2.2.2 t s) }
  exact ⟨a⟩

theorem native_canonical_class_greatest (gc : C → C → Prop) (gb : B → B → Prop)
    (ord : C → C → Prop) (r : C → D → B → Prop) (anti)
    (P : Presentation C B) (hp : Admissible gc gb ord r P) :
    classLE (Quotient.mk isoSetoid P) (Quotient.mk isoSetoid (canonical gc gb ord r anti)) :=
  native_canonical_greatest gc gb ord r anti P hp

theorem source_native_canonical_class_greatest
    (r : C → D → B → Prop) (bind : C × D × B → C × D × B → Prop)
    (ord : C → C → Prop) (anti) (P : Presentation C B)
    (hp : Admissible (genC r bind) (genB r bind) ord r P) :
    classLE (Quotient.mk isoSetoid P)
      (Quotient.mk isoSetoid (canonical (genC r bind) (genB r bind) ord r anti)) :=
  native_canonical_class_greatest _ _ ord r anti P hp

theorem missing_projection_surjectivity_control :
    (∀ x : Unit, (fun _ : Bool => false) ((fun _ : Unit => false) x) = false) ∧
    ¬ (∀ y : Bool, (fun _ : Bool => false) y = y) := by
  exact ⟨fun _ => rfl,fun h => Bool.noConfusion (h true)⟩

end LCTR.CoreDynamicsRefinement
