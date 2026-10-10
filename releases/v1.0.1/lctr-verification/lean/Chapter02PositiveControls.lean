import «Chapter02LeanBridge»

namespace LCTR.Chapter02.PositiveControls

open LCTR.Chapter02

universe u v w z
variable {Scene : Type u} {Tracked : Type v} {Zeta : Type z}
variable (LC : Scene → Role → Type w)
variable (bindSpec : BindingSpec LC)
variable (BodyAbstractedFrom :
  Tracked → {sc : Scene} → LC sc .body → Prop)
variable (assign :
  Zeta → ObjectSpecData LC bindSpec BodyAbstractedFrom)

example :
    RIFamily LC bindSpec BodyAbstractedFrom assign
      (∅ : Set Zeta) :=
  riFamily LC bindSpec BodyAbstractedFrom assign ∅

theorem different_indices_remain_distinct_at_each_role
    (r : Role)
    (ζ1 ζ2 : Zeta)
    (hne : ζ1 ≠ ζ2) :
    roleInstance LC bindSpec BodyAbstractedFrom assign r ζ1 ≠
      roleInstance LC bindSpec BodyAbstractedFrom assign r ζ2 := by
  intro h
  exact hne
    ((roleInstance_eq_iff_index_eq
      LC bindSpec BodyAbstractedFrom assign r ζ1 ζ2).mp h)

theorem different_role_positions_remain_distinct
    (ζ : Zeta) :
    roleInstance LC bindSpec BodyAbstractedFrom assign .clock ζ ≠
      roleInstance LC bindSpec BodyAbstractedFrom assign .body ζ := by
  intro h
  have hr := congrArg RoleInstance.role h
  cases hr

section SameSpecifiedDataDifferentIndices

def TinyLC : Unit → Role → Type
  | _, _ => Unit

def tinySpec : BindingSpec TinyLC where
  correspondenceEntered := fun _ _ _ => True
  detectorRetains := fun _ _ _ => True
  observerReceives := fun _ _ _ _ => True
  observerCombines := fun _ _ _ _ => True

def tinyBodySource :
    Unit → {sc : Unit} → TinyLC sc .body → Prop :=
  fun _ {_} _ => True

def tinyWitness : BindWitness TinyLC tinySpec () where
  clock := ()
  detector := ()
  body := ()
  observer := ()
  condition1 := True.intro
  condition2 := True.intro
  condition3 := True.intro
  condition4 := True.intro

def sameObjectSpecData :
    ObjectSpecData TinyLC tinySpec tinyBodySource where
  tracked := ()
  scene := ()
  witness := tinyWitness
  bodyAbstractedFrom := True.intro

def sameAssignment :
    Bool → ObjectSpecData TinyLC tinySpec tinyBodySource :=
  fun _ => sameObjectSpecData

theorem distinct_zeta_same_object_scene_and_bind_witness :
    sameAssignment true = sameAssignment false := by
  rfl

theorem distinct_zeta_same_specified_data_still_distinct_in_every_role :
    ∀ r : Role,
      roleInstance TinyLC tinySpec tinyBodySource sameAssignment r true ≠
        roleInstance TinyLC tinySpec tinyBodySource sameAssignment r false := by
  intro r h
  have htf : true = false :=
    (roleInstance_eq_iff_index_eq
      TinyLC tinySpec tinyBodySource sameAssignment r true false).mp h
  cases htf

def tinyZ0 : Set Bool := {true, false}

example :
    RIFamily TinyLC tinySpec tinyBodySource sameAssignment tinyZ0 :=
  riFamily TinyLC tinySpec tinyBodySource sameAssignment tinyZ0

end SameSpecifiedDataDifferentIndices

end LCTR.Chapter02.PositiveControls
