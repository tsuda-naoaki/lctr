import Mathlib.Data.Set.Basic

namespace LCTR.Chapter02

inductive Role where
  | clock
  | detector
  | body
  | observer
deriving DecidableEq, Repr

abbrev RealizationRole := { r : Role // r ≠ .body }

def realizationClock : RealizationRole := ⟨.clock, by decide⟩
def realizationDetector : RealizationRole := ⟨.detector, by decide⟩
def realizationObserver : RealizationRole := ⟨.observer, by decide⟩

theorem realizationRole_cases (r : RealizationRole) :
    r.1 = .clock ∨ r.1 = .detector ∨ r.1 = .observer := by
  rcases r with ⟨r, hr⟩
  cases r with
  | clock => exact Or.inl rfl
  | detector => exact Or.inr (Or.inl rfl)
  | body => exact False.elim (hr rfl)
  | observer => exact Or.inr (Or.inr rfl)

universe u v w z

variable {Scene : Type u}
variable {Tracked : Type v}
variable {Zeta : Type z}
variable (LC : Scene → Role → Type w)

structure BindingSpec where
  correspondenceEntered :
    ∀ {sc : Scene}, LC sc .clock → LC sc .body → LC sc .detector → Prop
  detectorRetains :
    ∀ {sc : Scene}, LC sc .clock → LC sc .body → LC sc .detector → Prop
  observerReceives :
    ∀ {sc : Scene}, LC sc .clock → LC sc .detector → LC sc .body → LC sc .observer → Prop
  observerCombines :
    ∀ {sc : Scene}, LC sc .clock → LC sc .detector → LC sc .body → LC sc .observer → Prop

structure BindWitness (bindSpec : BindingSpec LC) (sc : Scene) where
  clock : LC sc .clock
  detector : LC sc .detector
  body : LC sc .body
  observer : LC sc .observer
  condition1 : bindSpec.correspondenceEntered clock body detector
  condition2 : bindSpec.detectorRetains clock body detector
  condition3 : bindSpec.observerReceives clock detector body observer
  condition4 : bindSpec.observerCombines clock detector body observer

variable (bindSpec : BindingSpec LC)
variable (BodyAbstractedFrom :
  Tracked → {sc : Scene} → LC sc .body → Prop)

structure ObjectSpecData where
  tracked : Tracked
  scene : Scene
  witness : BindWitness LC bindSpec scene
  bodyAbstractedFrom :
    BodyAbstractedFrom tracked witness.body

variable (assign :
  Zeta → ObjectSpecData LC bindSpec BodyAbstractedFrom)

def roleComponent
    (ζ : Zeta) :
    (r : Role) → LC (assign ζ).scene r
  | .clock => (assign ζ).witness.clock
  | .detector => (assign ζ).witness.detector
  | .body => (assign ζ).witness.body
  | .observer => (assign ζ).witness.observer

structure RoleInstance where
  role : Role
  zeta : Zeta
  component : LC (assign zeta).scene role

def roleInstance
    (r : Role)
    (ζ : Zeta) :
    RoleInstance LC bindSpec BodyAbstractedFrom assign where
  role := r
  zeta := ζ
  component := roleComponent LC bindSpec BodyAbstractedFrom assign ζ r

theorem roleInstance_eq_iff_index_eq
    (r : Role)
    (ζ1 ζ2 : Zeta) :
    roleInstance LC bindSpec BodyAbstractedFrom assign r ζ1 =
      roleInstance LC bindSpec BodyAbstractedFrom assign r ζ2 ↔
    ζ1 = ζ2 := by
  constructor
  · intro h
    exact congrArg RoleInstance.zeta h
  · intro h
    cases h
    rfl

structure RoleBundle where
  clock : RoleInstance LC bindSpec BodyAbstractedFrom assign
  detector : RoleInstance LC bindSpec BodyAbstractedFrom assign
  body : RoleInstance LC bindSpec BodyAbstractedFrom assign
  observer : RoleInstance LC bindSpec BodyAbstractedFrom assign

def roleBundle
    (ζ : Zeta) :
    RoleBundle LC bindSpec BodyAbstractedFrom assign where
  clock := roleInstance LC bindSpec BodyAbstractedFrom assign .clock ζ
  detector := roleInstance LC bindSpec BodyAbstractedFrom assign .detector ζ
  body := roleInstance LC bindSpec BodyAbstractedFrom assign .body ζ
  observer := roleInstance LC bindSpec BodyAbstractedFrom assign .observer ζ

abbrev RIFamily
    (Z0 : Set Zeta) :=
  (ζ : { ζ // ζ ∈ Z0 }) →
    RoleBundle LC bindSpec BodyAbstractedFrom assign

def riFamily
    (Z0 : Set Zeta) :
    RIFamily LC bindSpec BodyAbstractedFrom assign Z0 :=
  fun ζ => roleBundle LC bindSpec BodyAbstractedFrom assign ζ.1

theorem riFamily_preserves_index_and_role_positions
    (Z0 : Set Zeta)
    (ζ : { ζ // ζ ∈ Z0 }) :
    ((riFamily LC bindSpec BodyAbstractedFrom assign Z0 ζ).clock.zeta = ζ.1) ∧
    ((riFamily LC bindSpec BodyAbstractedFrom assign Z0 ζ).detector.zeta = ζ.1) ∧
    ((riFamily LC bindSpec BodyAbstractedFrom assign Z0 ζ).body.zeta = ζ.1) ∧
    ((riFamily LC bindSpec BodyAbstractedFrom assign Z0 ζ).observer.zeta = ζ.1) ∧
    ((riFamily LC bindSpec BodyAbstractedFrom assign Z0 ζ).clock.role = .clock) ∧
    ((riFamily LC bindSpec BodyAbstractedFrom assign Z0 ζ).detector.role = .detector) ∧
    ((riFamily LC bindSpec BodyAbstractedFrom assign Z0 ζ).body.role = .body) ∧
    ((riFamily LC bindSpec BodyAbstractedFrom assign Z0 ζ).observer.role = .observer) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem body_abstraction_source_preserved
    (Z0 : Set Zeta)
    (ζ : { ζ // ζ ∈ Z0 }) :
    BodyAbstractedFrom
      (assign ζ.1).tracked
      (assign ζ.1).witness.body :=
  (assign ζ.1).bodyAbstractedFrom

abbrev RealizationInput
    (Z0 : Set Zeta) :=
  (ζ : { ζ // ζ ∈ Z0 }) → (r : RealizationRole) →
    RoleInstance LC bindSpec BodyAbstractedFrom assign

def realizationInput
    (Z0 : Set Zeta) :
    RealizationInput LC bindSpec BodyAbstractedFrom assign Z0 :=
  fun ζ r =>
    roleInstance LC bindSpec BodyAbstractedFrom assign r.1 ζ.1

theorem realization_input_excludes_body
    (Z0 : Set Zeta)
    (ζ : { ζ // ζ ∈ Z0 })
    (r : RealizationRole) :
    (realizationInput LC bindSpec BodyAbstractedFrom assign Z0 ζ r).role ≠ .body := by
  simpa [realizationInput, roleInstance] using r.2

structure PhysicalRealization
    (Z0 : Set Zeta)
    (dom : RealizationInput LC bindSpec BodyAbstractedFrom assign Z0) where
  Carrier : Type
  realize :
    ∀ (ζ : { ζ // ζ ∈ Z0 }) (r : RealizationRole),
      { x : RoleInstance LC bindSpec BodyAbstractedFrom assign //
        x = dom ζ r } → Carrier

structure RealizedExtension
    (Z0 : Set Zeta) where
  base : RIFamily LC bindSpec BodyAbstractedFrom assign Z0
  realization :
    PhysicalRealization LC bindSpec BodyAbstractedFrom assign Z0
      (realizationInput LC bindSpec BodyAbstractedFrom assign Z0)

def attachRealization
    (Z0 : Set Zeta)
    (p : PhysicalRealization LC bindSpec BodyAbstractedFrom assign Z0
      (realizationInput LC bindSpec BodyAbstractedFrom assign Z0)) :
    RealizedExtension LC bindSpec BodyAbstractedFrom assign Z0 where
  base := riFamily LC bindSpec BodyAbstractedFrom assign Z0
  realization := p

theorem realization_is_additional_and_preserves_existing_ri
    (Z0 : Set Zeta)
    (p : PhysicalRealization LC bindSpec BodyAbstractedFrom assign Z0
      (realizationInput LC bindSpec BodyAbstractedFrom assign Z0)) :
    (attachRealization LC bindSpec BodyAbstractedFrom assign Z0 p).base =
      riFamily LC bindSpec BodyAbstractedFrom assign Z0 := by
  rfl

structure ConstructionInput where
  Z0 : Set Zeta

def synthesize
    (input : ConstructionInput (Zeta := Zeta)) :
    RIFamily LC bindSpec BodyAbstractedFrom assign input.Z0 :=
  riFamily LC bindSpec BodyAbstractedFrom assign input.Z0

theorem section2_synthesis_preserves_positions
    (input : ConstructionInput (Zeta := Zeta))
    (ζ : { ζ // ζ ∈ input.Z0 }) :
    ((synthesize LC bindSpec BodyAbstractedFrom assign input ζ).clock.zeta = ζ.1) ∧
    ((synthesize LC bindSpec BodyAbstractedFrom assign input ζ).detector.zeta = ζ.1) ∧
    ((synthesize LC bindSpec BodyAbstractedFrom assign input ζ).body.zeta = ζ.1) ∧
    ((synthesize LC bindSpec BodyAbstractedFrom assign input ζ).observer.zeta = ζ.1) ∧
    ((synthesize LC bindSpec BodyAbstractedFrom assign input ζ).clock.role = .clock) ∧
    ((synthesize LC bindSpec BodyAbstractedFrom assign input ζ).detector.role = .detector) ∧
    ((synthesize LC bindSpec BodyAbstractedFrom assign input ζ).body.role = .body) ∧
    ((synthesize LC bindSpec BodyAbstractedFrom assign input ζ).observer.role = .observer) := by
  exact riFamily_preserves_index_and_role_positions
    LC bindSpec BodyAbstractedFrom assign input.Z0 ζ

theorem section2_synthesis_body_source
    (input : ConstructionInput (Zeta := Zeta))
    (ζ : { ζ // ζ ∈ input.Z0 }) :
    BodyAbstractedFrom
      (assign ζ.1).tracked
      (assign ζ.1).witness.body :=
  body_abstraction_source_preserved
    LC bindSpec BodyAbstractedFrom assign input.Z0 ζ

theorem section2_synthesis_realization_domain
    (input : ConstructionInput (Zeta := Zeta))
    (ζ : { ζ // ζ ∈ input.Z0 })
    (r : RealizationRole) :
    (realizationInput LC bindSpec BodyAbstractedFrom assign input.Z0 ζ r).role = r.1 ∧
    r.1 ≠ .body := by
  exact ⟨rfl, r.2⟩

end LCTR.Chapter02
