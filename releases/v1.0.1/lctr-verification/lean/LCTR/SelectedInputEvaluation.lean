import Std




namespace LCTR.SelectedInputEvaluation

def extend {E : Type} (D : E → Prop)
    (P : (e : E) → D e → Prop) (e : E) : Prop :=
  ∃ h : D e, P e h

theorem extension_on_domain {E : Type} (D : E → Prop)
    (P : (e : E) → D e → Prop) (e : E) (h : D e) :
    extend D P e ↔ P e h := by
  constructor
  · rintro ⟨_, hp⟩
    exact hp
  · exact fun hp => ⟨h,hp⟩

theorem extension_outside_domain {E : Type} (D : E → Prop)
    (P : (e : E) → D e → Prop) (e : E) (h : ¬ D e) :
    ¬ extend D P e := by
  rintro ⟨hd,_⟩
  exact h hd

structure Selected (E Data : Type) where
  domain : E → Prop
  datum : { e // domain e } → Data

def evaluate {E Data : Type} (s : Selected E Data) (P : Data → Prop) (e : E) :=
  extend s.domain (fun e h => P (s.datum ⟨e,h⟩)) e

theorem selection_defines_unique_value {E Data : Type} (s : Selected E Data)
    (P : Data → Prop) (e : E) (h : s.domain e) :
    evaluate s P e ↔ P (s.datum ⟨e,h⟩) :=
  extension_on_domain _ _ _ h

structure MatchingDifferential (E Law Structure : Type) (law : Selected E Law) where
  domain : E → Prop
  subdomain : ∀ e, domain e → law.domain e
  structureAt : { e // domain e } → Structure

def differentialInput {E Law Structure : Type} {law : Selected E Law}
    (d : MatchingDifferential E Law Structure law) (e : E) (h : d.domain e) :=
  (law.datum ⟨e,d.subdomain e h⟩, d.structureAt ⟨e,h⟩)

theorem matching_law_projection {E Law Structure : Type} {law : Selected E Law}
    (d : MatchingDifferential E Law Structure law) (e : E) (h : d.domain e) :
    (differentialInput d e h).1 = law.datum ⟨e,d.subdomain e h⟩ := rfl

inductive State where
  | unformed | unevaluable | sat | failed
  deriving DecidableEq

def state (formed evaluated prior condition : Bool) : State :=
  if !(formed && prior) then .unformed
  else if !evaluated then .unevaluable
  else if condition then .sat else .failed

theorem missing_input_unformed (evaluated prior condition : Bool) :
    state false evaluated prior condition = .unformed := by
  simp [state]

theorem missing_input_never_failed (evaluated prior condition : Bool) :
    state false evaluated prior condition ≠ .failed := by
  simp [state]

theorem failed_requires_available_input (formed evaluated prior condition : Bool) :
    state formed evaluated prior condition = .failed →
      formed = true ∧ evaluated = true ∧ prior = true ∧ condition = false := by
  cases formed <;> cases evaluated <;> cases prior <;> cases condition <;> decide

structure Conditions where
  c1 : Prop
  c2 : Prop
  c3 : Prop
  c4 : Prop
  c5 : Prop

def all (c : Conditions) := c.c1 ∧ c.c2 ∧ c.c3 ∧ c.c4 ∧ c.c5
def lawFailure (available : Prop) (c : Conditions) := available ∧ ¬ all c
def lawClasses (available : Prop) (c : Conditions) :=
  (available ∧ ¬ c.c1) ∨ (available ∧ ¬ c.c2) ∨
  (available ∧ c.c1 ∧ ¬ c.c3) ∨ (available ∧ ¬ c.c4) ∨
  (available ∧ c.c1 ∧ c.c3 ∧ ¬ c.c5)

theorem law_cover (available : Prop) (c : Conditions) :
    lawFailure available c ↔ lawClasses available c := by
  grind [lawFailure,lawClasses,all]

theorem no_law_failure_without_selection (c : Conditions) :
    ¬ lawFailure False c ∧ ¬ lawClasses False c := by
  simp [lawFailure,lawClasses]

def diffFailure (available lawOperative : Prop) (c : Conditions) :=
  available ∧ lawOperative ∧ ¬ all c
def diffClasses (available lawOperative : Prop) (c : Conditions) :=
  (available ∧ lawOperative ∧ ¬ c.c1) ∨
  (available ∧ lawOperative ∧ c.c1 ∧ ¬ c.c2) ∨
  (available ∧ lawOperative ∧ c.c1 ∧ c.c2 ∧ ¬ c.c3) ∨
  (available ∧ lawOperative ∧ c.c1 ∧ ¬ c.c4) ∨
  (available ∧ lawOperative ∧ c.c1 ∧ ¬ c.c5)

theorem differential_cover (available lawOperative : Prop) (c : Conditions) :
    diffFailure available lawOperative c ↔
      diffClasses available lawOperative c := by
  grind [diffFailure,diffClasses,all]

theorem no_differential_failure_without_selection (lawOperative : Prop) (c : Conditions) :
    ¬ diffFailure False lawOperative c ∧ ¬ diffClasses False lawOperative c := by
  simp [diffFailure,diffClasses]

theorem failure_series_disjoint (available diffAvailable : Prop) (c : Conditions) :
    ¬ (lawFailure available c ∧ diffFailure diffAvailable (all c) c) := by
  grind [lawFailure,diffFailure]

def allFalse : Conditions := ⟨False,False,False,False,False⟩
theorem false_extension_alone_is_not_failure :
    (¬ allFalse.c1) ∧ ¬ lawFailure False allFalse := by
  simp [allFalse,lawFailure]

#print axioms extension_on_domain
#print axioms extension_outside_domain
#print axioms selection_defines_unique_value
#print axioms matching_law_projection
#print axioms missing_input_unformed
#print axioms missing_input_never_failed
#print axioms failed_requires_available_input
#print axioms law_cover
#print axioms no_law_failure_without_selection
#print axioms differential_cover
#print axioms no_differential_failure_without_selection
#print axioms failure_series_disjoint
#print axioms false_extension_alone_is_not_failure
end LCTR.SelectedInputEvaluation
