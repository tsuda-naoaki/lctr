import Chapter02LeanBridge

namespace LCTR.CoreCarrierPatterns

open LCTR.Chapter02
universe u

structure Input where
  Index : Type u
  Scene : Type u
  Tracked : Type u
  Local : Scene → Role → Type u
  binding : BindingSpec Local
  abstracted : Tracked → {sc : Scene} → Local sc .body → Prop
  assign : Index → ObjectSpecData Local binding abstracted
  selected : Set Index

abbrev IndexAt (a : Input) := {i : a.Index // i ∈ a.selected}
abbrev RI (a : Input) := RoleInstance a.Local a.binding a.abstracted a.assign

def roleAt (a : Input) (r : Role) (i : IndexAt a) : RI a :=
  roleInstance a.Local a.binding a.abstracted a.assign r i.val

abbrev RoleDomain (a : Input) (r : RealizationRole) :=
  {x : RI a // ∃ i : IndexAt a, roleAt a r.val i = x}

def domainAt (a : Input) (r : RealizationRole) (i : IndexAt a) : RoleDomain a r :=
  ⟨roleAt a r.val i, i, rfl⟩

def bodyPair (a : Input) (i : IndexAt a) : a.Tracked × RI a :=
  ((a.assign i.val).tracked, roleAt a .body i)

structure Physical (a : Input) where
  Carrier : RealizationRole → Type u
  Communication : Type u
  realize : (r : RealizationRole) → RoleDomain a r → Carrier r
  couples : Communication → Carrier realizationObserver → Carrier realizationObserver → Prop

def carrierAt {a : Input} (p : Physical a) (r : RealizationRole) (i : IndexAt a) : p.Carrier r :=
  p.realize r (domainAt a r i)

inductive ComparisonRole where | clock | detector
deriving DecidableEq

def comparisonRole : ComparisonRole → RealizationRole
  | .clock => realizationClock
  | .detector => realizationDetector

inductive ComparisonChoice where | shared | separated
deriving DecidableEq

def comparisonCondition {X : Type u} : ComparisonChoice → X → X → Prop
  | .shared, x, y => x = y
  | .separated, x, y => x ≠ y

inductive ObserverChoice where | shared | distributed
deriving DecidableEq

def observerCondition {a : Input} (p : Physical a) :
    ObserverChoice → p.Carrier realizationObserver → p.Carrier realizationObserver → Prop
  | .shared, x, y => x = y
  | .distributed, x, y => x ≠ y ∧ ∃ c : p.Communication, p.couples c x y

structure Assembled {a : Input} (p : Physical a) where
  clock : p.Carrier realizationClock × p.Carrier realizationClock
  detector : p.Carrier realizationDetector × p.Carrier realizationDetector
  observer : p.Carrier realizationObserver × p.Carrier realizationObserver
  body : (k : Fin 2) → a.Tracked × RI a

def assemble {a : Input} (p : Physical a) (i : Fin 2 → IndexAt a) : Assembled p where
  clock := (carrierAt p realizationClock (i 0), carrierAt p realizationClock (i 1))
  detector := (carrierAt p realizationDetector (i 0), carrierAt p realizationDetector (i 1))
  observer := (carrierAt p realizationObserver (i 0), carrierAt p realizationObserver (i 1))
  body := fun k => bodyPair a (i k)

theorem realization_domain_exact (a : Input) (r : RealizationRole) (x : RI a) :
    (∃ y : RoleDomain a r, y.val = x) ↔ ∃ i : IndexAt a, roleAt a r.val i = x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

theorem role_index_preserved (a : Input) (r : Role) (i : IndexAt a) :
    (roleAt a r i).zeta = i.val ∧ (roleAt a r i).role = r := by
  exact ⟨rfl, rfl⟩

theorem body_pair_distinct (a : Input) (i j : IndexAt a) (h : i ≠ j) :
    bodyPair a i ≠ bodyPair a j := by
  intro same
  have indices : i.val = j.val := congrArg (fun x => x.2.zeta) same
  exact h (Subtype.ext indices)

theorem body_abstraction_retained (a : Input) (i : IndexAt a) :
    a.abstracted (bodyPair a i).1 (a.assign i.val).witness.body :=
  (a.assign i.val).bodyAbstractedFrom

theorem carrier_condition_from_specified_values {a : Input} (p : Physical a)
    (i : Fin 2 → IndexAt a) (r : ComparisonRole) (choice : ComparisonChoice)
    (v : Fin 2 → p.Carrier (comparisonRole r))
    (hAt : ∀ k, carrierAt p (comparisonRole r) (i k) = v k)
    (hChoice : comparisonCondition choice (v 0) (v 1)) :
    comparisonCondition choice
      (carrierAt p (comparisonRole r) (i 0)) (carrierAt p (comparisonRole r) (i 1)) := by
  rw [hAt 0, hAt 1]
  exact hChoice

theorem role_typed_combination {a : Input} (p : Physical a)
    (i : Fin 2 → IndexAt a) (hi : i 0 ≠ i 1)
    (choice : ComparisonRole → ComparisonChoice) (oChoice : ObserverChoice)
    (v : (r : ComparisonRole) → Fin 2 → p.Carrier (comparisonRole r))
    (hAt : ∀ r k, carrierAt p (comparisonRole r) (i k) = v r k)
    (hChoice : ∀ r, comparisonCondition (choice r) (v r 0) (v r 1))
    (hObserver : observerCondition p oChoice
      (carrierAt p realizationObserver (i 0)) (carrierAt p realizationObserver (i 1))) :
    comparisonCondition (choice .clock) (assemble p i).clock.1 (assemble p i).clock.2 ∧
    comparisonCondition (choice .detector) (assemble p i).detector.1 (assemble p i).detector.2 ∧
    observerCondition p oChoice (assemble p i).observer.1 (assemble p i).observer.2 ∧
    (∀ k, (assemble p i).body k = bodyPair a (i k)) ∧
    (assemble p i).body 0 ≠ (assemble p i).body 1 := by
  exact ⟨carrier_condition_from_specified_values p i .clock (choice .clock)
      (v .clock) (hAt .clock) (hChoice .clock),
    carrier_condition_from_specified_values p i .detector (choice .detector)
      (v .detector) (hAt .detector) (hChoice .detector),
    hObserver, fun _ => rfl, body_pair_distinct a (i 0) (i 1) hi⟩

theorem body_independent_of_realization {a : Input} (p q : Physical a)
    (i : Fin 2 → IndexAt a) : (assemble p i).body = (assemble q i).body := by
  rfl

theorem carrier_condition_locality {a : Input} (p : Physical a) (r : ComparisonRole)
    (choice : ComparisonChoice) (i j : Fin 2 → IndexAt a)
    (same : ∀ k, carrierAt p (comparisonRole r) (i k) = carrierAt p (comparisonRole r) (j k)) :
    comparisonCondition choice (carrierAt p (comparisonRole r) (i 0))
      (carrierAt p (comparisonRole r) (i 1)) ↔
    comparisonCondition choice (carrierAt p (comparisonRole r) (j 0))
      (carrierAt p (comparisonRole r) (j 1)) := by
  rw [same 0, same 1]

theorem no_distribution_without_communication {a : Input} (p : Physical a)
    (x y : p.Carrier realizationObserver) (none : ∀ c, ¬ p.couples c x y) :
    ¬ observerCondition p .distributed x y := by
  rintro ⟨_, c, h⟩
  exact none c h

theorem physical_identity_does_not_merge_roles (a : Input) (r : Role)
    (i j : IndexAt a) (different : i ≠ j) : roleAt a r i ≠ roleAt a r j := by
  intro same
  exact different (Subtype.ext (congrArg RoleInstance.zeta same))

end LCTR.CoreCarrierPatterns
