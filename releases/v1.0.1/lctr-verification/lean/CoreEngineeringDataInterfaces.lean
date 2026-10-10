import CoreAuditStateTransport
import Mathlib.Data.ENNReal.Basic

namespace LCTR.CoreEngineeringDataInterfaces
set_option autoImplicit false
open Set LCTR.CoreAuditStateTransport
open scoped ENNReal
variable {I L O Z X Q C V : Type}

def engineeringSpec (input : I) (ev : I × O × Z) (_scale : L) (observer : O) (target : Z) : Prop :=
  ev = (input, observer, target)

theorem engineering_components (input : I) (ev : I × O × Z) (scale : L) (o : O) (z : Z) :
    engineeringSpec input ev scale o z ↔ ev.1 = input ∧ ev.2.1 = o ∧ ev.2.2 = z := by
  rcases ev with ⟨i,a,b⟩
  simp [engineeringSpec]

def pairSpec (inputOf : X → I) (operative : X → Prop) (a b : I × O × Z) : Prop :=
  ∃ x o z₁ z₂, operative x ∧ z₁ ≠ z₂ ∧ a = (inputOf x,o,z₁) ∧ b = (inputOf x,o,z₂)

theorem pair_common_context (inputOf : X → I) (operative : X → Prop) (a b : I × O × Z)
    (h : pairSpec inputOf operative a b) :
    a.1 = b.1 ∧ a.2.1 = b.2.1 ∧ a.2.2 ≠ b.2.2 ∧ ∃ x, operative x ∧ a.1 = inputOf x := by
  obtain ⟨x,o,z₁,z₂,hx,hz,rfl,rfl⟩ := h
  exact ⟨rfl,rfl,hz,x,hx,rfl⟩

def closedIntervals {A : Type} [LinearOrder A] (S : Set A) : Set (A × A) :=
  {p | p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 ≤ p.2}

theorem interval_membership {A : Type} [LinearOrder A] (S : Set A) (l r : A) :
    (l,r) ∈ closedIntervals S ↔ l ∈ S ∧ r ∈ S ∧ l ≤ r := Iff.rfl

structure Interval (A : Type) [LinearOrder A] where
  lower : A
  upper : A
  ordered : lower ≤ upper

def intervalAudit {A : Type} [LinearOrder A] (p : Interval A) (theta : A) : AuditStatus :=
  if p.upper ≤ theta then .pass else if theta < p.lower then .fail else .indeterminate

theorem interval_pass {A : Type} [LinearOrder A] (p : Interval A) (theta : A) :
    intervalAudit p theta = .pass ↔ p.upper ≤ theta := by
  unfold intervalAudit
  split_ifs <;> simp_all

theorem interval_fail {A : Type} [LinearOrder A] (p : Interval A) (theta : A) :
    intervalAudit p theta = .fail ↔ theta < p.lower := by
  by_cases upper : p.upper ≤ theta
  · have lower : ¬ theta < p.lower := not_lt.mpr (le_trans p.ordered upper)
    simp [intervalAudit,upper,lower]
  · simp [intervalAudit,upper]

theorem interval_indeterminate {A : Type} [LinearOrder A] (p : Interval A) (theta : A) :
    intervalAudit p theta = .indeterminate ↔ p.lower ≤ theta ∧ theta < p.upper := by
  by_cases upper : p.upper ≤ theta
  · simp [intervalAudit,upper,not_lt.mpr upper]
  · by_cases lower : theta < p.lower
    · simp [intervalAudit,upper,lower,not_le.mpr lower]
    · simp [intervalAudit,upper,lower,not_lt.mp lower,lt_of_not_ge upper]

theorem interval_range {A : Type} [LinearOrder A] (p : Interval A) (theta : A) :
    intervalAudit p theta = .pass ∨ intervalAudit p theta = .fail ∨
      intervalAudit p theta = .indeterminate := by
  unfold intervalAudit
  split_ifs <;> simp

theorem threshold_equality_pass {A : Type} [LinearOrder A] (p : Interval A) :
    intervalAudit p p.upper = .pass := by simp [intervalAudit]

theorem infinite_threshold_pass (p : Interval ℝ≥0∞) :
    intervalAudit p ⊤ = .pass := by simp [intervalAudit]

structure ViewData (C O L Q : Type) where
  carrier : C
  observer : O
  scale : L
  view : Set Q

def viewData (carrierAt : Z → C) (z : Z) (o : O) (l : L) (view : Set Q) : ViewData C O L Q :=
  ⟨carrierAt z,o,l,view⟩

theorem view_components (carrierAt : Z → C) (z : Z) (o : O) (l : L) (view : Set Q) :
    (viewData carrierAt z o l view).carrier = carrierAt z ∧
    (viewData carrierAt z o l view).observer = o ∧
    (viewData carrierAt z o l view).scale = l ∧
    (viewData carrierAt z o l view).view = view := ⟨rfl,rfl,rfl,rfl⟩

def viewRelation (relation : Q → V → Prop) (view : Set Q) (q : Q) (v : V) : Prop :=
  relation q v ∧ q ∈ view

theorem restricted_relation (relation : Q → V → Prop) (view : Set Q) (q : Q) (v : V) :
    viewRelation relation view q v ↔ relation q v ∧ q ∈ view := Iff.rfl

theorem restricted_domain (relation : Q → V → Prop) (view : Set Q) (q : Q) :
    (∃ v, viewRelation relation view q v) ↔ q ∈ view ∧ ∃ v, relation q v := by
  simp only [viewRelation]
  constructor
  · rintro ⟨v,hv,hq⟩; exact ⟨hq,v,hv⟩
  · rintro ⟨hq,v,hv⟩; exact ⟨v,hv,hq⟩

def bulk (carriers : Fin 2 → C) : Prop := carriers 0 = carriers 1
def following (carriers : Fin 2 → C) (views : Fin 2 → Set Q) (relation : Q → V → Prop) : Prop :=
  carriers 0 ≠ carriers 1 ∧ ∀ k q, q ∈ views k → ∃ v, viewRelation relation (views k) q v

theorem following_exact (carriers : Fin 2 → C) (views : Fin 2 → Set Q) (relation : Q → V → Prop) :
    following carriers views relation ↔
      carriers 0 ≠ carriers 1 ∧ ∀ k q, q ∈ views k → ∃ v, relation q v := by
  constructor
  · rintro ⟨different,covered⟩
    exact ⟨different,fun k q hq => ((restricted_domain relation (views k) q).mp (covered k q hq)).2⟩
  · rintro ⟨different,covered⟩
    exact ⟨different,fun k q hq => (restricted_domain relation (views k) q).mpr ⟨hq,covered k q hq⟩⟩

theorem following_not_bulk (carriers : Fin 2 → C) (views : Fin 2 → Set Q) (relation : Q → V → Prop)
    (h : following carriers views relation) : ¬ bulk carriers := h.1

theorem empty_views (carriers : Fin 2 → C) (relation : Q → V → Prop) :
    following carriers (fun _ => ∅) relation ↔ carriers 0 ≠ carriers 1 := by
  simp [following]

theorem missing_record_excludes_following (carriers : Fin 2 → C) (views : Fin 2 → Set Q)
    (relation : Q → V → Prop) (k : Fin 2) (q : Q) (hq : q ∈ views k)
    (missing : ∀ v, ¬ relation q v) : ¬ following carriers views relation := by
  intro h
  obtain ⟨v,hv⟩ := ((following_exact carriers views relation).mp h).2 k q hq
  exact missing v hv

structure InvasivenessData (Q : Type) where
  relation : Set (Q × Q)
  interval : Interval ℝ≥0∞
  tolerance : ℝ≥0∞

noncomputable def invasivenessAudit (d : InvasivenessData Q) : AuditStatus := intervalAudit d.interval d.tolerance

theorem invasiveness_components (relation : Set (Q × Q)) (interval : Interval ℝ≥0∞) (tolerance : ℝ≥0∞) :
    let d : InvasivenessData Q := ⟨relation,interval,tolerance⟩
    d.relation = relation ∧ d.interval = interval ∧ d.tolerance = tolerance := ⟨rfl,rfl,rfl⟩

theorem invasiveness_exact (d : InvasivenessData Q) :
    (invasivenessAudit d = .pass ↔ d.interval.upper ≤ d.tolerance) ∧
    (invasivenessAudit d = .fail ↔ d.tolerance < d.interval.lower) ∧
    (invasivenessAudit d = .indeterminate ↔
      d.interval.lower ≤ d.tolerance ∧ d.tolerance < d.interval.upper) :=
  ⟨interval_pass _ _,interval_fail _ _,interval_indeterminate _ _⟩

end LCTR.CoreEngineeringDataInterfaces
