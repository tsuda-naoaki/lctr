import Std



namespace LCTR.LawTimeTransport

structure Reindex (T U : Type) where
  forward : T → U
  inverse : U → T
  left : ∀ t, inverse (forward t) = t
  right : ∀ u, forward (inverse u) = u

structure Component (T X Y : Type) where
  evalTime : T → Prop
  input : {t // evalTime t} → X
  output : {t // evalTime t} → Y
  evalDomain : T → X → Prop
  relation : T → X → Y → Prop
  relationTyped : ∀ t x y, relation t x y → evalDomain t x

def transport {T U X Y : Type} (e : Reindex T U) (c : Component T X Y) :
    Component U X Y where
  evalTime u := c.evalTime (e.inverse u)
  input u := c.input ⟨e.inverse u.val, u.property⟩
  output u := c.output ⟨e.inverse u.val, u.property⟩
  evalDomain u x := c.evalDomain (e.inverse u) x
  relation u x y := c.relation (e.inverse u) x y
  relationTyped u x y h := c.relationTyped (e.inverse u) x y h

def liftTime {T U X Y : Type} (e : Reindex T U) (c : Component T X Y)
    (t : {t // c.evalTime t}) : {u // (transport e c).evalTime u} :=
  ⟨e.forward t.val, by simpa [transport, e.left] using t.property⟩

def unliftTime {T U X Y : Type} (e : Reindex T U) (c : Component T X Y)
    (u : {u // (transport e c).evalTime u}) : {t // c.evalTime t} :=
  ⟨e.inverse u.val, u.property⟩

theorem unlift_lift {T U X Y : Type} (e : Reindex T U) (c : Component T X Y)
    (t : {t // c.evalTime t}) : unliftTime e c (liftTime e c t) = t := by
  apply Subtype.ext
  exact e.left t.val

theorem lift_unlift {T U X Y : Type} (e : Reindex T U) (c : Component T X Y)
    (u : {u // (transport e c).evalTime u}) : liftTime e c (unliftTime e c u) = u := by
  apply Subtype.ext
  exact e.right u.val

theorem transported_value_pair {T U X Y : Type} (e : Reindex T U)
    (c : Component T X Y) (t : {t // c.evalTime t}) :
    ((transport e c).input (liftTime e c t), (transport e c).output (liftTime e c t)) =
    (c.input t, c.output t) := by
  change (c.input (unliftTime e c (liftTime e c t)),
    c.output (unliftTime e c (liftTime e c t))) = _
  rw [unlift_lift]

def IndividualAdmissible {T X Y : Type} (c : Component T X Y) : Prop :=
  (∃ t, c.evalTime t) ∧ ∀ t : {t // c.evalTime t}, c.evalDomain t.val (c.input t)

def RightUnique {T X Y : Type} (c : Component T X Y) : Prop :=
  ∀ t x y z, c.relation t x y → c.relation t x z → y = z

def GeneratedMember {T X Y : Type} (c : Component T X Y) : Prop :=
  ∀ t : {t // c.evalTime t}, c.relation t.val (c.input t) (c.output t)

theorem individual_admissibility_preserved {T U X Y : Type} (e : Reindex T U)
    (c : Component T X Y) : IndividualAdmissible (transport e c) ↔ IndividualAdmissible c := by
  constructor
  · intro ⟨⟨u, hu⟩, all⟩
    refine ⟨⟨e.inverse u, hu⟩, ?_⟩
    intro t
    have h := all (liftTime e c t)
    change c.evalDomain (e.inverse (e.forward t.val))
      (c.input (unliftTime e c (liftTime e c t))) at h
    simpa [unlift_lift, e.left] using h
  · intro ⟨⟨t, ht⟩, all⟩
    refine ⟨⟨e.forward t, ?_⟩, ?_⟩
    · simpa [transport, e.left] using ht
    · intro u
      exact all (unliftTime e c u)

theorem right_uniqueness_preserved {T U X Y : Type} (e : Reindex T U)
    (c : Component T X Y) : RightUnique (transport e c) ↔ RightUnique c := by
  constructor
  · intro h t x y z hy hz
    apply h (e.forward t) x y z
    · simpa [transport, e.left] using hy
    · simpa [transport, e.left] using hz
  · intro h u x y z hy hz
    exact h (e.inverse u) x y z hy hz

theorem generated_membership_preserved {T U X Y : Type} (e : Reindex T U)
    (c : Component T X Y) : GeneratedMember (transport e c) ↔ GeneratedMember c := by
  constructor
  · intro all t
    have h := all (liftTime e c t)
    change c.relation (e.inverse (e.forward t.val))
      (c.input (unliftTime e c (liftTime e c t)))
      (c.output (unliftTime e c (liftTime e c t))) at h
    simpa [unlift_lift, e.left] using h
  · intro all u
    exact all (unliftTime e c u)

def ValidAt {T X Y : Type} (c : Component T X Y) (t : T) : Prop :=
  ∃ h : c.evalTime t, c.relation t (c.input ⟨t, h⟩) (c.output ⟨t, h⟩)

theorem valid_time_transport {T U X Y : Type} (e : Reindex T U)
    (c : Component T X Y) (u : U) :
    ValidAt (transport e c) u ↔ ValidAt c (e.inverse u) := Iff.rfl

theorem common_valid_nonempty_preserved {T U A : Type} {X Y : A → Type}
    (e : Reindex T U) (c : (a : A) → Component T (X a) (Y a)) :
    (∃ u, ∀ a, ValidAt (transport e (c a)) u) ↔ (∃ t, ∀ a, ValidAt (c a) t) := by
  constructor
  · intro ⟨u, hu⟩
    exact ⟨e.inverse u, hu⟩
  · intro ⟨t, ht⟩
    refine ⟨e.forward t, ?_⟩
    intro a
    simpa [valid_time_transport, e.left] using ht a

 
theorem conjugated_invariance {T U : Type} (e : Reindex T U)
    (P : T → Prop) (f : T → T) :
    (∀ u, P (e.inverse (e.forward (f (e.inverse u)))) ↔ P (e.inverse u)) ↔
    (∀ t, P (f t) ↔ P t) := by
  constructor
  · intro h t
    simpa [e.left] using h (e.forward t)
  · intro h u
    simpa [e.left] using h (e.inverse u)

 
theorem fixed_zero_not_in_shifted_nat_image :
    ¬ ∃ n : Nat, n + 2 = 0 := by omega

#print axioms unlift_lift
#print axioms lift_unlift
#print axioms transported_value_pair
#print axioms individual_admissibility_preserved
#print axioms right_uniqueness_preserved
#print axioms generated_membership_preserved
#print axioms valid_time_transport
#print axioms common_valid_nonempty_preserved
#print axioms conjugated_invariance
#print axioms fixed_zero_not_in_shifted_nat_image
end LCTR.LawTimeTransport
