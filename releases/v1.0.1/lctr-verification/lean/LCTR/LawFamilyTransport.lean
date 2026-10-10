import LCTR.LawTimeTransport





namespace LCTR.LawFamilyTransport
open LCTR.LawTimeTransport

abbrev Tuple (T X Y : Type) := (T × X) × Y

def tupleReindex {T U X Y : Type} (e : Reindex T U) :
    Reindex (Tuple T X Y) (Tuple U X Y) where
  forward z := ((e.forward z.1.1, z.1.2), z.2)
  inverse z := ((e.inverse z.1.1, z.1.2), z.2)
  left z := by rcases z with ⟨⟨t, x⟩, y⟩; simp [e.left]
  right z := by rcases z with ⟨⟨u, x⟩, y⟩; simp [e.right]

def conjugate {T U : Type} (e : Reindex T U) (f : Reindex T T) : Reindex U U where
  forward u := e.forward (f.forward (e.inverse u))
  inverse u := e.forward (f.inverse (e.inverse u))
  left u := by simp [e.left, f.left, e.right]
  right u := by simp [e.left, f.right, e.right]

def image {T U : Type} (e : Reindex T U) (P : T → Prop) : U → Prop :=
  fun u => P (e.inverse u)

theorem image_membership {T U : Type} (e : Reindex T U) (P : T → Prop) (u : U) :
    image e P u ↔ ∃ t, P t ∧ e.forward t = u := by
  constructor
  · intro h; exact ⟨e.inverse u, h, e.right u⟩
  · rintro ⟨t, ht, rfl⟩; simpa [image, e.left] using ht

def tupleRelation {T X Y : Type} (c : Component T X Y) : Tuple T X Y → Prop :=
  fun z => c.relation z.1.1 z.1.2 z.2

def evalTuple {T X Y : Type} (c : Component T X Y) (t : {t // c.evalTime t}) :
    Tuple T X Y := ((t.val, c.input t), c.output t)

theorem evaluation_tuple_transport {T U X Y : Type} (e : Reindex T U)
    (c : Component T X Y) (t : {t // c.evalTime t}) :
    evalTuple (transport e c) (liftTime e c t) =
      (tupleReindex e).forward (evalTuple c t) := by
  exact congrArg (fun pair : X × Y => ((e.forward t.val, pair.1), pair.2))
    (transported_value_pair e c t)

theorem relation_image_transport {T U X Y : Type} (e : Reindex T U)
    (c : Component T X Y) (z : Tuple U X Y) :
    tupleRelation (transport e c) z ↔ image (tupleReindex e) (tupleRelation c) z :=
  Iff.rfl

def ImageInvariant {T : Type} (P : T → Prop) (f : Reindex T T) : Prop :=
  ∀ z, (∃ w, P w ∧ f.forward w = z) ↔ P z

theorem image_invariance_iff {T : Type} (P : T → Prop) (f : Reindex T T) :
    ImageInvariant P f ↔ ∀ z, P (f.forward z) ↔ P z := by
  constructor
  · intro h z
    constructor
    · intro hz
      obtain ⟨w, hw, eq⟩ := (h (f.forward z)).mpr hz
      have wz : w = z := by
        have q := congrArg f.inverse eq
        simpa [f.left] using q
      simpa [wz] using hw
    · intro hz
      exact (h (f.forward z)).mp ⟨z, hz, rfl⟩
  · intro h z
    constructor
    · rintro ⟨w, hw, rfl⟩; exact (h w).mpr hw
    · intro hz
      refine ⟨f.inverse z, ?_, f.right z⟩
      exact (h (f.inverse z)).mp (by simpa [f.right] using hz)

theorem conjugate_image_invariance {T U : Type} (e : Reindex T U)
    (P : T → Prop) (f : Reindex T T) :
    ImageInvariant (image e P) (conjugate e f) ↔ ImageInvariant P f := by
  rw [image_invariance_iff, image_invariance_iff]
  exact conjugated_invariance e P f.forward

structure Family (T A : Type) (X Y : A → Type) where
  indicesNonempty : Nonempty A
  component : (a : A) → Component T (X a) (Y a)
  admissibleCommon : (T → Prop) → Prop
  faithful : ((a : A) → Reindex (Tuple T (X a) (Y a)) (Tuple T (X a) (Y a))) → Prop

def transportFamily {T U A : Type} {X Y : A → Type} (e : Reindex T U)
    (d : Family T A X Y) : Family U A X Y where
  indicesNonempty := d.indicesNonempty
  component a := transport e (d.component a)
  admissibleCommon Q := d.admissibleCommon (fun t => Q (e.forward t))
  faithful psi := ∃ phi, d.faithful phi ∧
    psi = fun a => conjugate (tupleReindex e) (phi a)

def common {T A : Type} {X Y : A → Type} (d : Family T A X Y) : T → Prop :=
  fun t => ∀ a, ValidAt (d.component a) t

def K1 {T A : Type} {X Y : A → Type} (d : Family T A X Y) : Prop :=
  ∀ a, IndividualAdmissible (d.component a)

def K2 {T A : Type} {X Y : A → Type} (d : Family T A X Y) : Prop :=
  ∀ a, RightUnique (d.component a)

def K3 {T A : Type} {X Y : A → Type} (d : Family T A X Y) : Prop :=
  K1 d ∧ ∀ a, GeneratedMember (d.component a)

def K4 {T A : Type} {X Y : A → Type} (d : Family T A X Y) : Prop :=
  ∀ phi, d.faithful phi → ∀ a, ImageInvariant (tupleRelation (d.component a)) (phi a)

def K5 {T A : Type} {X Y : A → Type} (d : Family T A X Y) : Prop :=
  K3 d ∧ (∃ t, common d t) ∧ d.admissibleCommon (common d)

theorem admissible_family_is_image {T U A : Type} {X Y : A → Type}
    (e : Reindex T U) (d : Family T A X Y) (Q : U → Prop) :
    (transportFamily e d).admissibleCommon Q ↔
      ∃ P, d.admissibleCommon P ∧ Q = image e P := by
  constructor
  · intro h
    refine ⟨(fun t => Q (e.forward t)), h, ?_⟩
    funext u
    simp [image, e.right]
  · rintro ⟨P, hP, rfl⟩
    change d.admissibleCommon (fun t => P (e.inverse (e.forward t)))
    simpa [e.left] using hP

theorem common_is_image {T U A : Type} {X Y : A → Type}
    (e : Reindex T U) (d : Family T A X Y) :
    common (transportFamily e d) = image e (common d) := rfl

theorem common_pullback {T U A : Type} {X Y : A → Type}
    (e : Reindex T U) (d : Family T A X Y) :
    (fun t => common (transportFamily e d) (e.forward t)) = common d := by
  funext t
  simp only [common_is_image, image, e.left]

theorem condition1_preserved {T U A : Type} {X Y : A → Type}
    (e : Reindex T U) (d : Family T A X Y) : K1 (transportFamily e d) ↔ K1 d := by
  unfold K1
  exact forall_congr' (fun a => individual_admissibility_preserved e (d.component a))

theorem condition2_preserved {T U A : Type} {X Y : A → Type}
    (e : Reindex T U) (d : Family T A X Y) : K2 (transportFamily e d) ↔ K2 d := by
  unfold K2
  exact forall_congr' (fun a => right_uniqueness_preserved e (d.component a))

theorem condition3_preserved {T U A : Type} {X Y : A → Type}
    (e : Reindex T U) (d : Family T A X Y) : K3 (transportFamily e d) ↔ K3 d := by
  unfold K3
  exact and_congr (condition1_preserved e d)
    (forall_congr' (fun a => generated_membership_preserved e (d.component a)))

theorem condition4_preserved {T U A : Type} {X Y : A → Type}
    (e : Reindex T U) (d : Family T A X Y) : K4 (transportFamily e d) ↔ K4 d := by
  constructor
  · intro h phi hp a
    have hi := h (fun a => conjugate (tupleReindex e) (phi a)) ⟨phi, hp, rfl⟩ a
    exact (conjugate_image_invariance (tupleReindex e)
      (tupleRelation (d.component a)) (phi a)).mp hi
  · intro h psi hp a
    obtain ⟨phi, hphi, rfl⟩ := hp
    exact (conjugate_image_invariance (tupleReindex e)
      (tupleRelation (d.component a)) (phi a)).mpr (h phi hphi a)

theorem condition5_preserved {T U A : Type} {X Y : A → Type}
    (e : Reindex T U) (d : Family T A X Y) : K5 (transportFamily e d) ↔ K5 d := by
  unfold K5
  apply and_congr (condition3_preserved e d)
  apply and_congr
  · exact common_valid_nonempty_preserved e d.component
  · change d.admissibleCommon (fun t => common (transportFamily e d) (e.forward t)) ↔ _
    rw [common_pullback]

def AllConditions {T A : Type} {X Y : A → Type} (d : Family T A X Y) : Prop :=
  K1 d ∧ K2 d ∧ K3 d ∧ K4 d ∧ K5 d

theorem five_conditions_preserved {T U A : Type} {X Y : A → Type}
    (e : Reindex T U) (d : Family T A X Y) :
    AllConditions (transportFamily e d) ↔ AllConditions d := by
  unfold AllConditions
  rw [condition1_preserved, condition2_preserved, condition3_preserved,
    condition4_preserved, condition5_preserved]

 
 
def identityReindex (T : Type) : Reindex T T where
  forward := id
  inverse := id
  left _ := rfl
  right _ := rfl

def flipValues : Reindex (Tuple Nat Bool Bool) (Tuple Nat Bool Bool) where
  forward z := ((z.1.1, !z.1.2), !z.2)
  inverse z := ((z.1.1, !z.1.2), !z.2)
  left z := by rcases z with ⟨⟨t,x⟩,y⟩; simp
  right z := by rcases z with ⟨⟨t,x⟩,y⟩; simp

def constantComponent : Component Nat Bool Bool where
  evalTime _ := True
  input _ := false
  output _ := false
  evalDomain _ _ := True
  relation _ x y := y = x
  relationTyped _ _ _ _ := True.intro

def exampleFamily : Family Nat Unit (fun _ => Bool) (fun _ => Bool) where
  indicesNonempty := ⟨()⟩
  component _ := constantComponent
  admissibleCommon P := ∃ t, P t
  faithful phi := phi () = identityReindex _ ∨ phi () = flipValues

theorem example_conditions_nonvacuous : AllConditions exampleFamily := by
  have h1 : K1 exampleFamily := by
    intro a
    exact ⟨⟨0, True.intro⟩, fun _ => True.intro⟩
  have h2 : K2 exampleFamily := by
    intro a t x y z hy hz
    exact hy.trans hz.symm
  have h3 : K3 exampleFamily := by
    exact ⟨h1, fun _ _ => rfl⟩
  have h4 : K4 exampleFamily := by
    intro phi hp a
    cases a
    rw [image_invariance_iff]
    intro z
    rcases hp with hp | hp
    · rw [hp]; rfl
    · rw [hp]
      rcases z with ⟨⟨t,x⟩,y⟩
      cases x <;> cases y <;> simp [tupleRelation, exampleFamily, constantComponent, flipValues]
  have hc : common exampleFamily 0 := by
    intro a
    exact ⟨True.intro, rfl⟩
  exact ⟨h1,h2,h3,h4,h3,⟨0,hc⟩,⟨0,hc⟩⟩

def shiftByTwo : Reindex Nat {n : Nat // 2 ≤ n} where
  forward n := ⟨n+2, by omega⟩
  inverse n := n.val-2
  left n := by simp
  right n := by apply Subtype.ext; dsimp; have hn := n.property; omega

theorem shifted_example_conditions : AllConditions (transportFamily shiftByTwo exampleFamily) :=
  (five_conditions_preserved shiftByTwo exampleFamily).mpr example_conditions_nonvacuous

#print axioms image_membership
#print axioms evaluation_tuple_transport
#print axioms relation_image_transport
#print axioms image_invariance_iff
#print axioms conjugate_image_invariance
#print axioms admissible_family_is_image
#print axioms common_is_image
#print axioms common_pullback
#print axioms condition1_preserved
#print axioms condition2_preserved
#print axioms condition3_preserved
#print axioms condition4_preserved
#print axioms condition5_preserved
#print axioms five_conditions_preserved
#print axioms example_conditions_nonvacuous
#print axioms shifted_example_conditions
end LCTR.LawFamilyTransport
