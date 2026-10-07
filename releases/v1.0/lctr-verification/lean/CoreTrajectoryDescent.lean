import Mathlib.Logic.Relation
import LCTR.CanonicalGraphTrajectoryCurrentPaper

namespace LCTR.CoreTrajectoryDescent
set_option autoImplicit false
universe u v w
variable {C : Type u} {D : Type v} {B : Type w}

def genC (r : C → D → B → Prop) (bind : C × D × B → C × D × B → Prop)
    (x y : C) : Prop :=
  ∃ d b d' b', r x d b ∧ r y d' b' ∧ bind (x,d,b) (y,d',b')
def genB (r : C → D → B → Prop) (bind : C × D × B → C × D × B → Prop)
    (x y : B) : Prop :=
  ∃ c d c' d', r c d x ∧ r c' d' y ∧ bind (c,d,x) (c',d',y)

theorem generated_equivalence_least {X : Type u} (g E : X → X → Prop)
    (eqv : Equivalence E) (contains : ∀ x y, g x y → E x y) :
    ∀ x y, Relation.EqvGen g x y → E x y := by
  intro x y h
  induction h with
  | rel a b hab => exact contains a b hab
  | refl a => exact eqv.refl a
  | symm a b _ ih => exact eqv.symm ih
  | trans a b c _ _ ih₁ ih₂ => exact eqv.trans ih₁ ih₂

abbrev Q {X : Type u} (g : X → X → Prop) := Quotient (Relation.EqvGen.setoid g)
def prj {X : Type u} (g : X → X → Prop) (x : X) : Q g := Quotient.mk _ x
def source (r : C → D → B → Prop) (c : C) (b : B) : Prop := ∃ d, r c d b
def imageRelation (gc : C → C → Prop) (gb : B → B → Prop) (r : C → D → B → Prop)
    (t : Q gc) (s : Q gb) : Prop :=
  ∃ c b, source r c b ∧ prj gc c = t ∧ prj gb b = s
def Desc (gc : C → C → Prop) (gb : B → B → Prop) (r : C → D → B → Prop) : Prop :=
  ∀ c c' b b', Relation.EqvGen gc c c' → Relation.EqvGen gb b b' →
    (source r c b ↔ source r c' b')

theorem image_membership_iff (gc : C → C → Prop) (gb : B → B → Prop)
    (r : C → D → B → Prop) (desc : Desc gc gb r) (c : C) (b : B) :
    imageRelation gc gb r (prj gc c) (prj gb b) ↔ source r c b := by
  constructor
  · rintro ⟨c',b',h,hc,hb⟩
    exact (desc c' c b' b (Quotient.exact hc) (Quotient.exact hb)).mp h
  · intro h
    exact ⟨c,b,h,rfl,rfl⟩

theorem descent_iff_exact_membership (gc : C → C → Prop) (gb : B → B → Prop)
    (r : C → D → B → Prop) :
    Desc gc gb r ↔ ∀ c b, imageRelation gc gb r (prj gc c) (prj gb b) ↔ source r c b := by
  constructor
  · exact image_membership_iff gc gb r
  · intro h c c' b b' hc hb
    have ec : prj gc c = prj gc c' := Quotient.sound hc
    have eb : prj gb b = prj gb b' := Quotient.sound hb
    rw [← h c b,← h c' b',ec,eb]

theorem generated_closure_descent (r : C → D → B → Prop)
    (bind : C × D × B → C × D × B → Prop)
    (desc : Desc (genC r bind) (genB r bind) r)
    (c c' : C) (b b' : B)
    (hc : Relation.EqvGen (genC r bind) c c')
    (hb : Relation.EqvGen (genB r bind) b b') :
    imageRelation (genC r bind) (genB r bind) r (prj _ c) (prj _ b) ↔
    imageRelation (genC r bind) (genB r bind) r (prj _ c') (prj _ b') := by
  rw [image_membership_iff _ _ _ desc,image_membership_iff _ _ _ desc]
  exact desc c c' b b' hc hb

theorem domain_is_source_image (gc : C → C → Prop) (gb : B → B → Prop)
    (r : C → D → B → Prop) (t : Q gc) :
    (∃ s, imageRelation gc gb r t s) ↔ ∃ c b, source r c b ∧ prj gc c = t := by
  constructor
  · rintro ⟨s,c,b,h,hc,_⟩
    exact ⟨c,b,h,hc⟩
  · rintro ⟨c,b,h,hc⟩
    exact ⟨prj gb b,c,b,h,hc,rfl⟩

theorem native_graph_trajectory (r : C → D → B → Prop)
    (bind : C × D × B → C × D × B → Prop)
    (single : ∀ t s₀ s₁, imageRelation (genC r bind) (genB r bind) r t s₀ →
      imageRelation (genC r bind) (genB r bind) r t s₁ → s₀ = s₁) :
    ∃ trajectory : {t : Q (genC r bind) // ∃ s, imageRelation (genC r bind) (genB r bind) r t s} → Q (genB r bind),
      (∀ p : {t : Q (genC r bind) // ∃ s, imageRelation (genC r bind) (genB r bind) r t s} × Q (genB r bind),
        imageRelation (genC r bind) (genB r bind) r p.1.1 p.2 ↔ p.2 = trajectory p.1) ∧
      ∀ other, (∀ p : {t : Q (genC r bind) // ∃ s, imageRelation (genC r bind) (genB r bind) r t s} × Q (genB r bind),
        imageRelation (genC r bind) (genB r bind) r p.1.1 p.2 ↔ p.2 = other p.1) → other = trajectory := by
  exact LCTR.CurrentPaperCorrespondence.canonical_graph_trajectory_existence_and_uniqueness
    (imageRelation (genC r bind) (genB r bind) r) single

theorem empty_relation_domain (gc : C → C → Prop) (gb : B → B → Prop) (t : Q gc) :
    ¬ ∃ s, imageRelation gc gb (fun (_ : C) (_ : D) (_ : B) => False) t s := by
  rintro ⟨s,c,b,⟨d,h⟩,_⟩
  exact h

theorem missing_descent_control :
    imageRelation (fun (_ _ : Bool) => True) (fun (_ _ : Unit) => False)
      (fun c (_ : Unit) (_ : Unit) => c = true) (prj _ false) (prj _ ()) ∧
    ¬ source (fun c (_ : Unit) (_ : Unit) => c = true) false () := by
  constructor
  · exact ⟨true,(),⟨(),rfl⟩,Quotient.sound (.rel _ _ trivial),rfl⟩
  · rintro ⟨_,h⟩
    cases h

end LCTR.CoreTrajectoryDescent
