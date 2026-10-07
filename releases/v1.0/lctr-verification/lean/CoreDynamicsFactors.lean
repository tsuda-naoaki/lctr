import CoreTrajectoryDescent
import Mathlib.Data.Quot
import Mathlib.Order.Basic
import LCTR.GeneratedOrderUniversal

namespace LCTR.CoreDynamicsFactors
set_option autoImplicit false
open LCTR.CoreTrajectoryDescent
open LCTR.GeneratedOrderUniversal
universe u v w a b
variable {C : Type u} {D : Type v} {B : Type w} {T : Type a} {S : Type b}

theorem native_generated_partial_order (gc : C → C → Prop) (ord : C → C → Prop)
    (anti : ∀ x y, Order (Relation.EqvGen.setoid gc) ord x y →
      Order (Relation.EqvGen.setoid gc) ord y x → x = y) :
    ∃ p : PartialOrder (Q gc), p.le = Order (Relation.EqvGen.setoid gc) ord := by
  let p : PartialOrder (Q gc) :=
    { le := Order (Relation.EqvGen.setoid gc) ord
      le_refl := reflexive _ _
      le_trans := fun _ _ _ => transitive _ _
      le_antisymm := anti }
  exact ⟨p,rfl⟩

theorem native_order_minimality (gc : C → C → Prop) (ord : C → C → Prop)
    (l : Q gc → Q gc → Prop) (lr : ∀ x, l x x)
    (lt : ∀ x y z, l x y → l y z → l x z)
    (lm : ∀ x y, ord x y → l (prj gc x) (prj gc y)) :
    ∀ x y, Order (Relation.EqvGen.setoid gc) ord x y → l x y := by
  exact fun _ _ => least_preorder _ _ l lr lt lm

def imageBy (r : C → D → B → Prop) (gC : C → T) (gB : B → S) (t : T) (s : S) : Prop :=
  ∃ c b, source r c b ∧ gC c = t ∧ gB b = s

theorem trajectory_factor_image (gc : C → C → Prop) (gb : B → B → Prop)
    (r : C → D → B → Prop) (gC : C → T) (gB : B → S)
    (fC : Q gc → T) (fB : Q gb → S)
    (hc : ∀ c, fC (prj gc c) = gC c) (hb : ∀ b, fB (prj gb b) = gB b) (t : T) (s : S) :
    imageBy r gC gB t s ↔ ∃ qt qs, imageRelation gc gb r qt qs ∧ fC qt = t ∧ fB qs = s := by
  constructor
  · rintro ⟨c,b,h,hc',hb'⟩
    exact ⟨prj gc c,prj gb b,⟨c,b,h,rfl,rfl⟩,(hc c).trans hc',(hb b).trans hb'⟩
  · rintro ⟨qt,qs,⟨c,b,h,hcq,hbq⟩,ht,hs⟩
    exact ⟨c,b,h,(hc c).symm.trans ((congrArg fC hcq).trans ht),
      (hb b).symm.trans ((congrArg fB hbq).trans hs)⟩

def FactorPairConditions [Preorder T]
    (gc : C → C → Prop) (gb : B → B → Prop) (ord : C → C → Prop)
    (r : C → D → B → Prop) (gC : C → T) (gB : B → S)
    (f : (Q gc → T) × (Q gb → S)) : Prop :=
  Function.Surjective f.1 ∧ Function.Surjective f.2 ∧
  (∀ c, f.1 (prj gc c) = gC c) ∧ (∀ b, f.2 (prj gb b) = gB b) ∧
  (∀ x y, Order (Relation.EqvGen.setoid gc) ord x y → f.1 x ≤ f.1 y) ∧
  (∀ t s, imageBy r gC gB t s ↔ ∃ qt qs, imageRelation gc gb r qt qs ∧ f.1 qt = t ∧ f.2 qs = s)

theorem native_factor_pair_exists_unique [Preorder T]
    (gc : C → C → Prop) (gb : B → B → Prop) (ord : C → C → Prop)
    (r : C → D → B → Prop) (gC : C → T) (gB : B → S)
    (ontoC : Function.Surjective gC) (ontoB : Function.Surjective gB)
    (constC : ∀ x y, Relation.EqvGen gc x y → gC x = gC y)
    (constB : ∀ x y, Relation.EqvGen gb x y → gB x = gB y)
    (monoC : ∀ x y, ord x y → gC x ≤ gC y) :
    ∃! f : (Q gc → T) × (Q gb → S), FactorPairConditions gc gb ord r gC gB f := by
  let sc := Relation.EqvGen.setoid gc
  let sb := Relation.EqvGen.setoid gb
  let fc := Factor sc gC constC
  let fb := Factor sb gB constB
  have hc : ∀ c, fc (prj gc c) = gC c := fun _ => rfl
  have hb : ∀ b, fb (prj gb b) = gB b := fun _ => rfl
  refine ⟨(fc,fb),?_,?_⟩
  · refine ⟨factor_surjective sc gC constC ontoC, factor_surjective sb gB constB ontoB,
      hc,hb,?_,trajectory_factor_image gc gb r gC gB fc fb hc hb⟩
    intro x y h
    exact factor_monotone sc ord gC constC (· ≤ ·) le_refl
      (fun _ _ _ => le_trans) monoC h
  · intro f hf
    apply Prod.ext
    · exact factor_unique sc gC constC f.1 hf.2.2.1
    · exact factor_unique sb gB constB f.2 hf.2.2.2.1

theorem source_native_factor_pair [PartialOrder T]
    (r : C → D → B → Prop) (bind : C × D × B → C × D × B → Prop)
    (ord : C → C → Prop) (gC : C → T) (gB : B → S)
    (ontoC : Function.Surjective gC) (ontoB : Function.Surjective gB)
    (constC : ∀ x y, Relation.EqvGen (genC r bind) x y → gC x = gC y)
    (constB : ∀ x y, Relation.EqvGen (genB r bind) x y → gB x = gB y)
    (monoC : ∀ x y, ord x y → gC x ≤ gC y) :
    ∃! f : (Q (genC r bind) → T) × (Q (genB r bind) → S),
      FactorPairConditions (genC r bind) (genB r bind) ord r gC gB f :=
  native_factor_pair_exists_unique _ _ ord r gC gB ontoC ontoB constC constB monoC

theorem canonical_projection_surjective (gc : C → C → Prop) : Function.Surjective (prj gc) :=
  Quotient.mk_surjective

theorem canonical_projection_class (gc : C → C → Prop) (x y : C) :
    prj gc x = prj gc y ↔ Relation.EqvGen gc x y := by
  change Quotient.mk (Relation.EqvGen.setoid gc) x = Quotient.mk (Relation.EqvGen.setoid gc) y ↔ _
  constructor
  · exact Quotient.exact
  · intro h
    exact @Quotient.sound C (Relation.EqvGen.setoid gc) x y h

theorem canonical_source_order_preserved (gc : C → C → Prop) (ord : C → C → Prop)
    (x y : C) (h : ord x y) :
    Order (Relation.EqvGen.setoid gc) ord (prj gc x) (prj gc y) :=
  source_monotone _ _ h

end LCTR.CoreDynamicsFactors
