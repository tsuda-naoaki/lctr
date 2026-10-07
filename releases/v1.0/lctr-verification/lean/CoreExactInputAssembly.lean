import CoreExactCompletion

namespace LCTR.CoreExactInputAssembly
set_option autoImplicit false
open Set LCTR.CoreSourceMatch LCTR.CorePreorderQuotient
open LCTR.Chapter03SourceOrderRecovery
open LCTR.CoreExactStructure LCTR.CoreExactCompletion
universe u v w
variable {U : Type u} {S : Fin 2 → Type v} {V : Fin 2 → U → Type w}

structure RoleOrder (x : LCTR.CoreComparisonStage.Input U S V) (r : Fin 2) where
  relation : S r → S r → Prop
  refl : ReflRel relation
  trans : TransRel relation
  anti : AntiRel relation
  descent : OrdDesc (LCTR.CoreTypedWords.orbitSetoid (LCTR.CoreSourceLoops.system (x.data r)))
    (Pullback (recover (x.data r).arrival (x.data r).unique) relation)

def assembled (x : LCTR.CoreComparisonStage.Input U S V) (r : Fin 2) (o : RoleOrder x r) :
    LCTR.CoreExactStructure.Input U (S r) (V r) where
  arrival := (x.data r).arrival
  unique := (x.data r).unique
  transport := (x.data r).transport
  admissible := (x.data r).admissible
  transportInjective := (x.data r).transportInjective
  sourceOrder := o.relation
  refl := o.refl
  trans := o.trans
  anti := o.anti
  descent := o.descent

variable (x : LCTR.CoreComparisonStage.Input U S V)
variable (orders : ∀ r, RoleOrder x r)

theorem same_arrivals (r : Fin 2) :
    (assembled x r (orders r)).arrival = (x.data r).arrival := rfl

theorem same_transport (r : Fin 2) :
    (assembled x r (orders r)).transport = (x.data r).transport := rfl

theorem same_quotient (r : Fin 2) :
    Canonical (assembled x r (orders r)) = LCTR.CoreComparisonStage.RoleQuotient x r := rfl

theorem same_projection (r : Fin 2) (i : U) (a : ImageAt (x.data r).arrival i) :
    canonicalProjection (assembled x r (orders r)) ⟨i,a⟩ =
      LCTR.CoreComparisonStage.roleProjection x r i a := rfl

theorem source_order_recovered (r : Fin 2)
    (a b : Tagged (x.data r).arrival) :
    canonicalOrder (assembled x r (orders r))
      (canonicalProjection (assembled x r (orders r)) a)
      (canonicalProjection (assembled x r (orders r)) b) ↔
      (orders r).relation
        (recover (x.data r).arrival (x.data r).unique a)
        (recover (x.data r).arrival (x.data r).unique b) := Iff.rfl

abbrev OrderedFamily (g : ∀ r, GlobalInc (assembled x r (orders r))) :=
  ∀ r, OrderedOutput (assembled x r (orders r)) (g r)

noncomputable def generatedFamily (g : ∀ r, GlobalInc (assembled x r (orders r))) :
    OrderedFamily x orders g := fun r => generatedOrdered (assembled x r (orders r)) (g r)

def FamilyValid (g : ∀ r, GlobalInc (assembled x r (orders r)))
    (q : OrderedFamily x orders g) : Prop :=
  ∀ r, OrderedValid (assembled x r (orders r)) (g r) (q r)

theorem ordered_family_unique (g : ∀ r, GlobalInc (assembled x r (orders r))) :
    ∃! q : OrderedFamily x orders g, FamilyValid x orders g q := by
  refine ⟨generatedFamily x orders g,fun r => generated_ordered_valid _ _,?_⟩
  intro q hq
  funext r
  exact ordered_output_unique _ _ (q r) (hq r)

theorem comparison_and_order_same_input
    (operative : LCTR.CoreComparisonStage.ResidualOperative x)
    (g : ∀ r, GlobalInc (assembled x r (orders r))) :
    ∃! p : LCTR.CoreComparisonStage.Output x × OrderedFamily x orders g,
      LCTR.CoreComparisonStage.Valid x p.1 ∧ FamilyValid x orders g p.2 := by
  obtain ⟨c,hc,uc⟩ := LCTR.CoreComparisonStage.unique_generated_output x operative
  obtain ⟨q,hq,uq⟩ := ordered_family_unique x orders g
  exact ⟨⟨c,q⟩,⟨hc,hq⟩,fun p hp => Prod.ext (uc p.1 hp.1) (uq p.2 hp.2)⟩

theorem local_global_same_source (g : ∀ r, GlobalInc (assembled x r (orders r)))
    (r : Fin 2) (i : U) (a : ImageAt (x.data r).arrival i) :
    (generatedFamily x orders g r).localGlobalMap i
      ((generatedFamily x orders g r).localChart i a) =
      (generatedFamily x orders g r).global
        (LCTR.CoreComparisonStage.roleProjection x r i a) := rfl

theorem comparison_injection_retained
    (operative : LCTR.CoreComparisonStage.ResidualOperative x) (r : Fin 2) (i : U) :
    Function.Injective (fun a : ImageAt (x.data r).arrival i =>
      canonicalProjection (assembled x r (orders r)) ⟨i,a⟩) :=
  LCTR.CoreComparisonStage.generated_local_injective x operative r i

theorem generated_order_no_extra_coordinate_input
    (g : ∀ r, GlobalInc (assembled x r (orders r)))
    {Parameter : Type} (candidate : Parameter → OrderedFamily x orders g)
    (valid : ∀ p, FamilyValid x orders g (candidate p)) (p q : Parameter) :
    candidate p = candidate q := by
  obtain ⟨z,_,unique⟩ := ordered_family_unique x orders g
  exact (unique _ (valid p)).trans (unique _ (valid q)).symm

end LCTR.CoreExactInputAssembly
