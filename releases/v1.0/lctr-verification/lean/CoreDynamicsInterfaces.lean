import CoreOperationalConfiguration
import CoreSourceMatch

namespace LCTR.CoreDynamicsInterfaces
open LCTR.CoreOperationalConfiguration LCTR.CoreSourceMatch LCTR.Chapter03SourceOrderRecovery
universe u v w z
set_option autoImplicit false

def quotientRoles : Set SourceRole := {.clock,.body}
theorem quotient_role_membership (r : SourceRole) :
    r∈quotientRoles ↔ r=.clock ∨ r=.body := Iff.rfl

abbrev Evaluation {I : Type u} (input : I) (U : Type v) (Z : Type w) :=
  {ev : I × U × Z // ev.1=input}

def makeEvaluation {I : Type u} {U : Type v} {Z : Type w}
    (input : I) (observer : U) (object : Z) : Evaluation input U Z :=
  ⟨(input,observer,object),rfl⟩

theorem complete_eval_fields {I : Type u} {U : Type v} {Z : Type w}
    (input : I) (observer : U) (object : Z) :
    (makeEvaluation input observer object).val=(input,observer,object) := rfl

theorem complete_eval_roundtrip {I : Type u} {U : Type v} {Z : Type w}
    {input : I} (ev : Evaluation input U Z) :
    makeEvaluation input ev.val.2.1 ev.val.2.2=ev := by
  apply Subtype.ext
  exact Prod.ext ev.property.symm rfl

def ExactEvaluation {I : Type u} {U : Type v} {Z : Type w}
    {input : I} (exactInput : I → Prop) (ev : Evaluation input U Z) : Prop := exactInput ev.val.1
theorem exact_eval_iff {I : Type u} {U : Type v} {Z : Type w} {input : I}
    (exactInput : I → Prop) (ev : Evaluation input U Z) :
    ExactEvaluation exactInput ev ↔ exactInput input := by
  simp only [ExactEvaluation,ev.property]

def extended {E : Type u} (D : E → Prop) (P : {e // D e} → Prop) (e : E) : Prop :=
  ∃ witness : {a // D a}, e=witness.val ∧ P witness

theorem extended_bounded_identity {E : Type u} (D : E → Prop)
    (P : {e // D e} → Prop) (e : E) :
    extended D P e ↔ ∃ witness : {a // D a}, e=witness.val ∧ P witness := Iff.rfl

theorem extended_on_domain {E : Type u} (D : E → Prop)
    (P : {e // D e} → Prop) (e : E) (he : D e) :
    extended D P e ↔ P ⟨e,he⟩ := by
  constructor
  · rintro ⟨w,hw,hp⟩
    have eq : w=⟨e,he⟩ := Subtype.ext hw.symm
    exact eq ▸ hp
  · intro hp
    exact ⟨⟨e,he⟩,rfl,hp⟩

theorem extended_outside_domain {E : Type u} (D : E → Prop)
    (P : {e // D e} → Prop) (e : E) (he : ¬D e) : ¬extended D P e := by
  rintro ⟨w,rfl,_⟩
  exact he w.property

abbrev ArrivalFamily (R : Type u) (S : R → Type v) (V : R → Type w) :=
  ∀ r, PartialArrival (S r) (V r)
abbrev ArrivalTuple {R : Type u} {S : R → Type v} {V : R → Type w}
    (arr : ArrivalFamily R S V) :=
  ∀ r, ImageAt (fun (_ : Unit) => arr r) ()

structure ReceptionData (R : Type u) (S : R → Type v) (V : R → Type w) where
  arrival : ArrivalFamily R S V
  localRelation : Set (ArrivalTuple arrival)
  sourceRelation : Set (∀ r, S r)

abbrev ReceptionPackage (R : Type u) (S : R → Type v) (V : R → Type w) :=
  (arr : ArrivalFamily R S V) × (Set (ArrivalTuple arr) × Set (∀ r, S r))

def packReception {R : Type u} {S : R → Type v} {V : R → Type w}
    (p : ReceptionPackage R S V) : ReceptionData R S V := ⟨p.1,p.2.1,p.2.2⟩
def unpackReception {R : Type u} {S : R → Type v} {V : R → Type w}
    (x : ReceptionData R S V) : ReceptionPackage R S V := ⟨x.arrival,x.localRelation,x.sourceRelation⟩

theorem reception_pack_roundtrip {R : Type u} {S : R → Type v} {V : R → Type w}
    (x : ReceptionData R S V) : packReception (unpackReception x)=x := by cases x; rfl
theorem reception_unpack_roundtrip {R : Type u} {S : R → Type v} {V : R → Type w}
    (p : ReceptionPackage R S V) : unpackReception (packReception p)=p := by cases p; rfl

theorem arrival_image_exact {R : Type u} {S : R → Type v} {V : R → Type w}
    (arr : ArrivalFamily R S V) (r : R) (a : V r) :
    a∈ImageAt (fun (_ : Unit) => arr r) () ↔
      ∃ t : S r, ∃ ht : t∈(arr r).dom, (arr r).val t ht=a := by
  constructor
  · rintro ⟨t,ht⟩
    exact ⟨t.val,t.property,ht⟩
  · rintro ⟨t,ht,eq⟩
    exact ⟨⟨t,ht⟩,eq⟩

theorem local_relation_typed {R : Type u} {S : R → Type v} {V : R → Type w}
    (x : ReceptionData R S V) (a : ArrivalTuple x.arrival) (_ha : a∈x.localRelation) :
    ∀ r, ∃ t : S r, ∃ ht : t∈(x.arrival r).dom, (x.arrival r).val t ht=(a r).val :=
  fun r => (arrival_image_exact x.arrival r (a r).val).mp (a r).property

theorem source_relation_typed {R : Type u} {S : R → Type v} {V : R → Type w}
    (x : ReceptionData R S V) (s : ∀ r, S r) (_hs : s∈x.sourceRelation) :
    ∀ r, s r∈(Set.univ : Set (S r)) := fun _ => Set.mem_univ _

end LCTR.CoreDynamicsInterfaces
