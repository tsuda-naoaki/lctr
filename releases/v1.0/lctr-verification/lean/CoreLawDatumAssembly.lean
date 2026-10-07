import CoreLawDatumSemantics
import CoreNativeLawComponents

namespace LCTR.CoreLawDatumAssembly
set_option autoImplicit false
open Set LCTR.CoreLawDatumSemantics LCTR.LawFamilyTransport LCTR.LawTimeTransport
variable {E J U T A : Type} {X Y : A → Type}

def assemble (e : E ⊕ J) (f : Family T A X Y) : Datum E J := ⟨e, pack f⟩

def coupling (singleLocation : E → U) (jointLocation : J → U) (d : Datum E J) : U :=
  Sum.elim singleLocation jointLocation d.evalSpec

theorem outer_projections (e : E ⊕ J) (f : Family T A X Y) :
    (assemble e f).evalSpec = e ∧ (assemble e f).candidate = pack f := ⟨rfl,rfl⟩

theorem coupling_single (s : E → U) (j : J → U) (e : E) (f : Family T A X Y) :
    coupling s j (assemble (Sum.inl e) f) = s e := rfl

theorem coupling_joint (s : E → U) (j : J → U) (e : J) (f : Family T A X Y) :
    coupling s j (assemble (Sum.inr e) f) = j e := rfl

theorem component_projection (e : E ⊕ J) (f : Family T A X Y) (a : A) :
    (assemble e f).candidate.family.component a = f.component a := rfl

theorem family_projections (e : E ⊕ J) (f : Family T A X Y) :
    (assemble e f).candidate.family.admissibleCommon = f.admissibleCommon ∧
    (assemble e f).candidate.family.faithful = f.faithful := ⟨rfl,rfl⟩

theorem individual_input_typed (d : Datum E J) (a : d.candidate.Index)
    (t : {t // (d.candidate.family.component a).evalTime t}) :
    (t.val, (d.candidate.family.component a).input t) ∈
      (Set.univ : Set d.candidate.Time) ×ˢ (Set.univ : Set (d.candidate.InputValue a)) :=
  ⟨Set.mem_univ _, Set.mem_univ _⟩

theorem evaluation_tuple_domain_typed (d : Datum E J) (h : K1 d.candidate.family)
    (a : d.candidate.Index) (t : {t // (d.candidate.family.component a).evalTime t}) :
    evalTuple (d.candidate.family.component a) t ∈
      {p | (d.candidate.family.component a).evalDomain p.1 p.2} ×ˢ
        (Set.univ : Set (d.candidate.OutputValue a)) :=
  ⟨(h a).2 t, Set.mem_univ _⟩

theorem common_valid_contract (d : Datum E J) (h : K5 d.candidate.family) :
    (∃ t, common d.candidate.family t) ∧
    d.candidate.family.admissibleCommon (common d.candidate.family) ∧
    (∀ t, common d.candidate.family t → ∀ a,
      ∃ ht : (d.candidate.family.component a).evalTime t,
        tupleRelation (d.candidate.family.component a)
          (evalTuple (d.candidate.family.component a) ⟨t,ht⟩)) :=
  ⟨h.2.1,h.2.2,fun _ ht a => ht a⟩

theorem evaluation_tuple_projections (d : Datum E J) (a : d.candidate.Index)
    (t : {t // (d.candidate.family.component a).evalTime t}) :
    (evalTuple (d.candidate.family.component a) t).1.1 = t.val ∧
    (evalTuple (d.candidate.family.component a) t).1.2 =
      (d.candidate.family.component a).input t ∧
    (evalTuple (d.candidate.family.component a) t).2 =
      (d.candidate.family.component a).output t := ⟨rfl,rfl,rfl⟩

theorem native_component_projection {C D B I : Type} {Val : I → Type}
    (c : LCTR.CoreNativeLawComponents.Context C D B I Val) {N : Type}
    (hn : Nonempty N) (inputs : N → LCTR.CoreNativeLawComponents.ComponentInput c)
    (allowed : (LCTR.CoreNativeLawComponents.NativeTime c → Prop) → Prop)
    (faithful : ((a : N) → Reindex
      (Tuple (LCTR.CoreNativeLawComponents.NativeTime c)
        (LCTR.CoreNativeLawComponents.Values (Val:=Val) (inputs a).inIndices)
        (LCTR.CoreNativeLawComponents.Values (Val:=Val) (inputs a).outIndices))
      (Tuple (LCTR.CoreNativeLawComponents.NativeTime c)
        (LCTR.CoreNativeLawComponents.Values (Val:=Val) (inputs a).inIndices)
        (LCTR.CoreNativeLawComponents.Values (Val:=Val) (inputs a).outIndices))) → Prop)
    (e : E ⊕ J) (a : N) :
    (assemble e (LCTR.CoreNativeLawComponents.nativeFamily c hn inputs allowed faithful)).candidate.family.component a =
      LCTR.CoreNativeLawComponents.generated c (inputs a) := rfl

end LCTR.CoreLawDatumAssembly
