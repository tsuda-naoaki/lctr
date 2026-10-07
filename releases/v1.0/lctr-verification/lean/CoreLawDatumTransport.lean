import CoreLawDatumAssembly

namespace LCTR.CoreLawDatumTransport
set_option autoImplicit false
open Set LCTR.LawTimeTransport LCTR.LawFamilyTransport
open LCTR.CoreLawDatumSemantics LCTR.CoreLawConditionGraph
variable {E J U Q V : Type}

def moved (d : Datum E J) (e : Reindex d.candidate.Time U) : Datum E J :=
  ⟨d.evalSpec, pack (transportFamily e d.candidate.family)⟩

theorem specification_preserved (d : Datum E J) (e : Reindex d.candidate.Time U) :
    (moved d e).evalSpec = d.evalSpec := rfl

theorem condition_preserved (d : Datum E J) (e : Reindex d.candidate.Time U) (i : Node) :
    condition (moved d e).candidate.family i ↔ condition d.candidate.family i := by
  change condition (transportFamily e d.candidate.family) i ↔ _
  fin_cases i <;> simp only [condition, condition1_preserved,
    condition2_preserved, condition3_preserved, condition4_preserved, condition5_preserved]

theorem common_image (d : Datum E J) (e : Reindex d.candidate.Time U) :
    common (moved d e).candidate.family = image e (common d.candidate.family) :=
  common_is_image e d.candidate.family

theorem admissible_image (d : Datum E J) (e : Reindex d.candidate.Time U) (P : U → Prop) :
    (moved d e).candidate.family.admissibleCommon P ↔
      ∃ R, d.candidate.family.admissibleCommon R ∧ P = image e R :=
  admissible_family_is_image e d.candidate.family P

theorem evaluation_tuple_transport (d : Datum E J) (e : Reindex d.candidate.Time U)
    (a : d.candidate.Index) (t : {t // (d.candidate.family.component a).evalTime t}) :
    evalTuple ((moved d e).candidate.family.component a)
      (liftTime e (d.candidate.family.component a) t) =
    (tupleReindex e).forward (evalTuple (d.candidate.family.component a) t) :=
  LCTR.LawFamilyTransport.evaluation_tuple_transport e (d.candidate.family.component a) t

theorem law_operative_preserved (d : Datum E J) (e : Reindex d.candidate.Time U)
    (dyn : E → Prop) (joint : J → Prop) :
    lawOperative dyn joint (moved d e) ↔ lawOperative dyn joint d := by
  change (_ ∧ AllConditions (transportFamily e d.candidate.family)) ↔ _
  exact and_congr Iff.rfl (five_conditions_preserved e d.candidate.family)

theorem generated_common_representability (d : Datum E J)
    (dyn : E → Prop) (joint : J → Prop)
    (rho : Q → V) (domain : Set Q) (value : d.candidate.Time → V)
    (compatible : ∀ t, value t ∈ rho '' domain)
    (operative : lawOperative dyn joint d) :
    (∃ t, common d.candidate.family t) ∧
    ∀ t, common d.candidate.family t → value t ∈ rho '' domain ∧
      ∀ a, ∃ ht : (d.candidate.family.component a).evalTime t,
        tupleRelation (d.candidate.family.component a)
          (evalTuple (d.candidate.family.component a) ⟨t,ht⟩) := by
  have hc := LCTR.CoreLawDatumAssembly.common_valid_contract d operative.2.2.2.2.2
  exact ⟨hc.1,fun t h => ⟨compatible t,hc.2.2 t h⟩⟩

end LCTR.CoreLawDatumTransport
