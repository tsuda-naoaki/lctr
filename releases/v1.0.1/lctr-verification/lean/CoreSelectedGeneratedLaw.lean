import CoreLawDatumAssembly
import Mathlib.Data.Real.Basic

namespace LCTR.CoreSelectedGeneratedLaw
set_option autoImplicit false
open Set LCTR.LawFamilyTransport LCTR.LawTimeTransport
variable {E J : Type}

structure TimeBases (E J : Type) where
  Point : E ⊕ J → Type
  domain : (e : E ⊕ J) → Set (Point e)
  admitted : (e : E ⊕ J) → Set (Point e → ℝ)

structure NumericDatum (E J : Type) where
  evalSpec : E ⊕ J
  timeDomain : Set ℝ
  Index : Type
  InputValue : Index → Type
  OutputValue : Index → Type
  family : Family {t // t ∈ timeDomain} Index InputValue OutputValue

def NumericDatum.toDatum (d : NumericDatum E J) : LCTR.CoreLawDatumSemantics.Datum E J :=
  ⟨d.evalSpec, LCTR.CoreLawDatumSemantics.pack d.family⟩

def generated (b : TimeBases E J) (dyn : E → Prop) (joint : J → Prop)
    (d : NumericDatum E J) (rho : b.Point d.evalSpec → ℝ) : Prop :=
  d.evalSpec ∈ LCTR.CoreLawReadinessBridge.readySet dyn joint ∧
  rho ∈ b.admitted d.evalSpec ∧ d.timeDomain ⊆ rho '' b.domain d.evalSpec

def timeAdmissible (b : TimeBases E J) (dyn : E → Prop) (joint : J → Prop)
    (d : NumericDatum E J) (rho : b.Point d.evalSpec → ℝ) : Prop :=
  generated b dyn joint d rho ∧ AllConditions d.family

structure GeneratedSelection (b : TimeBases E J) (dyn : E → Prop) (joint : J → Prop) where
  domain : E → Prop
  datum : {e // domain e} → NumericDatum E J
  same_spec : ∀ x, (datum x).evalSpec = Sum.inl x.val
  representation : (x : {e // domain e}) → b.Point (datum x).evalSpec → ℝ
  compatible : ∀ x, generated b dyn joint (datum x) (representation x)

variable {b : TimeBases E J} {dyn : E → Prop} {joint : J → Prop}

theorem generated_exact (d : NumericDatum E J) (rho : b.Point d.evalSpec → ℝ) :
    generated b dyn joint d rho ↔
      d.evalSpec ∈ LCTR.CoreLawReadinessBridge.readySet dyn joint ∧
      rho ∈ b.admitted d.evalSpec ∧ d.timeDomain ⊆ rho '' b.domain d.evalSpec := Iff.rfl

theorem selected_generation_components (s : GeneratedSelection b dyn joint)
    (x : {e // s.domain e}) :
    (s.datum x).evalSpec ∈ LCTR.CoreLawReadinessBridge.readySet dyn joint ∧
    s.representation x ∈ b.admitted (s.datum x).evalSpec ∧
    (s.datum x).timeDomain ⊆ s.representation x '' b.domain (s.datum x).evalSpec :=
  s.compatible x

theorem selected_domain_ready (s : GeneratedSelection b dyn joint)
    (e : E) (h : s.domain e) : dyn e := by
  have ready := (s.compatible ⟨e,h⟩).1
  rw [s.same_spec] at ready
  exact (LCTR.CoreLawReadinessBridge.single_ready_exact dyn joint e).mp ready

def forget (s : GeneratedSelection b dyn joint) : LCTR.CoreLawDatumSemantics.Selection E J dyn where
  domain := s.domain
  datum x := (s.datum x).toDatum
  domain_ready := selected_domain_ready s
  same_spec := s.same_spec

theorem forget_retains_specification (s : GeneratedSelection b dyn joint)
    (x : {e // s.domain e}) :
    (forget s).datum x = (s.datum x).toDatum ∧
    ((forget s).datum x).evalSpec = Sum.inl x.val := ⟨rfl,s.same_spec x⟩

theorem selected_condition_exact (s : GeneratedSelection b dyn joint)
    (e : E) (h : s.domain e) (i : LCTR.CoreLawConditionGraph.Node) :
    LCTR.CoreLawDatumSemantics.totalCondition (forget s) e i ↔
      LCTR.CoreLawConditionGraph.condition (s.datum ⟨e,h⟩).family i :=
  LCTR.CoreLawDatumSemantics.selected_condition_exact (forget s) e h i

theorem selected_failure_operative (s : GeneratedSelection b dyn joint)
    (e : E) (h : s.domain e) :
    LCTR.CoreLawDatumSemantics.failure (forget s) e ↔
      dyn e ∧ ¬ LCTR.CoreLawDatumSemantics.lawOperative dyn joint (s.datum ⟨e,h⟩).toDatum :=
  LCTR.CoreLawDatumSemantics.failure_vs_operative (forget s) joint e h

theorem selected_time_admissibility (s : GeneratedSelection b dyn joint)
    (x : {e // s.domain e}) :
    timeAdmissible b dyn joint (s.datum x) (s.representation x) ↔
      LCTR.CoreLawDatumSemantics.lawOperative dyn joint (s.datum x).toDatum := by
  change (generated b dyn joint (s.datum x) (s.representation x) ∧ AllConditions (s.datum x).family) ↔
    ((s.datum x).evalSpec ∈ LCTR.CoreLawReadinessBridge.readySet dyn joint ∧ AllConditions (s.datum x).family)
  simp only [s.compatible x, true_and, (s.compatible x).1]

theorem outside_selection_not_failure (s : GeneratedSelection b dyn joint)
    (e : E) (h : ¬ s.domain e) :
    (∀ i, ¬ LCTR.CoreLawDatumSemantics.totalCondition (forget s) e i) ∧
      ¬ LCTR.CoreLawDatumSemantics.failure (forget s) e :=
  LCTR.CoreLawDatumSemantics.outside_selection_not_failure (forget s) e h

theorem generated_common_representability (d : NumericDatum E J)
    (rho : b.Point d.evalSpec → ℝ) (g : generated b dyn joint d rho)
    (all : AllConditions d.family) :
    (∃ t, common d.family t) ∧
    ∀ t, common d.family t → t.val ∈ rho '' b.domain d.evalSpec ∧
      ∀ a, ∃ ht : (d.family.component a).evalTime t,
        tupleRelation (d.family.component a) (evalTuple (d.family.component a) ⟨t,ht⟩) := by
  have c := LCTR.CoreLawDatumAssembly.common_valid_contract d.toDatum all.2.2.2.2
  exact ⟨c.1,fun t h => ⟨g.2.2 t.property,c.2.2 t h⟩⟩

theorem proper_generated_subdomain_possible :
    ({0} : Set ℝ) ⊂ (fun x : ℝ => x) '' ({0,1} : Set ℝ) := by
  simp only [Set.image_id']
  exact Set.ssubset_iff_subset_ne.mpr ⟨by intro x hx; simp_all,
    by intro h; have bad : (1 : ℝ) ∈ ({0} : Set ℝ) := h.symm ▸ (by simp); simp at bad⟩

end LCTR.CoreSelectedGeneratedLaw
