import CoreStageBoundaries
import CoreDynamicMaster
import CoreLawDifferentialBundle

namespace LCTR.CoreThreeLayerSynthesis
set_option autoImplicit false
open LCTR.SelectedInputEvaluation LCTR.LawFamilyTransport LCTR.CoreStageBoundaries
variable {E T A Ω : Type} {X Y : A → Type}

theorem dynamics_equivalence (exactInput : E → Prop) (K : E → Fin 8 → Prop) (ev : E) :
    DynOperative exactInput K ev ↔ exactInput ev ∧ ∀ i, K ev i := Iff.rfl

theorem law_equivalence (exactInput : E → Prop) (K : E → Fin 8 → Prop)
    (law : Selected E (Family T A X Y))
    (domain : ∀ ev, law.domain ev ↔ DynOperative exactInput K ev) (ev : E) :
    LawOperative law ev ↔ DynOperative exactInput K ev ∧
      ∀ i, LCTR.CoreNativeLawFailure.totalCondition law ev i := by
  constructor
  · rintro ⟨h,all⟩
    refine ⟨(domain ev).mp h,?_⟩
    intro i
    exact (LCTR.CoreNativeLawFailure.selected_condition_exact law ev h i).mpr
      ((LCTR.CoreLawConditionGraph.all_conditions_exact _).mpr all i)
  · rintro ⟨hd,all⟩
    have h := (domain ev).mpr hd
    refine ⟨h,(LCTR.CoreLawConditionGraph.all_conditions_exact _).mp ?_⟩
    intro i
    exact (LCTR.CoreNativeLawFailure.selected_condition_exact law ev h i).mp (all i)

theorem differential_equivalence (law : Selected E (Family T A X Y))
    (diff : MatchingDifferential E (Family T A X Y) (LCTR.DifferentialNativeDomains.Input Ω) law)
    (ev : E) :
    DiffOperative law diff ev ↔ LawOperative law ev ∧
      ∀ i, LCTR.CoreDifferentialFailure.selectedCondition diff ev i := by
  constructor
  · rintro ⟨h,hl,hd⟩
    refine ⟨⟨diff.subdomain ev h,hl⟩,?_⟩
    intro i
    exact (LCTR.CoreDifferentialFailure.selected_restricts diff ev h i).mpr
      ((LCTR.CoreDifferentialFailure.all_conditions_complete _).mpr hd i)
  · rintro ⟨⟨_,hl⟩,all⟩
    obtain ⟨h,_⟩ := all 0
    refine ⟨h,hl,(LCTR.CoreDifferentialFailure.all_conditions_complete _).mp ?_⟩
    intro i
    exact (LCTR.CoreDifferentialFailure.selected_restricts diff ev h i).mp (all i)

theorem cumulative_same_input (exactInput : E → Prop) (K : E → Fin 8 → Prop)
    (law : Selected E (Family T A X Y))
    (domain : ∀ ev, law.domain ev ↔ DynOperative exactInput K ev)
    (diff : MatchingDifferential E (Family T A X Y) (LCTR.DifferentialNativeDomains.Input Ω) law)
    (ev : E) (h : DiffOperative law diff ev) :
    LawOperative law ev ∧ DynOperative exactInput K ev ∧ exactInput ev := by
  have hl := differential_requires_same_law law diff ev h
  have hd := (law_equivalence exactInput K law domain ev).mp hl |>.1
  exact ⟨hl,hd,hd.1⟩

open LCTR.CoreObserverTime LCTR.CoreNativeCurves LCTR.CoreDynamicsBundle
open LCTR.CoreLawInputBundle LCTR.CoreLawDifferentialBundle LCTR.CoreNativeLawComponents
variable {C D B U L J V W P N : Type} {Arr : U → Type}
variable (b : Basis C D B U L J V W P N Arr) (a : LawData (A := A) b)

theorem dynamics_every_embedding :
    Nonempty (RealEmbedding b.data b.inc) ∧ ∀ rho : RealEmbedding b.data b.inc,
      (∃! x : Description b.data b.inc rho J V W P N,
        DescriptionSpec b.data b.inc b.single rho b.localDatum b.descent b.code x) ∧
      (∃! x : CoreLawInputBundle.LawInput b.data J V W P N × Description b.data b.inc rho J V W P N,
        WitnessSpec b.data b.inc b.single rho b.localDatum b.descent b.code x) :=
  CoreDynamicMaster.dynamic_master b.data b.inc b.single b.fiber ⟨b.rho⟩ b.localDatum b.descent b.code

noncomputable def transported (rho : RealEmbedding b.data b.inc) :=
  transportFamily (CoreNativeLawGeneration.timeChange (context b) rho) (candidates b a)

abbrev TransportedCore (rho : RealEmbedding b.data b.inc) :=
  Description b.data b.inc rho J V W P N ×
  Family (CoreNativeLawTransport.NewTime b.data b.inc b.rho rho
    (Set.range (realValue b.data b.inc b.rho))) A
      (fun j => Values (Val := ObsValue b) (a.component j).inIndices)
      (fun j => Values (Val := ObsValue b) (a.component j).outIndices)

def TransportedSpec (rho : RealEmbedding b.data b.inc) (x : TransportedCore b a rho) : Prop :=
  DescriptionSpec b.data b.inc b.single rho b.localDatum b.descent b.code x.1 ∧
    x.2=transported b a rho

theorem transported_core_exists_unique (rho : RealEmbedding b.data b.inc) :
    ∃! x : TransportedCore b a rho, TransportedSpec b a rho x := by
  refine ⟨⟨description b.data b.inc b.single b.fiber rho b.localDatum b.descent b.code,
    transported b a rho⟩,?_,?_⟩
  · exact ⟨description_spec b.data b.inc b.single b.fiber rho b.localDatum b.descent b.code,rfl⟩
  · intro x hx
    exact Prod.ext
      (description_unique b.data b.inc b.single b.fiber rho b.localDatum b.descent b.code x.1 hx.1) hx.2

theorem same_law_all_embeddings (conditions : AllConditions (candidates b a)) :
    ∀ rho : RealEmbedding b.data b.inc,
      AllConditions (transported b a rho) ∧
      (∃ t, common (transported b a rho) t) ∧
      ∀ t, common (transported b a rho) t →
        t.val ∈ Set.range (realValue b.data b.inc rho) := by
  intro rho
  have h := CoreNativeLawGeneration.transported_law_generation (context b) a rho conditions
  exact ⟨h.1,h.2.1,fun t ht => (h.2.2 t ht).1⟩

theorem law_cores_all_embeddings (conditions : AllConditions (candidates b a)) :
    ∀ rho : RealEmbedding b.data b.inc,
      ∃! x : TransportedCore b a rho,
        TransportedSpec b a rho x ∧ AllConditions x.2 := by
  intro rho
  obtain ⟨x,hx,unique⟩ := transported_core_exists_unique b a rho
  refine ⟨x,⟨hx,?_⟩,fun y hy => unique y hy.1⟩
  rw [hx.2]
  exact (same_law_all_embeddings b a conditions rho).1

theorem same_reference_differential_objects (conditions : AllConditions (candidates b a)) :
    (∃! x : DifferentialData b a, DifferentialSpec b a x ∧ AllConditions x.candidate) ∧
    (differential b a).embedding=(dynamics b).time.embedding ∧
    (differential b a).representation=(dynamics b).time.representation ∧
    (differential b a).scalar=(dynamics b).trajectory.scalar ∧
    (differential b a).curves=(dynamics b).trajectory.curves.2 :=
  ⟨differential_with_law_conditions b a conditions,differential_same_dynamics b a⟩

theorem differential_conditions_keep_native_domains (d : LCTR.DifferentialNativeDomains.Input Ω)
    (h : LCTR.DifferentialNativeDomains.complete d) :
    LCTR.DifferentialNativeDomains.c1 d ∧ LCTR.DifferentialNativeDomains.c2 d ∧
    LCTR.DifferentialNativeDomains.c3 d ∧ LCTR.DifferentialNativeDomains.c4 d ∧
    LCTR.DifferentialNativeDomains.c5 d := h

end LCTR.CoreThreeLayerSynthesis
