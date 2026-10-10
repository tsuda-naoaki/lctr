import CoreNativeTimeConditions
import LCTR.DifferentialNativeDomains

namespace LCTR.CoreNativeDifferentialFamily
set_option autoImplicit false
open Set LCTR.CoreLocalCharts LCTR.CoreNativeLawComponents LCTR.CoreLawComponentCharts
open LCTR.CoreNativeLawGeneration LCTR.LawTimeTransport LCTR.CoreTransportedLawCharts
open LCTR.CoreNativeJointJets LCTR.CoreNativeChartOverlaps
open LCTR.CoreNativeAtlasConditions LCTR.CoreNativeTimeConditions
open LCTR.CoreObserverTime
variable {C D B I A : Type} {Val : I → Type}
variable (c : Context C D B I Val)
abbrev Rep := RealEmbedding c.data c.inc

noncomputable def componentAt (l : ComponentInput c) (rho : Rep c) :=
  transport (timeChange c rho) (generated c l)
abbrev EvalAt (l : ComponentInput c) (rho : Rep c) :=
  {t // (componentAt c l rho).evalTime t}

noncomputable def toRepresentation (l : ComponentInput c) (rho : Rep c) :=
  evaluationEquiv (timeChange c rho) (generated c l)
noncomputable def between (l : ComponentInput c) (rho sigma : Rep c) :
    EvalAt c l rho ≃ EvalAt c l sigma :=
  (toRepresentation c l rho).symm.trans (toRepresentation c l sigma)

noncomputable def valuesAt (l : ComponentInput c) (rho : Rep c)
    (s : Fin 2) (t : EvalAt c l rho) : SideValue c l s :=
  nativeValues c l s ((toRepresentation c l rho).symm t)

theorem same_transported_input_value (l : ComponentInput c) (rho : Rep c) (t : EvalAt c l rho) :
    valuesAt c l rho 0 t = (componentAt c l rho).input t := rfl
theorem same_transported_output_value (l : ComponentInput c) (rho : Rep c) (t : EvalAt c l rho) :
    valuesAt c l rho 1 t = (componentAt c l rho).output t := rfl

theorem between_preserves_native_values (l : ComponentInput c) (rho sigma : Rep c)
    (s : Fin 2) (t : EvalAt c l rho) :
    valuesAt c l sigma s (between c l rho sigma t) = valuesAt c l rho s t := by
  exact congrArg (nativeValues c l s)
    ((toRepresentation c l sigma).symm_apply_apply ((toRepresentation c l rho).symm t))

variable (law : LawInput c A)
structure RawFamily where
  selected : Set A
  selectedNonempty : selected.Nonempty
  order : selected → ℕ
  orderPositive : ∀ j, 0 < order j
  timeIndex : Rep c → selected → Type
  valIndex : selected → Fin 2 → Type
  dim : selected → Fin 2 → ℕ
  time : ∀ rho j, timeIndex rho j → Chart (EvalAt c (law.component j.val) rho) ℝ
  valChart : ∀ j s, valIndex j s → Chart (SideValue c (law.component j.val) s) (Fin (dim j s) → ℝ)
  timeIndexNonempty : ∀ rho j, Nonempty (timeIndex rho j)
  valueIndexNonempty : ∀ j s, Nonempty (valIndex j s)
  timeOpen : ∀ rho j alpha, IsOpen (time rho j alpha).target
  valueOpen : ∀ j s beta, IsOpen (valChart j s beta).target
  cover : ∀ rho j (t : EvalAt c (law.component j.val) rho),
    ∃ (alpha : timeIndex rho j) (beta : (s : Fin 2) → valIndex j s),
      t ∈ (time rho j alpha).source ∧
      ∀ s, valuesAt c (law.component j.val) rho s t ∈ (valChart j s (beta s)).source

noncomputable def atlas (f : RawFamily c law) (rho : Rep c) (j : f.selected) :
    Atlas (EvalAt c (law.component j.val) rho) (f.timeIndex rho j)
      (SideValue c (law.component j.val)) (f.valIndex j) where
  dim := f.dim j
  value := valuesAt c (law.component j.val) rho
  time := f.time rho j
  valChart := f.valChart j
  timeIndexNonempty := f.timeIndexNonempty rho j
  valueIndexNonempty := f.valueIndexNonempty j
  timeOpen := f.timeOpen rho j
  valueOpen := f.valueOpen j
  cover t := by
    obtain ⟨alpha,beta,ht,hv⟩ := f.cover rho j t
    exact ⟨(alpha,beta),ht,hv⟩

structure Family where
  raw : RawFamily c law
  relation : ∀ rho (j : raw.selected), Relations (atlas c law raw rho j) (raw.order j)

variable (f : Family c law)
def AtlasCondition (rho : Rep c) : Prop :=
  ∀ j : f.raw.selected, Diff1 (atlas c law f.raw rho j) (f.raw.order j)
def JetCondition (rho : Rep c) : Prop :=
  ∀ (j : f.raw.selected) i,
    LCTR.CoreNativeDifferentialPredicates.Diff2 (atlas c law f.raw rho j) i (f.raw.order j)
def MemberCondition (rho : Rep c) (h : JetCondition c law f rho) : Prop :=
  ∀ (j : f.raw.selected) i theta,
    LCTR.CoreNativeDifferentialPredicates.canonicalPair
      (atlas c law f.raw rho j) i (f.raw.order j) (h j i) theta ∈ f.relation rho j i
def ValueCondition (rho : Rep c) : Prop :=
  ∀ j : f.raw.selected,
    Diff4 (atlas c law f.raw rho j) (f.raw.order j) (f.relation rho j)

def TimeCondition (rho sigma : Rep c) : Prop :=
  ∀ (j : f.raw.selected) (alpha : f.raw.timeIndex rho j) (delta : f.raw.timeIndex sigma j)
    (beta : (s : Fin 2) → f.raw.valIndex j s),
    ∃ b : RepChange (f.raw.order j) (productChart (atlas c law f.raw rho j) beta).target
      (between c (law.component j.val) rho sigma)
      (f.raw.time rho j alpha) (f.raw.time sigma j delta),
      RepCov (f.raw.order j) (productChart (atlas c law f.raw rho j) beta).target
        (between c (law.component j.val) rho sigma)
        (f.raw.time rho j alpha) (f.raw.time sigma j delta) b
        (f.relation rho j (alpha,beta)) (f.relation sigma j (delta,beta))

def input : LCTR.DifferentialNativeDomains.Input (Rep c) where
  atlas := AtlasCondition c law f
  jet := JetCondition c law f
  member := MemberCondition c law f
  value := fun rho _ => ValueCondition c law f rho
  time := fun rho sigma _ _ => TimeCondition c law f rho sigma

theorem native_first_condition : LCTR.DifferentialNativeDomains.c1 (input c law f) ↔
    ∀ rho (j : f.raw.selected), Diff1 (atlas c law f.raw rho j) (f.raw.order j) := Iff.rfl

theorem native_second_condition : LCTR.DifferentialNativeDomains.c2 (input c law f) ↔
    ∀ rho (j : f.raw.selected) i,
      LCTR.CoreNativeDifferentialPredicates.Diff2 (atlas c law f.raw rho j) i (f.raw.order j) := Iff.rfl

theorem native_third_condition : LCTR.DifferentialNativeDomains.c3 (input c law f) ↔
    ∀ rho (j : f.raw.selected) i,
      LCTR.CoreNativeDifferentialPredicates.Diff3
        (atlas c law f.raw rho j) i (f.raw.order j) (f.relation rho j i) := by
  constructor
  · intro hc rho j i
    obtain ⟨h,mem⟩ := hc rho
    exact ⟨h j i,mem j i⟩
  · intro hc rho
    have h : JetCondition c law f rho := fun j i => (hc rho j i).choose
    refine ⟨h,?_⟩
    intro j i
    exact (LCTR.CoreNativeDifferentialPredicates.diff3_restricts
      (atlas c law f.raw rho j) i (f.raw.order j) (f.relation rho j i) (h j i)).mp (hc rho j i)

theorem native_fourth_condition : LCTR.DifferentialNativeDomains.c4 (input c law f) ↔
    ∀ rho (j : f.raw.selected),
      Diff4 (atlas c law f.raw rho j) (f.raw.order j) (f.relation rho j) := by
  constructor
  · intro hc rho
    exact (hc rho).choose_spec
  · intro hc rho
    exact ⟨fun j => diff4_requires_diff1 _ _ _ (hc rho j),hc rho⟩

theorem native_fifth_condition : LCTR.DifferentialNativeDomains.c5 (input c law f) ↔
    ∀ rho sigma, AtlasCondition c law f rho ∧ AtlasCondition c law f sigma ∧
      TimeCondition c law f rho sigma := by
  constructor
  · intro hc rho sigma
    obtain ⟨h,g,ht⟩ := hc rho sigma
    exact ⟨h,g,ht⟩
  · intro hc rho sigma
    exact ⟨(hc rho sigma).1,(hc rho sigma).2.1,(hc rho sigma).2.2⟩

theorem same_law_data_all_representations (rho : Rep c) (j : f.raw.selected)
    (t : EvalAt c (law.component j.val) rho) :
    (atlas c law f.raw rho j).value 0 t = (componentAt c (law.component j.val) rho).input t ∧
    (atlas c law f.raw rho j).value 1 t = (componentAt c (law.component j.val) rho).output t := ⟨rfl,rfl⟩

theorem shared_value_charts (rho sigma : Rep c) (j : f.raw.selected) :
    (atlas c law f.raw rho j).dim = (atlas c law f.raw sigma j).dim ∧
    (atlas c law f.raw rho j).valChart = (atlas c law f.raw sigma j).valChart := ⟨rfl,rfl⟩

theorem native_failure_cover :
    ¬ LCTR.DifferentialNativeDomains.complete (input c law f) ↔
      LCTR.DifferentialNativeDomains.f1 (input c law f) ∨
      LCTR.DifferentialNativeDomains.f2 (input c law f) ∨
      LCTR.DifferentialNativeDomains.f3 (input c law f) ∨
      LCTR.DifferentialNativeDomains.f4 (input c law f) ∨
      LCTR.DifferentialNativeDomains.f5 (input c law f) :=
  LCTR.DifferentialNativeDomains.five_failure_cover (input c law f)

end LCTR.CoreNativeDifferentialFamily
