import CoreNativeDifferentialSynthesis

namespace LCTR.CoreNativeSelectedDifferential
set_option autoImplicit false
open LCTR.CoreLawDifferentialBundle LCTR.CoreNativeDifferentialSynthesis
open LCTR.SelectedInputEvaluation LCTR.CoreDifferentialFailure
open LCTR.CoreNativeDifferentialFamily LCTR.CoreLocalCharts LCTR.CoreNativeJointJets
variable {C D B U L J V W P N A E : Type} {Arr : U → Type}
variable (b : Basis C D B U L J V W P N Arr)

structure Selection where
  law : Selected E (LawData (A := A) b)
  domain : E → Prop
  subdomain : ∀ ev, domain ev → law.domain ev
  family : (ev : {e // domain e}) →
    CoreNativeDifferentialFamily.Family (context b) (law.datum ⟨ev.val,subdomain ev.val ev.property⟩)

variable (s : Selection (A:=A) (E:=E) b)
noncomputable def matching : MatchingDifferential E (LawData (A:=A) b)
    (LCTR.DifferentialNativeDomains.Input (Rep (context b))) s.law where
  domain := s.domain
  subdomain := s.subdomain
  structureAt ev := nativeInput b (s.law.datum ⟨ev.val,s.subdomain ev.val ev.property⟩) (s.family ev)

def lawOperative (a : LawData (A:=A) b) : Prop := LCTR.LawFamilyTransport.AllConditions (candidates b a)
def selectedOperative (ev : E) : Prop := ∃ he : s.domain ev,
  Operative b (s.law.datum ⟨ev,s.subdomain ev he⟩) (s.family ⟨ev,he⟩)

theorem selected_law_owned (ev : E) (he : s.domain ev) :
    (differentialInput (matching b s) ev he).1 = s.law.datum ⟨ev,s.subdomain ev he⟩ := rfl
theorem selected_differential_owned (ev : E) (he : s.domain ev) :
    (differentialInput (matching b s) ev he).2 =
      nativeInput b (s.law.datum ⟨ev,s.subdomain ev he⟩) (s.family ⟨ev,he⟩) := rfl

theorem operative_on_domain (ev : E) (he : s.domain ev) :
    selectedOperative b s ev ↔
      Operative b (s.law.datum ⟨ev,s.subdomain ev he⟩) (s.family ⟨ev,he⟩) :=
  ⟨fun ⟨_,h⟩ => h,fun h => ⟨he,h⟩⟩

theorem operative_requires_same_law (ev : E) (h : selectedOperative b s ev) :
    evaluate s.law (lawOperative b) ev := by
  obtain ⟨he,hl,_⟩ := h
  exact ⟨s.subdomain ev he,hl⟩

theorem outside_selection_unformed (ev : E) (outside : ¬ s.domain ev) :
    ¬ selectedOperative b s ev ∧
    ¬ failure (matching b s) (lawOperative b) ev ∧
    ∀ i, ¬ minimalFailure (matching b s) (lawOperative b) ev i :=
  ⟨fun h => outside h.choose,outside_selection_no_failure (matching b s) (lawOperative b) ev outside⟩

theorem selected_condition_native (ev : E) (he : s.domain ev) (i : Node) :
    selectedCondition (matching b s) ev i ↔
      condition (nativeInput b (s.law.datum ⟨ev,s.subdomain ev he⟩) (s.family ⟨ev,he⟩)) i :=
  selected_restricts (matching b s) ev he i

theorem selected_failure_exact (ev : E) (he : s.domain ev) :
    failure (matching b s) (lawOperative b) ev ↔
      lawOperative b (s.law.datum ⟨ev,s.subdomain ev he⟩) ∧ ¬ selectedOperative b s ev := by
  rw [operative_on_domain b s ev he]
  exact failure_vs_operative (matching b s) (lawOperative b) ev he

theorem selected_minimal_counter (ev : E) (he : s.domain ev) (i : Node) :
    minimalFailure (matching b s) (lawOperative b) ev i ↔
      ancestorReady (matching b s) (lawOperative b) ev i ∧
      counter (nativeInput b (s.law.datum ⟨ev,s.subdomain ev he⟩) (s.family ⟨ev,he⟩)) i :=
  minimal_failure_witness (matching b s) (lawOperative b) ev he i

theorem selected_failure_cover (ev : E) :
    failure (matching b s) (lawOperative b) ev ↔
      ∃ i, minimalFailure (matching b s) (lawOperative b) ev i :=
  failure_cover (matching b s) (lawOperative b) ev

theorem selected_native_synthesis (ev : E) (he : s.domain ev) (h : selectedOperative b s ev) :
    let a := s.law.datum ⟨ev,s.subdomain ev he⟩
    let f := s.family ⟨ev,he⟩
    let operative := (operative_on_domain b s ev he).mp h
    (∀ rho : Rep (context b), ∃! x : CoreThreeLayerSynthesis.TransportedCore b a rho,
      CoreThreeLayerSynthesis.TransportedSpec b a rho x ∧ LCTR.LawFamilyTransport.AllConditions x.2) ∧
    (∀ rho (j : f.raw.selected) i theta,
      localPair b a f operative rho j i theta ∈ f.relation rho j i) ∧
    (∀ rho (j : f.raw.selected), CoreNativeAtlasConditions.ValueCov
      (atlas (context b) a f.raw rho j) (f.raw.order j)
      (regular b a f operative rho j) (f.relation rho j)) ∧
    (∀ rho sigma, TimeCondition (context b) a f rho sigma) := by
  dsimp only
  have all := native_differential_synthesis b (s.law.datum ⟨ev,s.subdomain ev he⟩)
    (s.family ⟨ev,he⟩) ((operative_on_domain b s ev he).mp h)
  exact ⟨all.1,all.2.2⟩

end LCTR.CoreNativeSelectedDifferential
