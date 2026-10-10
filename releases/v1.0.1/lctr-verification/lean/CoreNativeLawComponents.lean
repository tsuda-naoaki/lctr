import CoreNativeLawTransport
import LCTR.LawCandidateRelationPartialOutputMapCurrentPaper

namespace LCTR.CoreNativeLawComponents
set_option autoImplicit false
open LCTR.CoreObserverTime LCTR.CoreNativeCurves LCTR.LawTimeTransport LCTR.LawFamilyTransport
universe u v w
variable {C : Type u} {D : Type v} {B : Type w} {I : Type} {Val : I → Type}

structure Context (C : Type u) (D : Type v) (B : Type w) (I : Type) (Val : I → Type) where
  data : Input C D B
  inc : IncTrans data
  single : Single data
  fiber : FiberCondition data inc single
  rho : RealEmbedding data inc
  observable : (i : I) → State data → Val i

abbrev NativeTime (c : Context C D B I Val) := RealDomain c.data c.inc c.rho
abbrev Values (J : Set I) := (i : J) → Val i.val
noncomputable def curve (c : Context C D B I Val) (i : I) : NativeTime c → Val i :=
  realCurve c.data c.inc c.single c.fiber c.rho (c.observable i)

structure ComponentInput (c : Context C D B I Val) where
  inIndices : Set I
  outIndices : Set I
  evalTimes : Set (NativeTime c)
  evalDomain : Set (NativeTime c × Values (Val := Val) inIndices)
  candidate : Set ((NativeTime c × Values (Val := Val) inIndices) × Values (Val := Val) outIndices)
  candidateTyped : ∀ p ∈ candidate, p.1 ∈ evalDomain

noncomputable def generated (c : Context C D B I Val) (a : ComponentInput c) :
    Component (NativeTime c) (Values (Val := Val) a.inIndices) (Values (Val := Val) a.outIndices) where
  evalTime t := t ∈ a.evalTimes
  input t i := curve c i.val t.val
  output t i := curve c i.val t.val
  evalDomain t x := (t,x) ∈ a.evalDomain
  relation t x y := ((t,x),y) ∈ a.candidate
  relationTyped t x y hx := a.candidateTyped ((t,x),y) hx

theorem generated_value_components (c : Context C D B I Val) (a : ComponentInput c)
    (t : {t // (generated c a).evalTime t}) :
    ((generated c a).input t = fun i : a.inIndices => curve c i.val t.val) ∧
    ((generated c a).output t = fun i : a.outIndices => curve c i.val t.val) := ⟨rfl,rfl⟩

theorem evaluation_tuple_components (c : Context C D B I Val) (a : ComponentInput c)
    (t : {t // (generated c a).evalTime t}) :
    evalTuple (generated c a) t =
      ((t.val, fun i : a.inIndices => curve c i.val t.val),
        fun i : a.outIndices => curve c i.val t.val) := rfl

theorem individual_input_typed (c : Context C D B I Val) (a : ComponentInput c)
    (t : {t // (generated c a).evalTime t}) :
    t.val ∈ a.evalTimes ∧ (evalTuple (generated c a) t).1.1 = t.val := ⟨t.property,rfl⟩

theorem evaluation_tuple_domain_typed (c : Context C D B I Val) (a : ComponentInput c)
    (adm : IndividualAdmissible (generated c a)) (t : {t // (generated c a).evalTime t}) :
    (evalTuple (generated c a) t).1 ∈ a.evalDomain := adm.2 t

theorem candidate_relation_typed (c : Context C D B I Val) (a : ComponentInput c) :
    ∀ p ∈ a.candidate, p.1 ∈ a.evalDomain := a.candidateTyped

theorem generated_membership_contract (c : Context C D B I Val) (a : ComponentInput c) :
    GeneratedMember (generated c a) ↔
      ∀ t : {t // (generated c a).evalTime t}, evalTuple (generated c a) t ∈ a.candidate := Iff.rfl

abbrev CandidateDomain (c : Context C D B I Val) (a : ComponentInput c) :=
  {x : NativeTime c × Values (Val := Val) a.inIndices //
    ∃ y : Values (Val := Val) a.outIndices, (x,y) ∈ a.candidate}

theorem native_partial_output (c : Context C D B I Val) (a : ComponentInput c)
    (unique : RightUnique (generated c a)) :
    ∃ f : CandidateDomain c a → Values (Val := Val) a.outIndices,
      (∀ p : CandidateDomain c a × Values (Val := Val) a.outIndices,
        (p.1.val,p.2) ∈ a.candidate ↔ p.2 = f p.1) ∧
      (∀ other, (∀ p : CandidateDomain c a × Values (Val := Val) a.outIndices,
        (p.1.val,p.2) ∈ a.candidate ↔ p.2 = other p.1) → other = f) := by
  exact LCTR.CurrentPaperCorrespondence.law_candidate_relation_partial_output_map
    (fun x y => (x,y) ∈ a.candidate)
    (fun x y z hy hz => unique x.1 x.2 y z hy hz)

noncomputable def nativeFamily (c : Context C D B I Val) {A : Type} (nonempty : Nonempty A)
    (a : A → ComponentInput c)
    (allowedDomains : (NativeTime c → Prop) → Prop)
    (faithful : ((j : A) → Reindex
      (Tuple (NativeTime c) (Values (Val := Val) (a j).inIndices) (Values (Val := Val) (a j).outIndices))
      (Tuple (NativeTime c) (Values (Val := Val) (a j).inIndices) (Values (Val := Val) (a j).outIndices))) → Prop) :
    Family (NativeTime c) A
      (fun j => Values (Val := Val) (a j).inIndices) (fun j => Values (Val := Val) (a j).outIndices) where
  indicesNonempty := nonempty
  component j := generated c (a j)
  admissibleCommon := allowedDomains
  faithful := faithful

theorem native_common_valid_contract (c : Context C D B I Val) {A : Type} (nonempty : Nonempty A)
    (a : A → ComponentInput c) (allowedDomains : (NativeTime c → Prop) → Prop)
    (faithful : ((j : A) → Reindex
      (Tuple (NativeTime c) (Values (Val := Val) (a j).inIndices) (Values (Val := Val) (a j).outIndices))
      (Tuple (NativeTime c) (Values (Val := Val) (a j).inIndices) (Values (Val := Val) (a j).outIndices))) → Prop)
    (k5 : K5 (nativeFamily c nonempty a allowedDomains faithful)) :
    (∃ t, common (nativeFamily c nonempty a allowedDomains faithful) t) ∧
    allowedDomains (common (nativeFamily c nonempty a allowedDomains faithful)) ∧
    (∀ t, common (nativeFamily c nonempty a allowedDomains faithful) t → ∀ j,
      ∃ ht : t ∈ (a j).evalTimes, evalTuple (generated c (a j)) ⟨t,ht⟩ ∈ (a j).candidate) := by
  refine ⟨k5.2.1, k5.2.2, ?_⟩
  intro t valid j
  exact valid j

theorem empty_index_values_unique (f g : Values (Val := Val) (∅ : Set I)) : f = g := by
  funext i
  exact False.elim i.property

end LCTR.CoreNativeLawComponents
