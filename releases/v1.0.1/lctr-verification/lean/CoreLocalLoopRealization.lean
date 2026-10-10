import CoreSourceLoops

namespace LCTR.CoreLocalLoopRealization
open Set LCTR.CoreSourceMatch LCTR.CoreSourceLoops LCTR.Chapter03SourceOrderRecovery
universe u v w
set_option autoImplicit false
variable {U : Type u} {S : Type v} {V : U → Type w}

structure Spec (d : Data U S V) where
  base : U
  word : Path d base base
  pure : TransportOnly word
  domain : Set (ImageAt d.arrival base)

def Realizable (d : Data U S V) (s : Spec d) :=
  ∀ a ∈ s.domain, s.word.domain a

noncomputable def realize (d : Data U S V) (s : Spec d) (h : Realizable d s)
    (a : s.domain) : ImageAt d.arrival s.base := (h a.val a.property).choose

theorem realization_correct (d : Data U S V) (s : Spec d) (h : Realizable d s) (a : s.domain) :
    s.word.action a.val (realize d s h a) := (h a.val a.property).choose_spec

theorem realization_graph (d : Data U S V) (s : Spec d) (h : Realizable d s)
    (a : s.domain) (b : ImageAt d.arrival s.base) :
    realize d s h a = b ↔ s.word.action a.val b := by
  constructor
  · intro eq
    exact eq ▸ realization_correct d s h a
  · exact LCTR.CoreTypedWords.action_functional s.word a.val _ b (realization_correct d s h a)

theorem realization_injective (d : Data U S V) (s : Spec d) (h : Realizable d s) :
    Function.Injective (realize d s h) := by
  intro a b eq
  apply Subtype.ext
  exact LCTR.CoreTypedWords.action_injective s.word a.val b.val (realize d s h b)
    (eq ▸ realization_correct d s h a) (realization_correct d s h b)

theorem realization_unique (d : Data U S V) (s : Spec d) (h : Realizable d s)
    (f : s.domain → ImageAt d.arrival s.base) (correct : ∀ a, s.word.action a.val (f a)) :
    f = realize d s h := by
  funext a
  exact ((realization_graph d s h a (f a)).mpr (correct a)).symm

theorem realizable_iff_total_realization (d : Data U S V) (s : Spec d) :
    Realizable d s ↔ ∃ f : s.domain → ImageAt d.arrival s.base, ∀ a, s.word.action a.val (f a) := by
  constructor
  · intro h
    exact ⟨realize d s h,realization_correct d s h⟩
  · rintro ⟨f,hf⟩ a ha
    exact ⟨f ⟨a,ha⟩,hf ⟨a,ha⟩⟩

def IdOnSpecified (d : Data U S V) (s : Spec d) : Prop :=
  ∀ a ∈ s.domain, ∀ b, s.word.action a b → a=b

theorem specified_identity_iff (d : Data U S V) (s : Spec d) (h : Realizable d s) :
    IdOnSpecified d s ↔ ∀ a : s.domain, realize d s h a = a.val := by
  constructor
  · intro hid a
    exact (hid a.val a.property _ (realization_correct d s h a)).symm
  · intro hr a ha b hab
    exact (hr ⟨a,ha⟩).symm.trans ((realization_graph d s h ⟨a,ha⟩ b).mpr hab)

theorem global_identity_restricts (d : Data U S V) (h : PureLoopIdentity d) (s : Spec d) :
    IdOnSpecified d s := fun a _ b hab => h s.base s.word s.pure a b hab

def restrictSpec (d : Data U S V) (s : Spec d) (domain : Set (ImageAt d.arrival s.base)) : Spec d :=
  ⟨s.base,s.word,s.pure,domain⟩

theorem restriction_realizable (d : Data U S V) (s : Spec d) (h : Realizable d s)
    (domain : Set (ImageAt d.arrival s.base)) (sub : domain ⊆ s.domain) :
    Realizable d (restrictSpec d s domain) := fun a ha => h a (sub ha)

theorem restriction_agrees (d : Data U S V) (s : Spec d) (h : Realizable d s)
    (domain : Set (ImageAt d.arrival s.base)) (sub : domain ⊆ s.domain) (a : domain) :
    realize d (restrictSpec d s domain) (restriction_realizable d s h domain sub) a =
      realize d s h ⟨a.val,sub a.property⟩ := by
  apply LCTR.CoreTypedWords.action_functional s.word a.val
  · exact realization_correct d (restrictSpec d s domain) _ a
  · exact realization_correct d s h ⟨a.val,sub a.property⟩

theorem empty_specification (d : Data U S V) (s : Spec d) :
    Realizable d (restrictSpec d s ∅) ∧ IdOnSpecified d (restrictSpec d s ∅) := by
  constructor
  · exact fun _ ha => False.elim ha
  · exact fun _ ha => False.elim ha

def controlData : Data Unit Bool (fun _ => Bool) where
  arrival := fun _ => ⟨univ,fun x _ => x⟩
  unique := by
    apply (l1_iff_injective _).mpr
    intro i x y h
    exact Subtype.ext h
  transport := fun _ _ a b => b.val = !a.val
  admissible := fun _ _ => True
  transportInjective := by
    intro i j h
    constructor
    · intro a b c hb hc
      exact Subtype.ext (hb.trans hc.symm)
    · intro a b c ha hb
      apply Subtype.ext
      have eq := congrArg Bool.not (ha.symm.trans hb)
      simpa using eq

def controlValue (b : Bool) : ImageAt controlData.arrival () := ⟨b,⟨⟨b,trivial⟩,rfl⟩⟩

def controlPath : Path controlData () () := .cons ⟨.trPlus,trivial⟩ (.nil ())

theorem control_path_pure : TransportOnly controlPath := by
  constructor
  · intro h
    cases h
  · trivial

theorem control_global_identity_fails : ¬ PureLoopIdentity controlData := by
  intro h
  have bad := h () controlPath control_path_pure (controlValue false) (controlValue true)
    (show controlPath.action (controlValue false) (controlValue true) from ⟨controlValue true,rfl,rfl⟩)
  have eq : false = true := congrArg Subtype.val bad
  cases eq

def controlSpec : Spec controlData := ⟨(),controlPath,control_path_pure,∅⟩

theorem specified_identity_does_not_imply_global :
    Realizable controlData controlSpec ∧ IdOnSpecified controlData controlSpec ∧
    ¬ PureLoopIdentity controlData :=
  ⟨fun _ ha => False.elim ha,fun _ ha => False.elim ha,control_global_identity_fails⟩

end LCTR.CoreLocalLoopRealization
