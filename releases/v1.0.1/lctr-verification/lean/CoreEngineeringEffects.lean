import CoreFiniteAudit
import LCTR.EngineeringEffectSoundness

namespace LCTR.CoreEngineeringEffects
set_option autoImplicit false
open Set LCTR.CoreTokenGraph LCTR.CoreEvaluation LCTR.CoreFiniteAudit
open LCTR.SelectedInputEvaluation
open EngineeringEffectSoundness (Effect Method)

inductive Flag where
  | missingField | provenance | recordCell | externalTime | nonmonotone
  | uncertaintyOverlap | contractVersion | solverFailure | dataGap
  deriving DecidableEq

def allowed : Flag → Effect → Prop
  | .missingField, e | .dataGap, e => e = .form ∨ e = .eval
  | .provenance, e | .uncertaintyOverlap, e | .contractVersion, e => e = .eval
  | .recordCell, e => e = .form ∨ e = .exactEvidence
  | .externalTime, e => e = .admissibility
  | .nonmonotone, e => e = .boundary
  | .solverFailure, e => e = .eval ∨ e = .exactEvidence

structure Input (Ref : Type) where
  formed : Token → Bool
  evaluated : Token → Bool
  condition : Token → Bool
  flags : Set Flag
  references : Flag → Set Ref
  references_nonempty : ∀ flag ∈ flags, (references flag).Nonempty
  Evidence : Token → Type
  provided : (t : Token) → Set (Evidence t)
  exactNeeded : (t : Token) → Evidence t → Prop
  external : Set Ref
  premiseAt : Ref → Token → Prop
  method : Ref → Method
  BoundaryPayload : Ref → Method → Type
  boundaryComponent : (t : Token) → (r : Ref) → (m : Method) → BoundaryPayload r m → Evidence t
  boundaryNeeded : Token → Ref → Prop

structure Candidate {Ref : Type} (d : Input Ref) where
  flag : Flag
  effect : Effect
  target : Token
  active : flag ∈ d.flags
  compatible : allowed flag effect

def effectMeaning {Ref : Type} (d : Input Ref) (c : Candidate d) : Prop :=
  match c.effect with
  | .form => d.formed c.target = false
  | .eval => d.evaluated c.target = false
  | .exactEvidence => ∃ a ∈ d.provided c.target, d.exactNeeded c.target a
  | .admissibility => ∃ r ∈ d.references c.flag, r ∈ d.external ∧ d.premiseAt r c.target
  | .boundary => c.target.1 = 3 ∧ ∀ r ∈ d.references c.flag,
      d.boundaryNeeded c.target r ∧
      match d.method r with
      | .unformed => d.evaluated c.target = false
      | .envelope => ∃ a : d.BoundaryPayload r .envelope,
          d.boundaryComponent c.target r .envelope a ∈ d.provided c.target
      | .partition => ∃ a : d.BoundaryPayload r .partition,
          d.boundaryComponent c.target r .partition a ∈ d.provided c.target

def verified {Ref : Type} (d : Input Ref)
    (coherent supported : Candidate d → Prop) (c : Candidate d) : Prop :=
  coherent c ∧ supported c ∧ effectMeaning d c

variable {Ref : Type} (d : Input Ref) (coherent supported : Candidate d → Prop) (c : Candidate d)

theorem verified_has_reference (h : verified d coherent supported c) :
    (d.references c.flag).Nonempty ∧ supported c := ⟨d.references_nonempty c.flag c.active,h.2.1⟩

theorem form_effect_actual (h : verified d coherent supported c) (he : c.effect = .form) :
    d.formed c.target = false := by
  have hm := h.2.2
  simpa [effectMeaning,he] using hm

theorem evaluation_effect_actual (h : verified d coherent supported c) (he : c.effect = .eval) :
    d.evaluated c.target = false := by
  have hm := h.2.2
  simpa [effectMeaning,he] using hm

theorem exact_requirement_component (h : verified d coherent supported c) (he : c.effect = .exactEvidence) :
    ∃ a ∈ d.provided c.target, d.exactNeeded c.target a := by
  have hm := h.2.2
  simpa [effectMeaning,he] using hm

theorem admissibility_actual_site (h : verified d coherent supported c) (he : c.effect = .admissibility) :
    ∃ r ∈ d.references c.flag, r ∈ d.external ∧ d.premiseAt r c.target := by
  have hm := h.2.2
  simpa [effectMeaning,he] using hm

theorem boundary_target_and_need (h : verified d coherent supported c) (he : c.effect = .boundary) :
    c.target.1 = 3 ∧ ∀ r ∈ d.references c.flag, d.boundaryNeeded c.target r := by
  have hm := h.2.2
  simp only [effectMeaning,he] at hm
  exact ⟨hm.1,fun r hr => (hm.2 r hr).1⟩

theorem envelope_component (h : verified d coherent supported c) (he : c.effect = .boundary)
    (r : Ref) (hr : r ∈ d.references c.flag) (method : d.method r = .envelope) :
    ∃ a : d.BoundaryPayload r .envelope,
      d.boundaryComponent c.target r .envelope a ∈ d.provided c.target := by
  have hm := h.2.2
  simp only [effectMeaning,he] at hm
  simpa only [method] using (hm.2 r hr).2

theorem partition_component (h : verified d coherent supported c) (he : c.effect = .boundary)
    (r : Ref) (hr : r ∈ d.references c.flag) (method : d.method r = .partition) :
    ∃ a : d.BoundaryPayload r .partition,
      d.boundaryComponent c.target r .partition a ∈ d.provided c.target := by
  have hm := h.2.2
  simp only [effectMeaning,he] at hm
  simpa only [method] using (hm.2 r hr).2

theorem unformed_boundary_input (h : verified d coherent supported c) (he : c.effect = .boundary)
    (r : Ref) (hr : r ∈ d.references c.flag) (method : d.method r = .unformed) :
    c.target.1 = 3 ∧ d.evaluated c.target = false := by
  have hm := h.2.2
  simp only [effectMeaning,he] at hm
  exact ⟨hm.1,by simpa only [method] using (hm.2 r hr).2⟩

def targetSet : Set Token := {t | ∃ c : Candidate d, verified d coherent supported c ∧ c.target = t}

theorem targets_stay_within_six_series (t : Token) (ht : t ∈ targetSet d coherent supported) :
    ∃! i : Fin 6, t.1 = i := by
  obtain ⟨_,_,_⟩ := ht
  exact ⟨t.1,rfl,fun _ h => h.symm⟩

theorem missing_formation_is_unformed (h : verified d coherent supported c) (he : c.effect = .form) :
    run d.formed d.evaluated d.condition 40 c.target = .unformed := by
  have hf := form_effect_actual d coherent supported c h he
  rw [finite_run_solves d.formed d.evaluated d.condition c.target]
  simp [update,state,hf]

theorem missing_evaluation_is_not_failed (h : verified d coherent supported c) (he : c.effect = .eval) :
    run d.formed d.evaluated d.condition 40 c.target ≠ .failed := by
  have hf := evaluation_effect_actual d coherent supported c h he
  intro bad
  rw [finite_run_solves d.formed d.evaluated d.condition c.target] at bad
  have parts := (update_failed_iff _ _ _ _ _ _).mp bad
  simp [hf] at parts

def exampleInput : Input Unit where
  formed := fun _ => true
  evaluated := fun _ => true
  condition := fun _ => true
  flags := {.solverFailure}
  references := fun _ => Set.univ
  references_nonempty := fun _ _ => ⟨(),trivial⟩
  Evidence := fun _ => Unit
  provided := fun _ => Set.univ
  exactNeeded := fun _ _ => True
  external := ∅
  premiseAt := fun _ _ => False
  method := fun _ => .unformed
  BoundaryPayload := fun _ _ => Unit
  boundaryComponent := fun _ _ _ _ => ()
  boundaryNeeded := fun _ _ => False

def exampleCandidate : Candidate exampleInput where
  flag := .solverFailure
  effect := .exactEvidence
  target := ⟨0,⟨0,by decide⟩⟩
  active := rfl
  compatible := Or.inr rfl

theorem requirement_need_not_fail :
    verified exampleInput (fun _ => True) (fun _ => True) exampleCandidate ∧
    ∀ t, run exampleInput.formed exampleInput.evaluated exampleInput.condition 40 t = .sat := by
  constructor
  · exact ⟨trivial,trivial,⟨(),trivial,trivial⟩⟩
  · have hs : Recurs Edge exampleInput.formed exampleInput.evaluated exampleInput.condition (fun _ => .sat) := by
      intro t
      simp [update,state,exampleInput]
    have eq := finite_run_unique _ _ _ _ hs
    intro t
    exact (congrFun eq t).symm

end LCTR.CoreEngineeringEffects
