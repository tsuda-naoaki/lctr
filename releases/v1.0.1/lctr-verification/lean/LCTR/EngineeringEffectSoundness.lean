import Init

namespace EngineeringEffectSoundness
inductive Effect where
  | form | eval | exactEvidence | admissibility | boundary
  deriving DecidableEq
inductive Method where
  | envelope | partition | unformed
  deriving DecidableEq
structure Data where
  typed : Bool
  supported : Bool
  formSat : Bool
  evalSat : Bool
  exactRequired : Bool
  externalPremise : Bool
  approxTarget : Bool
  boundaryRequired : Bool
  boundaryIncluded : Bool
  method : Method

def meaning (e : Effect) (d : Data) : Prop :=
  match e with
  | .form => d.formSat = false
  | .eval => d.evalSat = false
  | .exactEvidence => d.exactRequired = true
  | .admissibility => d.externalPremise = true
  | .boundary => d.approxTarget = true ∧ d.boundaryRequired = true ∧
      match d.method with
      | .unformed => d.evalSat = false
      | .envelope | .partition => d.boundaryIncluded = true

def verified (e : Effect) (d : Data) : Prop :=
  d.typed = true ∧ d.supported = true ∧ meaning e d

theorem verified_form (d : Data) (h : verified .form d) : d.formSat = false := h.2.2
theorem verified_eval (d : Data) (h : verified .eval d) : d.evalSat = false := h.2.2
theorem verified_boundary_target (d : Data) (h : verified .boundary d) :
    d.approxTarget = true ∧ d.boundaryRequired = true := ⟨h.2.2.1,h.2.2.2.1⟩
theorem verified_unformed (d : Data) (h : verified .boundary d)
    (hm : d.method = .unformed) : d.evalSat = false := by
  have hdata := h.2.2.2.2
  simp only [hm] at hdata
  exact hdata
theorem verified_formed (d : Data) (h : verified .boundary d)
    (hm : d.method = .envelope ∨ d.method = .partition) : d.boundaryIncluded = true := by
  have hdata := h.2.2.2.2
  cases hm with
  | inl he => simp only [he] at hdata; exact hdata
  | inr hp => simp only [hp] at hdata; exact hdata

def exampleData : Data :=
  ⟨true,true,true,true,true,true,true,true,true,.envelope⟩
theorem type_alone_is_insufficient :
    exampleData.typed = true ∧ ¬ meaning .form exampleData := by simp [verified, meaning, exampleData]
theorem exact_requirement_does_not_force_failure :
    verified .exactEvidence exampleData ∧ exampleData.formSat = true ∧
    exampleData.evalSat = true := by simp [verified, meaning, exampleData]
theorem each_effect_has_a_verified_instance (e : Effect) : ∃ d, verified e d := by
  cases e with
  | form => exact ⟨{exampleData with formSat := false}, by simp [verified, meaning, exampleData]⟩
  | eval => exact ⟨{exampleData with evalSat := false}, by simp [verified, meaning, exampleData]⟩
  | exactEvidence => exact ⟨exampleData, by simp [verified, meaning, exampleData]⟩
  | admissibility => exact ⟨exampleData, by simp [verified, meaning, exampleData]⟩
  | boundary => exact ⟨exampleData, by simp [verified, meaning, exampleData]⟩
end EngineeringEffectSoundness

#print axioms EngineeringEffectSoundness.verified_form
#print axioms EngineeringEffectSoundness.verified_eval
#print axioms EngineeringEffectSoundness.verified_boundary_target
#print axioms EngineeringEffectSoundness.verified_unformed
#print axioms EngineeringEffectSoundness.verified_formed
#print axioms EngineeringEffectSoundness.type_alone_is_insufficient
#print axioms EngineeringEffectSoundness.exact_requirement_does_not_force_failure
#print axioms EngineeringEffectSoundness.each_effect_has_a_verified_instance
