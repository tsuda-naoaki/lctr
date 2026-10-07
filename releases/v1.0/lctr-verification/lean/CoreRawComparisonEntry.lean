import CoreConfigurationComparison
import CoreExactCompletion

namespace LCTR.CoreRawComparisonEntry
open Set LCTR.CoreOperationalConfiguration LCTR.CoreConfigurationComparison
open LCTR.CoreLocalLoopRealization
set_option autoImplicit false
noncomputable section

theorem guarded_step_iff (P Q : Prop) : (P ∧ (P → Q)) ↔ P ∧ Q := by
  constructor
  · rintro ⟨hP,hQ⟩
    exact ⟨hP,hQ hP⟩
  · rintro ⟨hP,hQ⟩
    exact ⟨hP,fun _ => hQ⟩

variable (x : Configuration) (d : PairDatum x)
variable (specs : (h1 : L1 x) → (h2 : L2 x d) →
  (r : Fin 2) → Set (Spec (data x d h1 h2 r)))

abbrev typedInput (h1 : L1 x) (h2 : L2 x d) :=
  input x d h1 h2 (specs h1 h2)

def fullStageSeven : Prop := ∃ h1 : L1 x, ∃ h2 : L2 x d,
  CoreExactCompletion.residualStageSeven (typedInput x d specs h1 h2)

def guardedG : Prop := ∀ (h1 : L1 x) (h2 : L2 x d),
  CoreExactCompletion.residualStageSeven (typedInput x d specs h1 h2) →
  CoreComparisonStage.G (typedInput x d specs h1 h2)

def operative : Prop := fullStageSeven x d specs ∧ guardedG x d specs

theorem full_master_condition : operative x d specs ↔
    fullStageSeven x d specs ∧ guardedG x d specs := Iff.rfl

theorem operative_iff_residual : operative x d specs ↔
    ∃ h1 : L1 x, ∃ h2 : L2 x d,
      CoreComparisonStage.ResidualOperative (typedInput x d specs h1 h2) := by
  constructor
  · rintro ⟨⟨h1,h2,hs⟩,hg⟩
    exact ⟨h1,h2,hs,hg h1 h2 hs⟩
  · rintro ⟨h1,h2,hs,hg⟩
    exact ⟨⟨h1,h2,hs⟩,fun _ _ _ => hg⟩

theorem failed_entry_blocks (failed : ¬ L1 x ∨ ¬ L2 x d) :
    ¬ operative x d specs := by
  rintro ⟨⟨h1,h2,_⟩,_⟩
  rcases failed with h | h
  · exact h h1
  · exact h h2

theorem guardedG_before_entry (absent : ¬ fullStageSeven x d specs) :
    guardedG x d specs := by
  intro h1 h2 hs
  exact False.elim (absent ⟨h1,h2,hs⟩)

theorem full_conditions_generate (h : operative x d specs) :
    ∃ h1 : L1 x, ∃ h2 : L2 x d,
      ∃! out : CoreComparisonStage.Output (typedInput x d specs h1 h2),
        CoreComparisonStage.Valid (typedInput x d specs h1 h2) out := by
  obtain ⟨h1,h2,hr⟩ := (operative_iff_residual x d specs).mp h
  exact ⟨h1,h2,CoreComparisonStage.unique_generated_output _ hr⟩

theorem entered_residual (h : operative x d specs) (h1 : L1 x) (h2 : L2 x d) :
    CoreComparisonStage.ResidualOperative (typedInput x d specs h1 h2) := by
  obtain ⟨_,_,hr⟩ := (operative_iff_residual x d specs).mp h
  exact hr

end
end LCTR.CoreRawComparisonEntry
