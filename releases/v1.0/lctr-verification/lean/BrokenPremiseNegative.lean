import Mathlib.Data.Fin.Basic
import Lean.Elab.Tactic.Omega
import LCTR.TransitiveIncomparabilityQuotientCore

namespace LCTR.OrderEmbeddingBridgeV1.Negative

open LCTR.TransitiveIncomparabilityQuotientCore

def brokenStrict (x y : Fin 3) : Prop :=
  x.val = 0 ∧ y.val = 2

theorem brokenStrict_irreflexive : ∀ x, ¬ brokenStrict x x := by
  intro x h
  rcases h with ⟨hx0, hx2⟩
  omega

theorem brokenStrict_transitive :
    ∀ {x y z}, brokenStrict x y → brokenStrict y z → brokenStrict x z := by
  intro x y z hxy hyz
  rcases hxy with ⟨hx0, hy2⟩
  rcases hyz with ⟨hy0, hz2⟩
  omega

theorem brokenStrict_incomparability_not_transitive :
    ¬ (∀ {x y z},
      Inc brokenStrict x y →
      Inc brokenStrict y z →
      Inc brokenStrict x z) := by
  intro h
  have h01 : Inc brokenStrict (0 : Fin 3) (1 : Fin 3) := by
    simp [Inc, brokenStrict]
  have h12 : Inc brokenStrict (1 : Fin 3) (2 : Fin 3) := by
    simp [Inc, brokenStrict]
  have h02 := h h01 h12
  simpa [Inc, brokenStrict] using h02

#print axioms brokenStrict_irreflexive
#print axioms brokenStrict_transitive
#print axioms brokenStrict_incomparability_not_transitive

end LCTR.OrderEmbeddingBridgeV1.Negative
