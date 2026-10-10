import CoreLawConditionGraph
import CoreContinuumDatum
import CoreDifferentialFailure

namespace LCTR.CoreJudgmentBoundary
set_option autoImplicit false
open LCTR.LawFamilyTransport LCTR.LawTimeTransport
open LCTR.CoreContinuumDatum LCTR.DifferentialNativeDomains
variable {T A Ω : Type} {X Y : A → Type}

theorem law3_trajectory_membership (d : Family T A X Y) :
    LCTR.CoreLawConditionGraph.condition d 2 ↔
      K1 d ∧ ∀ a, GeneratedMember (d.component a) := by
  rfl

theorem law4_relation_reexpression (d : Family T A X Y) :
    LCTR.CoreLawConditionGraph.condition d 3 ↔
      ∀ phi, d.faithful phi → ∀ a,
        ImageInvariant (tupleRelation (d.component a)) (phi a) := by
  rfl

theorem differential3_jet_membership (d : Input Ω) :
    LCTR.CoreDifferentialFailure.condition d 2 ↔
      ∀ r, ∃ h : d.jet r, d.member r h := Iff.rfl

theorem differential4_value_covariance (d : Input Ω) :
    LCTR.CoreDifferentialFailure.condition d 3 ↔
      ∀ r, ∃ h : d.atlas r, d.value r h := Iff.rfl

theorem differential5_time_covariance (d : Input Ω) :
    LCTR.CoreDifferentialFailure.condition d 4 ↔
      ∀ r s, ∃ h : d.atlas r, ∃ k : d.atlas s, d.time r s h k := Iff.rfl

theorem approximation_quantitative (p : Packet) (i : Fin 6) :
    Actual p ⟨i.val,by omega⟩ ↔ firstDefect p i ≤ p.tolerance i := by
  simp only [Actual, i.isLt, dite_true]

theorem approximation7_extension (p : Packet) : Actual p 6 ↔ Extension p.maps := by
  simp [Actual]

theorem approximation8_order (p : Packet) : Actual p 7 ↔ OrderCondition p.maps p.orders := by
  simp [Actual]

theorem approximation9_relation (p : Packet) : Actual p 8 ↔ RelationCondition p.relations := by
  simp [Actual]

def ApproxComplete (p : Packet) : Prop := ∀ i, Actual p i

structure ComponentBridge (p : Packet) (d : Input Ω) where
  source : Fin 5 → Fin 9
  transfer : ∀ i, Actual p (source i) → LCTR.CoreDifferentialFailure.condition d i

theorem component_bridge_suffices (p : Packet) (d : Input Ω)
    (bridge : ComponentBridge p d) (h : ApproxComplete p) : complete d :=
  (LCTR.CoreDifferentialFailure.all_conditions_complete d).mp
    (fun i => bridge.transfer i (h (bridge.source i)))

def completeDifferential : Input Unit where
  atlas _ := True
  jet _ := True
  member _ _ := True
  value _ _ := True
  time _ _ _ _ := True

theorem complete_differential_control : complete completeDifferential :=
  ⟨fun _ => trivial,fun _ => trivial,fun _ => ⟨trivial,trivial⟩,
    fun _ => ⟨trivial,trivial⟩,fun _ _ => ⟨trivial,trivial,trivial⟩⟩

theorem incomplete_differential_control : ¬ complete independentJet :=
  fun h => h.1 ()

theorem same_approximation_different_differential_results (p : Packet)
    (h : ApproxComplete p) :
    (ApproxComplete p ∧ complete completeDifferential) ∧
      (ApproxComplete p ∧ ¬ complete independentJet) :=
  ⟨⟨h,complete_differential_control⟩,⟨h,incomplete_differential_control⟩⟩

theorem no_unconditional_transfer (p : Packet) (h : ApproxComplete p) :
    ¬ ∀ d : Input Unit, ApproxComplete p → complete d :=
  fun transfer => incomplete_differential_control (transfer independentJet h)

theorem inconsistent_bridge_rejected (p : Packet) (h : ApproxComplete p) :
    ¬ Nonempty (ComponentBridge p independentJet) := by
  rintro ⟨bridge⟩
  exact incomplete_differential_control (component_bridge_suffices p independentJet bridge h)

theorem jet_membership_native_domain (d : Input Ω)
    (h : LCTR.CoreDifferentialFailure.condition d 2) :
    LCTR.CoreDifferentialFailure.condition d 1 := third_requires_second d h

end LCTR.CoreJudgmentBoundary
