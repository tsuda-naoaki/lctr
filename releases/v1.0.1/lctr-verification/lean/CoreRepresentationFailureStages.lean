import CoreRepresentationFailure
import CoreRepresentationStages

namespace LCTR.CoreRepresentationFailureStages
set_option autoImplicit false
open LCTR.CoreTokenGraph LCTR.CoreFiniteAudit LCTR.SelectedInputEvaluation
open LCTR.CoreComparisonFailure (cmpToken)
open LCTR.CoreRepresentationFailure
open LCTR.CoreExactStructure
namespace RS
export LCTR.CoreRepresentationStages (Base First Second Third atFirst)
end RS

variable {U S : Type} {V : U → Type}

def LocalCondition (p : RS.Base U S V) : Prop :=
  ∃ h : RS.First p, ∀ i, LocalInc (RS.atFirst p h) i
def GlobalCondition (p : RS.Base U S V) : Prop :=
  ∃ h : RS.First p, GlobalInc (RS.atFirst p h)

theorem local_condition_exact (p : RS.Base U S V) : LocalCondition p ↔ RS.Second p := by
  constructor
  · rintro ⟨h,hl⟩; exact ⟨h,hl⟩
  · intro h; exact ⟨h.first,h.localInc⟩

theorem global_condition_exact (p : RS.Base U S V) (h : RS.Second p) :
    GlobalCondition p ↔ RS.Third p := by
  constructor
  · rintro ⟨_,hg⟩; exact ⟨h,hg⟩
  · intro ht; exact ⟨ht.second.first,ht.globalInc⟩

theorem local_condition_on_formed_input (p : RS.Base U S V) (h : RS.First p) :
    LocalCondition p ↔ ∀ i, LocalInc (RS.atFirst p h) i := by
  exact ⟨fun ⟨_,hl⟩ => hl,fun hl => ⟨h,hl⟩⟩

theorem global_condition_on_formed_input (p : RS.Base U S V) (h : RS.First p) :
    GlobalCondition p ↔ GlobalInc (RS.atFirst p h) := by
  exact ⟨fun ⟨_,hg⟩ => hg,fun hg => ⟨h,hg⟩⟩

 
 
noncomputable def condition (p : RS.Base U S V) (t : Token) : Bool := by
  classical
  exact if series t = 1 then
    if index t = 1 then decide (RS.First p)
    else if index t = 2 then decide (LocalCondition p)
    else decide (GlobalCondition p)
  else true

theorem condition_values (p : RS.Base U S V) :
    (condition p (reprToken 0) = true ↔ RS.First p) ∧
    (condition p (reprToken 1) = true ↔ LocalCondition p) ∧
    (condition p (reprToken 2) = true ↔ GlobalCondition p) := by
  classical
  simp [condition,reprToken,series,index]

noncomputable def config : Config (RS.Base U S V) where
  op := fun _ => True
  formed := fun _ _ => true
  evaluated := fun _ _ => true
  condition := condition
  comparison_ready := fun _ _ _ => ⟨rfl,rfl⟩
  comparison_pass := by
    intro p _ j
    simp [condition,cmpToken,series]
  representation_ready := fun _ _ _ => ⟨rfl,rfl⟩
  outside_unformed := fun _ h => False.elim (h trivial)

theorem generated_stage_one (p : RS.Base U S V) :
    Generated (condition p) 1 ↔ RS.First p := by
  have cv := (condition_values p).1
  change (∀ j : Fin 3, j.val < 1 → condition p (reprToken j) = true) ↔ _
  constructor
  · intro h; exact cv.mp (h 0 (by decide))
  · intro h j hj
    have ji : j = 0 := Fin.ext (by omega)
    rw [ji]
    exact cv.mpr h

theorem generated_stage_two (p : RS.Base U S V) :
    Generated (condition p) 2 ↔ RS.Second p := by
  have cv := (condition_values p).2.1
  constructor
  · intro h
    exact (local_condition_exact p).mp (cv.mp (h 1 (by decide)))
  · intro h j hj
    have ij : j = 0 ∨ j = 1 := by
      rcases Nat.eq_zero_or_pos j.val with hz | hz
      · exact Or.inl (Fin.ext hz)
      · exact Or.inr (Fin.ext (by omega))
    rcases ij with rfl | rfl
    · exact (condition_values p).1.mpr h.first
    · exact cv.mpr ((local_condition_exact p).mpr h)

theorem generated_stage_three (p : RS.Base U S V) :
    Generated (condition p) 3 ↔ RS.Third p := by
  constructor
  · intro h
    have hs : RS.Second p := (generated_stage_two p).mp (fun j hj => h j (by omega))
    exact (global_condition_exact p hs).mp ((condition_values p).2.2.mp (h 2 (by decide)))
  · intro h j _
    by_cases hj : j.val < 2
    · exact (generated_stage_two p).mpr h.second j hj
    · have ji : j = 2 := Fin.ext (by omega)
      rw [ji]
      exact (condition_values p).2.2.mpr ((global_condition_exact p h.second).mpr h)

theorem native_stage_failure_one (p : RS.Base U S V) :
    p ∈ region config 0 ↔ ¬ RS.First p := by
  rw [native_generation_boundary config p trivial 0]
  change Generated (condition p) 0 ∧ ¬ Generated (condition p) 1 ↔ _
  rw [generated_stage_one]
  simp [Generated]

theorem native_stage_failure_two (p : RS.Base U S V) :
    p ∈ region config 1 ↔ RS.First p ∧ ¬ RS.Second p := by
  rw [native_generation_boundary config p trivial 1]
  change Generated (condition p) 1 ∧ ¬ Generated (condition p) 2 ↔ _
  rw [generated_stage_one,generated_stage_two]

theorem native_stage_failure_three (p : RS.Base U S V) :
    p ∈ region config 2 ↔ RS.Second p ∧ ¬ RS.Third p := by
  rw [native_generation_boundary config p trivial 2]
  change Generated (condition p) 2 ∧ ¬ Generated (condition p) 3 ↔ _
  rw [generated_stage_two,generated_stage_three]

theorem native_failure_domain (p : RS.Base U S V) :
    p ∈ failureDomain config ↔ ¬ RS.Third p := by
  have all : (∀ i : Fin 3, condition p (reprToken i) = true) ↔
      Generated (condition p) 3 := by
    exact ⟨fun h j _ => h j,fun h j => h j j.isLt⟩
  change True ∧ ¬ (∀ i : Fin 3, condition p (reprToken i) = true) ↔ _
  rw [true_and,all,generated_stage_three]

theorem native_failure_signature (p : RS.Base U S V) (h : ¬ RS.Third p) :
    (∃! i : Fin 3, signature config p = basis i) ∧
    (∑ i : Fin 3, signature config p i) = 1 :=
  signature_one_hot config p ((native_failure_domain p).mpr h)

theorem native_second_failure_witness (p : RS.Base U S V) (h : RS.First p) :
    p ∈ region config 1 ↔ ∃ i, ¬ LocalInc (RS.atFirst p h) i := by
  rw [native_stage_failure_two,show RS.First p ∧ ¬ RS.Second p ↔ ¬ RS.Second p from
    and_iff_right h,← local_condition_exact p,local_condition_on_formed_input p h]
  exact not_forall

theorem native_third_failure_witness (p : RS.Base U S V) (h : RS.Second p) :
    p ∈ region config 2 ↔ ¬ GlobalInc (RS.atFirst p h.first) := by
  rw [native_stage_failure_three,show RS.Second p ∧ ¬ RS.Third p ↔ ¬ RS.Third p from
    and_iff_right h,← global_condition_exact p h,global_condition_on_formed_input p h.first]

open LCTR.TransitiveIncomparabilityQuotientCore

theorem native_second_failure_triple (p : RS.Base U S V) (h : RS.First p) :
    p ∈ region config 1 ↔ ∃ i, ∃ x y z : localCarrier (RS.atFirst p h) i,
      Inc (fun a b => (strictData (RS.atFirst p h)).lt a.val b.val) x y ∧
      Inc (fun a b => (strictData (RS.atFirst p h)).lt a.val b.val) y z ∧
      ¬ Inc (fun a b => (strictData (RS.atFirst p h)).lt a.val b.val) x z := by
  classical
  rw [native_second_failure_witness p h]
  simp only [LocalInc,not_forall,exists_prop]

theorem native_third_failure_triple (p : RS.Base U S V) (h : RS.Second p) :
    p ∈ region config 2 ↔ ∃ x y z : Canonical (RS.atFirst p h.first),
      Inc (strictData (RS.atFirst p h.first)).lt x y ∧
      Inc (strictData (RS.atFirst p h.first)).lt y z ∧
      ¬ Inc (strictData (RS.atFirst p h.first)).lt x z := by
  classical
  rw [native_third_failure_witness p h]
  simp only [GlobalInc,not_forall,exists_prop]

theorem native_first_failure_four_points (p : RS.Base U S V) :
    let s := LCTR.CoreTypedWords.orbitSetoid
      (LCTR.CoreComparisonIntegration.comparisonSystem p.arrival p.unique
        p.transport p.admissible p.transportInjective)
    let r := LCTR.CorePreorderQuotient.Pullback
      (LCTR.CoreSourceMatch.recover p.arrival p.unique) p.sourceOrder
    p ∈ region config 0 ↔ ∃ a a' b b', s.r a a' ∧ s.r b b' ∧ ¬ (r a b ↔ r a' b') := by
  classical
  dsimp only
  rw [native_stage_failure_one]
  have equiv : RS.First p ↔ LCTR.CorePreorderQuotient.OrdDesc
      (LCTR.CoreTypedWords.orbitSetoid
        (LCTR.CoreComparisonIntegration.comparisonSystem p.arrival p.unique
          p.transport p.admissible p.transportInjective))
      (LCTR.CorePreorderQuotient.Pullback
        (LCTR.CoreSourceMatch.recover p.arrival p.unique) p.sourceOrder) :=
    ⟨fun h => h.descent,fun h => ⟨h⟩⟩
  rw [equiv]
  simp only [LCTR.CorePreorderQuotient.OrdDesc,not_forall,exists_prop]

end LCTR.CoreRepresentationFailureStages
