import CoreNativeLawFailure
import Mathlib.Tactic.Tauto

namespace LCTR.CoreLawCounterCases
set_option autoImplicit false
open LCTR.LawTimeTransport LCTR.LawFamilyTransport LCTR.CoreLawConditionGraph
variable {T A : Type} {X Y : A → Type}

def emptyTime (d : Family T A X Y) : Prop :=
  ∃ a, ¬ ∃ t, (d.component a).evalTime t
def outEval (d : Family T A X Y) : Prop :=
  ∃ a, ∃ t : {t // (d.component a).evalTime t},
    ¬ (d.component a).evalDomain t.val ((d.component a).input t)
def nonunique (d : Family T A X Y) (a : A) (t : T) (x : X a) : Prop :=
  ∃ y z, (d.component a).relation t x y ∧ (d.component a).relation t x z ∧ y ≠ z
def globalConflict (d : Family T A X Y) : Prop :=
  ∃ a t x, (d.component a).evalDomain t x ∧ nonunique d a t x
def genConflict (d : Family T A X Y) : Prop :=
  ∃ a, ∃ t : {t // (d.component a).evalTime t},
    (d.component a).evalDomain t.val ((d.component a).input t) ∧
      nonunique d a t.val ((d.component a).input t)
def offGenConflict (d : Family T A X Y) : Prop := globalConflict d ∧ ¬ genConflict d
def missingOutput (d : Family T A X Y) (a : A)
    (t : {t // (d.component a).evalTime t}) : Prop :=
  ¬ (d.component a).relation t.val ((d.component a).input t) ((d.component a).output t)
def fiberNonempty (d : Family T A X Y) (a : A)
    (t : {t // (d.component a).evalTime t}) : Prop :=
  ∃ y, (d.component a).relation t.val ((d.component a).input t) y
def emptyFiber (d : Family T A X Y) : Prop :=
  ∃ a t, missingOutput d a t ∧ ¬ fiberNonempty d a t
def altOutput (d : Family T A X Y) : Prop :=
  ∃ a t, missingOutput d a t ∧ fiberNonempty d a t
def loss (d : Family T A X Y) : Prop :=
  ∃ phi, d.faithful phi ∧ ∃ a z,
    tupleRelation (d.component a) z ∧ ¬ tupleRelation (d.component a) ((phi a).forward z)
def gain (d : Family T A X Y) : Prop :=
  ∃ phi, d.faithful phi ∧ ∃ a z,
    ¬ tupleRelation (d.component a) z ∧ tupleRelation (d.component a) ((phi a).forward z)
def emptyCommon (d : Family T A X Y) : Prop := ¬ ∃ t, common d t
def inadmissibleCommon (d : Family T A X Y) : Prop :=
  (∃ t, common d t) ∧ ¬ d.admissibleCommon (common d)

theorem condition1_countercases (d : Family T A X Y) :
    ¬ K1 d ↔ emptyTime d ∨ outEval d := by
  classical
  simp only [K1,IndividualAdmissible,emptyTime,outEval,not_forall,not_and_or,exists_or]

theorem condition2_countercase (d : Family T A X Y) :
    ¬ K2 d ↔ globalConflict d := by
  classical
  constructor
  · intro h
    have witness : ∃ a t x y z, (d.component a).relation t x y ∧
        (d.component a).relation t x z ∧ y ≠ z := by
      simpa only [K2,RightUnique,not_forall,exists_prop] using h
    obtain ⟨a,t,x,y,z,hy,hz,ne⟩ := witness
    exact ⟨a,t,x,(d.component a).relationTyped t x y hy,y,z,hy,hz,ne⟩
  · rintro ⟨a,t,x,_,y,z,hy,hz,ne⟩ h
    exact ne (h a t x y z hy hz)

theorem generated_conflict_is_global (d : Family T A X Y) :
    genConflict d → globalConflict d := by
  rintro ⟨a,t,hd,hc⟩
  exact ⟨a,t.val,(d.component a).input t,hd,hc⟩

theorem condition2_remainder (d : Family T A X Y) (h : ¬ K2 d) :
    ¬ genConflict d ↔ offGenConflict d :=
  ⟨fun hn => ⟨(condition2_countercase d).mp h,hn⟩,fun hu => hu.2⟩

theorem condition3_countercases (d : Family T A X Y) (h1 : K1 d) :
    ¬ K3 d ↔ emptyFiber d ∨ altOutput d := by
  classical
  have witness : ¬ K3 d ↔ ∃ a t, missingOutput d a t := by
    simp only [K3,h1,true_and,GeneratedMember,missingOutput,not_forall]
  rw [witness]
  constructor
  · rintro ⟨a,t,hm⟩
    by_cases hf : fiberNonempty d a t
    · exact Or.inr ⟨a,t,hm,hf⟩
    · exact Or.inl ⟨a,t,hm,hf⟩
  · rintro (⟨a,t,hm,_⟩ | ⟨a,t,hm,_⟩) <;> exact ⟨a,t,hm⟩

theorem alternate_output_is_distinct (d : Family T A X Y) (a : A)
    (t : {t // (d.component a).evalTime t}) (hm : missingOutput d a t)
    (hf : fiberNonempty d a t) :
    ∃ y, (d.component a).relation t.val ((d.component a).input t) y ∧
      y ≠ (d.component a).output t := by
  obtain ⟨y,hy⟩ := hf
  exact ⟨y,hy,fun eq => hm (eq ▸ hy)⟩

theorem condition4_countercases (d : Family T A X Y) :
    ¬ K4 d ↔ loss d ∨ gain d := by
  classical
  have inv : K4 d ↔ ∀ phi, d.faithful phi → ∀ a z,
      tupleRelation (d.component a) ((phi a).forward z) ↔ tupleRelation (d.component a) z := by
    unfold K4
    exact forall_congr' fun phi => imp_congr_right fun _ =>
      forall_congr' fun a => image_invariance_iff _ _
  rw [inv]
  constructor
  · intro hn
    have w : ∃ phi, d.faithful phi ∧ ∃ a z,
        ¬ (tupleRelation (d.component a) ((phi a).forward z) ↔ tupleRelation (d.component a) z) := by
      simpa only [not_forall,exists_prop] using hn
    obtain ⟨phi,hp,a,z,ne⟩ := w
    by_cases hz : tupleRelation (d.component a) z
    · exact Or.inl ⟨phi,hp,a,z,hz,fun ht => ne ⟨fun _ => hz,fun _ => ht⟩⟩
    · exact Or.inr ⟨phi,hp,a,z,hz,by tauto⟩
  · rintro (⟨phi,hp,a,z,hz,ht⟩ | ⟨phi,hp,a,z,hz,ht⟩) h
    · exact ht ((h phi hp a z).mpr hz)
    · exact hz ((h phi hp a z).mp ht)

theorem condition5_countercases (d : Family T A X Y) (h3 : K3 d) :
    ¬ K5 d ↔ emptyCommon d ∨ inadmissibleCommon d := by
  classical
  unfold K5 emptyCommon inadmissibleCommon
  tauto

theorem condition5_cases_exclusive (d : Family T A X Y) :
    ¬ (emptyCommon d ∧ inadmissibleCommon d) := fun h => h.1 h.2.1

def purePair (p q : Prop) : Prop := (p ∧ ¬ q) ∨ (q ∧ ¬ p)
theorem pair_remainder (p q : Prop) (occurs : p ∨ q) :
    ¬ purePair p q ↔ p ∧ q := by unfold purePair; tauto

theorem condition135_remainders (d : Family T A X Y) :
    (¬ K1 d → (¬ purePair (emptyTime d) (outEval d) ↔ emptyTime d ∧ outEval d)) ∧
    (K1 d → ¬ K3 d → (¬ purePair (emptyFiber d) (altOutput d) ↔ emptyFiber d ∧ altOutput d)) ∧
    (K3 d → ¬ K5 d → purePair (emptyCommon d) (inadmissibleCommon d)) := by
  refine ⟨fun h => pair_remainder _ _ ((condition1_countercases d).mp h),
    fun h1 h3 => pair_remainder _ _ ((condition3_countercases d h1).mp h3),?_⟩
  intro h3 h5
  have h := (condition5_countercases d h3).mp h5
  have ex := condition5_cases_exclusive d
  unfold purePair
  tauto

theorem condition4_remainder (d : Family T A X Y) (h : ¬ K4 d) :
    ¬ purePair (loss d) (gain d) ↔ loss d ∧ gain d :=
  pair_remainder _ _ ((condition4_countercases d).mp h)

end LCTR.CoreLawCounterCases
