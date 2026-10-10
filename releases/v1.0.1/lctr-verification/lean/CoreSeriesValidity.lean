import CoreAuditGroups

namespace LCTR.CoreSeriesValidity
set_option autoImplicit false
open LCTR.CoreTokenGraph LCTR.CoreEvaluation LCTR.CoreFiniteAudit LCTR.CoreAuditGroups
open LCTR.SelectedInputEvaluation
universe u v

def SeriesComplete (q : Token → State) (i : Fin 6) : Prop := ∀ j, q ⟨i,j⟩ = .sat
def Full (q : Token → State) : Prop := ∀ i, SeriesComplete q i
def Strict (q : Token → State) : Prop := ∀ i, i ≠ 3 → SeriesComplete q i
def Approximation (q : Token → State) : Prop := SeriesComplete q 3

theorem series_completion_iff (q : Token → State) : Full q ↔ ∀ t, q t = .sat := by
  exact ⟨fun h t => h t.1 t.2, fun h i j => h ⟨i,j⟩⟩

theorem completion_split (q : Token → State) : Full q ↔ Strict q ∧ Approximation q := by
  constructor
  · intro h; exact ⟨fun i _ => h i, h 3⟩
  · rintro ⟨hs,ha⟩ i
    by_cases hi : i = 3
    · subst i; exact ha
    · exact hs i hi

theorem completion_clears_failures (q : Token → State) (h : Full q) :
    {t | q t = .failed} = ∅ ∧
    {t : Token | t.1 ≠ 3 ∧ q t = .failed} = ∅ ∧
    {t : Token | t.1 = 3 ∧ q t = .failed} = ∅ := by
  have all := (series_completion_iff q).mp h
  simp [all]

theorem no_failure_does_not_imply_completion :
    ∃ q : Token → State, {t | q t = .failed} = ∅ ∧ ¬ Full q := by
  refine ⟨fun _ => .unformed,by simp,?_⟩
  intro h
  have bad := h (0 : Fin 6) ⟨0,by decide⟩
  cases bad

theorem native_completion_iff_inputs (f e c : Token → Bool) :
    Full (run f e c 40) ↔ ∀ t, f t = true ∧ e t = true ∧ c t = true := by
  rw [series_completion_iff]
  constructor
  · intro h t
    have ht := h t
    rw [finite_run_solves f e c t] at ht
    have parts := (state_sat_iff _ _ _ _).mp ht
    exact ⟨parts.1,parts.2.1,parts.2.2.2⟩
  · intro inputs
    have hs : Recurs Edge f e c (fun _ => .sat) := by
      intro t
      obtain ⟨hf,he,hc⟩ := inputs t
      simp [update,state,hf,he,hc]
    have eq := finite_run_unique f e c (fun _ => .sat) hs
    intro t
    exact (congrFun eq t).symm

theorem native_audit_pass_iff_completion (f e c : Token → Bool) :
    (∀ t, auditOutput f e c t = .pass) ↔ Full (run f e c 40) :=
  (forall_congr' (native_pass_iff f e c)).trans (series_completion_iff _).symm

structure Profile (E : Type u) (L : Type v) where
  strict : E → {t : Token // t.1 ≠ 3} → State
  approximation : E → L → Fin (count 3) → State

def stateAt {E : Type u} {L : Type v} (p : Profile E L) (e : E) (l : L) (t : Token) : State := by
  rcases t with ⟨i,j⟩
  by_cases h : i = 3
  · subst i; exact p.approximation e l j
  · exact p.strict e ⟨⟨i,j⟩,h⟩

def strictComplete {E : Type u} {L : Type v} (p : Profile E L) (e : E) : Prop :=
  ∀ t, p.strict e t = .sat
def approxComplete {E : Type u} {L : Type v} (p : Profile E L) (e : E) (l : L) : Prop :=
  ∀ i, p.approximation e l i = .sat

theorem profile_completion_iff {E : Type u} {L : Type v} (p : Profile E L) (e : E) (l : L) :
    Full (stateAt p e l) ↔ strictComplete p e ∧ approxComplete p e l := by
  rw [series_completion_iff]
  constructor
  · intro h
    constructor
    · rintro ⟨⟨i,j⟩,hi⟩
      simpa only [stateAt,dif_neg hi] using h ⟨i,j⟩
    · intro i
      simpa [stateAt] using h ⟨3,i⟩
  · rintro ⟨hs,ha⟩ ⟨i,j⟩
    by_cases hi : i = 3
    · subst i; exact ha j
    · simpa only [stateAt,dif_neg hi] using hs ⟨⟨i,j⟩,hi⟩

theorem profile_strict_scale_independent {E : Type u} {L : Type v} (p : Profile E L)
    (e : E) (a b : L) (t : Token) (ht : t.1 ≠ 3) : stateAt p e a t = stateAt p e b t := by
  rcases t with ⟨i,j⟩
  simp only [stateAt,dif_neg ht]

theorem validity_domain_intersection {E : Type u} {L : Type v} (p : Profile E L) (e : E) :
    {l | Full (stateAt p e l)} = {_l : L | strictComplete p e} ∩ {l | approxComplete p e l} := by
  ext l
  exact profile_completion_iff p e l

end LCTR.CoreSeriesValidity
