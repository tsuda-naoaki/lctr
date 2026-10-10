import CoreLocalizationBundle

namespace LCTR.CoreRelativeStateProfile
set_option autoImplicit false
open Set LCTR.CoreTokenGraph LCTR.CoreEvaluation LCTR.SelectedInputEvaluation
open LCTR.CoreSeriesValidity LCTR.CoreFirstFailureReport LCTR.CoreLocalizationBundle

def fiber (s : Token → State) (v : State) : Set Token := {t | s t = v}

theorem four_state_cover (s : Token → State) :
    fiber s .sat ∪ fiber s .failed ∪ fiber s .unformed ∪ fiber s .unevaluable = Set.univ := by
  ext t
  simp only [fiber,Set.mem_union,Set.mem_ofPred_eq,Set.mem_univ,iff_true]
  cases s t <;> simp

theorem fibers_disjoint (s : Token → State) (v w : State) (h : v ≠ w) :
    Disjoint (fiber s v) (fiber s w) := by
  apply Set.disjoint_left.mpr
  exact fun _ hv hw => h (hv.symm.trans hw)

theorem unique_state_membership (s : Token → State) (t : Token) :
    ∃! v : State, t ∈ fiber s v := ⟨s t,rfl,fun _ h => h.symm⟩

theorem full_iff_sat_universe (s : Token → State) :
    Full s ↔ fiber s .sat = Set.univ := by
  rw [series_completion_iff]
  constructor
  · intro h
    ext t
    simp [fiber,h t]
  · intro h t
    have ht : t ∈ fiber s .sat := by rw [h]; exact Set.mem_univ t
    exact ht

theorem unique_series_membership (t : Token) : ∃! i : Fin 6, t.1 = i :=
  ⟨t.1,rfl,fun _ h => h.symm⟩

structure Profile (L : Type) where
  fullyValid : Prop
  fibers : State → Set Token
  boundary : Set (L × ApproxSignature)

def profile {L : Type} [LinearOrder L] (q : L → Token → State)
    (b : L → ApproxSignature) (l : L) : Profile L :=
  ⟨Full (q l),fiber (q l),boundaryData (approxDomain q) b⟩

theorem profile_and_localization_agree {L : Type} [LinearOrder L]
    (q : L → Token → State) (b : L → ApproxSignature) (l : L) :
    ((profile q b l).fullyValid ↔ l ∈ (assemble q b l).fullValidity) ∧
    (profile q b l).fibers .failed = (assemble q b l).firstFailure.1 ∧
    (profile q b l).boundary = (assemble q b l).firstFailure.2.2 := ⟨Iff.rfl,rfl,rfl⟩

theorem combined_outputs_independent {L : Type} [LinearOrder L]
    (f e c : L → Token → Bool) (q r : L → Token → State)
    (hq : ∀ l, Recurs Edge (f l) (e l) (c l) (q l))
    (hr : ∀ l, Recurs Edge (f l) (e l) (c l) (r l))
    (b : L → ApproxSignature) (l : L) :
    (profile q b l,assemble q b l) = (profile r b l,assemble r b l) := by
  rw [native_solution_family_unique f e c q hq,native_solution_family_unique f e c r hr]

end LCTR.CoreRelativeStateProfile
