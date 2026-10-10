import Mathlib.Analysis.Real.Cardinality
import Mathlib.Topology.MetricSpace.Basic

namespace LCTR.CoreCountableChartBoundary
set_option autoImplicit false
open Set

theorem real_open_countable_empty (S : Set ℝ) (hc : S.Countable) (ho : IsOpen S) :
    S = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp ho x hx
  have hi : (Ioo (x - ε) (x + ε)).Countable := by
    apply hc.mono
    simpa only [Real.ball_eq_Ioo] using hball
  have hle := Cardinal.Real.Ioo_countable_iff.mp hi
  linarith

theorem open_chart_domain_empty {T : Type} (A : Set T) (hc : A.Countable)
    (φ : T → ℝ) (ho : IsOpen (φ '' A)) : A = ∅ := by
  have h := real_open_countable_empty (φ '' A) (hc.image φ) ho
  exact Set.image_eq_empty.mp h

theorem no_nonempty_countable_cover {T I : Type} (H : Set T)
    (hc : H.Countable) (hne : H.Nonempty) (D : I → Set T) (φ : I → T → ℝ)
    (within : ∀ i, D i ⊆ H) (opened : ∀ i, IsOpen (φ i '' D i)) :
    ¬ (∀ t ∈ H, ∃ i, t ∈ D i) := by
  intro covered
  obtain ⟨t, ht⟩ := hne
  obtain ⟨i, hi⟩ := covered t ht
  have empty := open_chart_domain_empty (D i) (hc.mono (within i)) (φ i) (opened i)
  rw [empty] at hi
  exact hi

theorem countable_tagged_sources_iff {I : Type} (A : Set I) :
    (A ×ˢ (Set.univ : Set ℕ)).Countable ↔ A.Countable := by
  constructor
  · intro h
    have eq : Prod.fst '' (A ×ˢ (Set.univ : Set ℕ)) = A := by
      ext x
      constructor
      · rintro ⟨⟨i,n⟩, ⟨hi,_⟩, rfl⟩
        exact hi
      · intro hx
        exact ⟨(x,0),⟨hx,Set.mem_univ _⟩,rfl⟩
    rw [← eq]
    exact h.image Prod.fst
  · intro h
    exact h.prod (Set.to_countable _)

theorem each_source_countable (r : ℝ) :
    (Set.range (fun n : ℕ => (r,n))).Countable := Set.countable_range _

theorem all_sources_uncountable :
    ¬ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℕ)).Countable := by
  intro h
  exact Cardinal.not_countable_real ((countable_tagged_sources_iff Set.univ).mp h)

theorem empty_time_domain_allows_empty_cover :
    (∀ t ∈ (∅ : Set ℕ), ∃ _i : Unit, t ∈ (∅ : Set ℕ)) ∧
    IsOpen ((fun _ : ℕ => (0 : ℝ)) '' (∅ : Set ℕ)) := by
  simp

end LCTR.CoreCountableChartBoundary
