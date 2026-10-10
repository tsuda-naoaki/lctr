import Mathlib.Data.EReal.Operations
import Mathlib.Data.ENNReal.Real
import Mathlib.Order.Interval.Set.Basic

namespace LCTR.CoreContinuumBoundary
set_option autoImplicit false
open Set
open scoped ENNReal NNReal

noncomputable def margin (a b : ℝ≥0∞) : EReal :=
  if a = ⊤ then if b = ⊤ then 0 else ⊤
  else if b = ⊤ then ⊥ else ((a.toReal - b.toReal : ℝ) : EReal)

noncomputable def excess (a b : ℝ≥0∞) : EReal := max 0 (-margin a b)

theorem margin_nonneg (a b : ℝ≥0∞) : 0 ≤ margin a b ↔ b ≤ a := by
  by_cases ha : a = ⊤
  · subst a; by_cases hb : b = ⊤ <;> simp [margin,hb]
  · by_cases hb : b = ⊤
    · subst b; simp [margin,ha]
    · rw [margin,if_neg ha,if_neg hb,EReal.coe_nonneg,sub_nonneg,ENNReal.toReal_le_toReal hb ha]

theorem margin_zero (a b : ℝ≥0∞) : margin a b = 0 ↔ b = a := by
  by_cases ha : a = ⊤
  · subst a; by_cases hb : b = ⊤ <;> simp [margin,hb]
  · by_cases hb : b = ⊤
    · subst b; simp [margin,ha,Ne.symm ha]
    · rw [margin,if_neg ha,if_neg hb,EReal.coe_eq_zero,sub_eq_zero]
      constructor
      · intro h
        apply le_antisymm
        · exact (ENNReal.toReal_le_toReal hb ha).mp (le_of_eq h.symm)
        · exact (ENNReal.toReal_le_toReal ha hb).mp (le_of_eq h)
      · rintro rfl; rfl

theorem margin_negative (a b : ℝ≥0∞) : margin a b < 0 ↔ a < b := by
  rw [← not_le, margin_nonneg, not_le]

theorem margin_positive (a b : ℝ≥0∞) : 0 < margin a b ↔ b < a := by
  constructor
  · intro h
    exact lt_of_le_of_ne ((margin_nonneg a b).mp h.le)
      (fun heq => (ne_of_gt h) ((margin_zero a b).mpr heq))
  · intro h
    exact lt_of_le_of_ne ((margin_nonneg a b).mpr h.le)
      (fun heq => (ne_of_lt h) ((margin_zero a b).mp heq.symm))

theorem excess_nonneg (a b : ℝ≥0∞) : 0 ≤ excess a b := le_max_left _ _

theorem excess_zero (a b : ℝ≥0∞) : excess a b = 0 ↔ b ≤ a := by
  simp only [excess, max_eq_left_iff, EReal.neg_le_zero, margin_nonneg]

theorem excess_positive (a b : ℝ≥0∞) : 0 < excess a b ↔ a < b := by
  simp only [excess, lt_max_iff, lt_self_iff_false, false_or, EReal.neg_pos, margin_negative]

variable {I Λ : Type*}
def Valid (d : I → ℝ≥0∞) (e : I → ℝ≥0∞) : Prop := ∀ i, d i ≤ e i
def Saturated (d : I → ℝ≥0∞) (e : I → ℝ≥0∞) : Set I := {i | margin (e i) (d i) = 0}
def Exceeded (d : I → ℝ≥0∞) (e : I → ℝ≥0∞) : Set I := {i | 0 < excess (e i) (d i)}
def Robust (d : I → ℝ≥0∞) (e : I → ℝ≥0∞) : Prop := Valid d e ∧ ∀ i, 0 < margin (e i) (d i)

theorem validity_characterizations (d e : I → ℝ≥0∞) :
    (Valid d e ↔ ∀ i, 0 ≤ margin (e i) (d i)) ∧
    (Valid d e ↔ ∀ i, excess (e i) (d i) = 0) ∧
    (Valid d e ↔ Exceeded d e = ∅) := by
  simp [Valid, Exceeded, margin_nonneg, excess_zero, excess_positive, Set.eq_empty_iff_forall_notMem]

theorem saturation_excess_disjoint (d e : I → ℝ≥0∞) :
    Disjoint (Saturated d e) (Exceeded d e) := by
  rw [Set.disjoint_left]
  intro i hs he
  have h := (margin_zero _ _).mp hs
  have hlt := (excess_positive _ _).mp he
  exact (ne_of_lt hlt) h.symm

theorem valid_not_robust (d e : I → ℝ≥0∞) :
    (Valid d e ∧ ¬ Robust d e) ↔ (Saturated d e ≠ ∅ ∧ Exceeded d e = ∅) := by
  classical
  have hz : Saturated d e ≠ ∅ ↔ ∃ i, d i = e i := by
    simp [Saturated, margin_zero, Set.eq_empty_iff_forall_notMem]
  rw [hz, ← (validity_characterizations d e).2.2]
  constructor
  · rintro ⟨hv,hr⟩
    have hn : ¬ ∀ i, d i < e i := by
      intro h; exact hr ⟨hv,fun i => (margin_positive _ _).mpr (h i)⟩
    obtain ⟨i,hi⟩ := not_forall.mp hn
    exact ⟨⟨i,le_antisymm (hv i) (not_lt.mp hi)⟩,hv⟩
  · rintro ⟨⟨i,hi⟩,hv⟩
    refine ⟨hv,fun hr => ?_⟩
    have hlt := (margin_positive _ _).mp (hr.2 i)
    exact (ne_of_lt hlt) hi

theorem subset_saturation (d e : I → ℝ≥0∞) (A : Set I) :
    A ⊆ Saturated d e ↔ ∀ i ∈ A, d i = e i := by
  simp [Set.subset_def, Saturated, margin_zero]

theorem subset_excess (d e : I → ℝ≥0∞) (A : Set I) :
    A ⊆ Exceeded d e ↔ ∀ i ∈ A, e i < d i := by
  simp [Set.subset_def, Exceeded, excess_positive]

def Initial [Preorder Λ] (A : Set Λ) : Prop := ∀ ⦃x y⦄, x ≤ y → y ∈ A → x ∈ A
def InitialFamily [Preorder Λ] (V : Set Λ) : Set (Set Λ) := {A | A ⊆ V ∧ Initial A}
def MaximalInitial [Preorder Λ] (V : Set Λ) : Set Λ := ⋃₀ (InitialFamily V)

theorem maximal_initial_greatest [Preorder Λ] (V : Set Λ) :
    MaximalInitial V ∈ InitialFamily V ∧ ∀ A ∈ InitialFamily V, A ⊆ MaximalInitial V := by
  constructor
  · constructor
    · rintro x ⟨A,hA,hx⟩; exact hA.1 hx
    · intro x y hxy hy
      obtain ⟨A,hA,hy⟩ := hy
      exact ⟨A,hA,hA.2 hxy hy⟩
  · intro A hA x hx; exact ⟨A,hA,hx⟩

theorem maximal_initial_eq [Preorder Λ] (V : Set Λ) (h : Initial V) :
    MaximalInitial V = V := by
  apply Set.Subset.antisymm (maximal_initial_greatest V).1.1
  exact (maximal_initial_greatest V).2 V ⟨Set.Subset.rfl,h⟩

theorem monotone_defects_initial [Preorder Λ] (d : Λ → I → ℝ≥0∞) (e : I → ℝ≥0∞)
    (hd : ∀ i, Monotone (fun x => d x i)) : Initial {x | Valid (d x) e} := by
  intro x y hxy hy i
  exact le_trans (hd i hxy) (hy i)

theorem initial_boundary [LinearOrder Λ] (V : Set Λ) (hv : Initial V) (b : Λ)
    (hb : IsLeast Vᶜ b) : V = Iio b := by
  ext x
  constructor
  · intro hx
    by_contra hn
    exact hb.1 (hv (not_lt.mp hn) hx)
  · intro hx
    by_contra hn
    exact (not_le.mpr hx) (hb.2 hn)

theorem least_subset [Preorder Λ] (S T : Set Λ) (hs : S ⊆ T) (a b : Λ)
    (ha : IsLeast S a) (hb : IsLeast T b) : b ≤ a := hb.2 (hs ha.1)

theorem maximal_effective_interval [LinearOrder Λ] (d : Λ → I → ℝ≥0∞) (e : I → ℝ≥0∞)
    (hd : ∀ i, Monotone (fun x => d x i)) :
    MaximalInitial {x | Valid (d x) e} = {x | Valid (d x) e} :=
  maximal_initial_eq _ (monotone_defects_initial d e hd)

theorem first_excess [LinearOrder Λ] (d : Λ → I → ℝ≥0∞) (e : I → ℝ≥0∞)
    (hd : ∀ i, Monotone (fun x => d x i)) (b : Λ)
    (hb : IsLeast {x | ¬ Valid (d x) e} b) :
    MaximalInitial {x | Valid (d x) e} = Iio b ∧
    Exceeded (d b) e ≠ ∅ ∧ (∀ x, x < b → Exceeded (d x) e = ∅) := by
  have hi := initial_boundary {x | Valid (d x) e} (monotone_defects_initial d e hd) b hb
  refine ⟨(maximal_effective_interval d e hd).trans hi,?_,?_⟩
  · exact fun he => hb.1 ((validity_characterizations (d b) e).2.2.mpr he)
  · intro x hx
    apply (validity_characterizations (d x) e).2.2.mp
    change x ∈ {x | Valid (d x) e}
    rw [hi]; exact hx

theorem maximum_has_no_excess [Preorder Λ] (d : Λ → I → ℝ≥0∞) (e : I → ℝ≥0∞)
    (a : Λ) (ha : IsGreatest (MaximalInitial {x | Valid (d x) e}) a) :
    Exceeded (d a) e = ∅ :=
  (validity_characterizations (d a) e).2.2.mp ((maximal_initial_greatest _).1.1 ha.1)

theorem infinite_saturation_control : margin ⊤ ⊤ = 0 ∧ excess ⊤ ⊤ = 0 := by
  simp [margin,excess]

theorem no_least_open_excess_control : ¬ ∃ b : ℝ, IsLeast {x | 0 < x} b := by
  rintro ⟨b,hb⟩
  obtain ⟨x,hx,hxb⟩ := exists_between (show (0:ℝ) < b from hb.1)
  exact (not_le_of_gt hxb) (hb.2 hx)

theorem first_excess_is_least [LinearOrder Λ] (d : Λ → I → ℝ≥0∞) (e : I → ℝ≥0∞)
    (b : Λ) (hb : IsLeast {x | ¬ Valid (d x) e} b) :
    IsLeast {x | Exceeded (d x) e ≠ ∅} b := by
  have he : {x | Exceeded (d x) e ≠ ∅} = {x | ¬ Valid (d x) e} := by
    ext x; simp only [Set.mem_ofPred_eq, (validity_characterizations (d x) e).2.2]
  rw [he]; exact hb

end LCTR.CoreContinuumBoundary
