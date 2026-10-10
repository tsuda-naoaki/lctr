import CoreNativeObservables

namespace LCTR.CoreObservableInterfaces
set_option autoImplicit false
open LCTR.CoreTrajectoryDescent LCTR.CoreNativeObservables
universe u v w
variable {C : Type u} {D : Type v} {B : Type w}
variable {U L QI V : Type} {Arr : U → Type}

def common (a : LocalDatum B U L QI V Arr) (i : U) (l : L) (x : Arr i) : V :=
  a.compare i l (a.localObs i l x)
def changedDomain (a : LocalDatum B U L QI V Arr) (i j : U) (l : L) : Set (Arr i) :=
  {x | a.localObs i l x ∈ a.changeDom i j l}
def changed (a : LocalDatum B U L QI V Arr) (i j : U) (l : L)
    (x : {x // x ∈ changedDomain a i j l}) : V :=
  a.compare j l (a.change i j l ⟨a.localObs i l x.val, x.property⟩)

variable (r : C → D → B → Prop) (bind : C × D × B → C × D × B → Prop)
def state (a : LocalDatum B U L QI V Arr) (i : U) (x : Arr i) : Q (genB r bind) :=
  prj (genB r bind) (a.record i x)
def Descends (a : LocalDatum B U L QI V Arr) : Prop :=
  Function.Surjective a.index ∧
  (∀ l k, a.index l = a.index k → a.range l = a.range k) ∧
  (∀ q s, ∃ i l, ∃ x : Arr i, a.index l = q ∧ state r bind a i x = s) ∧
  (∀ i j l k (x : Arr i) (y : Arr j), a.index l = a.index k →
    state r bind a i x = state r bind a j y → common a i l x = common a j k y)

theorem trajectory_single_domain_iff {T S : Type u} (rel : T → S → Prop) :
    (∀ t, (∃ s, rel t s) → ∀ s₀ s₁, rel t s₀ → rel t s₁ → s₀ = s₁) ↔
    (∀ t s₀ s₁, rel t s₀ → rel t s₁ → s₀ = s₁) := by
  constructor
  · intro h t s₀ s₁ h₀ h₁
    exact h t ⟨s₀,h₀⟩ s₀ s₁ h₀ h₁
  · intro h t _ s₀ s₁ h₀ h₁
    exact h t s₀ s₁ h₀ h₁

theorem common_value_formula (a : LocalDatum B U L QI V Arr) (i : U) (l : L) :
    common a i l = a.compare i l ∘ a.localObs i l := rfl
theorem common_value_typed (a : LocalDatum B U L QI V Arr) (i : U) (l : L) (x : Arr i) :
    common a i l x ∈ a.range l := a.compareTyped i l (a.localObs i l x)
theorem changed_domain_iff (a : LocalDatum B U L QI V Arr) (i j : U) (l : L) (x : Arr i) :
    x ∈ changedDomain a i j l ↔ a.localObs i l x ∈ a.changeDom i j l := Iff.rfl
theorem changed_value_formula (a : LocalDatum B U L QI V Arr) (i j : U) (l : L)
    (x : {x // x ∈ changedDomain a i j l}) :
    changed a i j l x = a.compare j l (a.change i j l ⟨a.localObs i l x.val,x.property⟩) := rfl
theorem changed_value_typed (a : LocalDatum B U L QI V Arr) (i j : U) (l : L)
    (x : {x // x ∈ changedDomain a i j l}) : changed a i j l x ∈ a.range l :=
  a.compareTyped j l (a.change i j l ⟨a.localObs i l x.val,x.property⟩)
theorem local_state_formula (a : LocalDatum B U L QI V Arr) (i : U) :
    state r bind a i = prj (genB r bind) ∘ a.record i := rfl
theorem local_state_kernel (a : LocalDatum B U L QI V Arr) (i j : U) (x : Arr i) (y : Arr j) :
    state r bind a i x = state r bind a j y ↔
      Relation.EqvGen (genB r bind) (a.record i x) (a.record j y) := by
  change Quotient.mk (Relation.EqvGen.setoid (genB r bind)) (a.record i x) =
    Quotient.mk (Relation.EqvGen.setoid (genB r bind)) (a.record j y) ↔ _
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound (s := Relation.EqvGen.setoid (genB r bind)) h
theorem descent_conditions_iff (a : LocalDatum B U L QI V Arr) :
    Descends r bind a ↔
    Function.Surjective a.index ∧
    (∀ l k, a.index l = a.index k → a.range l = a.range k) ∧
    (∀ q s, ∃ i l, ∃ x : Arr i, a.index l = q ∧ state r bind a i x = s) ∧
    (∀ i j l k (x : Arr i) (y : Arr j), a.index l = a.index k →
      state r bind a i x = state r bind a j y → common a i l x = common a j k y) := Iff.rfl
theorem change_commutes_iff (a : LocalDatum B U L QI V Arr) :
    ChangeCommutes a ↔ ∀ i j l (x : {x // x ∈ changedDomain a i j l}),
      changed a i j l x = common a i l x.val := by
  constructor
  · intro h i j l x
    exact h i j l x.val x.property
  · intro h i j l x hx
    exact h i j l ⟨x,hx⟩

def sampleProjection (a : LocalDatum B U L QI V Arr)
    (x : Sample (L := L) (Arr := Arr)) : QI × Q (genB r bind) :=
  (a.index x.2.1, state r bind a x.1 x.2.2)
theorem raw_projection_surjective (a : LocalDatum B U L QI V Arr) (h : Descends r bind a) :
    Function.Surjective (sampleProjection r bind a) := by
  rintro ⟨q,s⟩
  obtain ⟨i,l,x,hi,hs⟩ := h.2.2.1 q s
  exact ⟨⟨i,l,x⟩,Prod.ext hi hs⟩
theorem raw_comparison_fiber_invariant (a : LocalDatum B U L QI V Arr)
    (h : Descends r bind a) (x y : Sample (L := L) (Arr := Arr))
    (same : sampleProjection r bind a x = sampleProjection r bind a y) : comparison a x = comparison a y :=
  h.2.2.2 x.1 y.1 x.2.1 y.2.1 x.2.2 y.2.2 (congrArg Prod.fst same) (congrArg Prod.snd same)
theorem raw_factor_exists_unique (a : LocalDatum B U L QI V Arr) (h : Descends r bind a) :
    ∃ f : QI × Q (genB r bind) → V,
      (∀ x, comparison a x = f (sampleProjection r bind a x)) ∧
      ∀ g, (∀ x, comparison a x = g (sampleProjection r bind a x)) → g = f :=
  LCTR.Trajectory.surjective_fiber_invariant_map_factors_uniquely
    (sampleProjection r bind a) (comparison a) (raw_projection_surjective r bind a h)
    (raw_comparison_fiber_invariant r bind a h)

end LCTR.CoreObservableInterfaces
