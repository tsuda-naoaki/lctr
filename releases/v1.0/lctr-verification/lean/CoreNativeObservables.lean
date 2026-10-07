import CoreNativeCurves

namespace LCTR.CoreNativeObservables
set_option autoImplicit false
open LCTR.CoreTrajectoryDescent LCTR.CoreObserverTime LCTR.CoreNativeCurves
universe u v w
variable {C : Type u} {D : Type v} {B : Type w}
variable {U L Q V : Type} {Arr : U → Type}

structure LocalDatum (B : Type w) (U L Q V : Type) (Arr : U → Type) where
  index : L → Q
  record : (i : U) → Arr i → B
  localVal : U → L → Type
  localObs : (i : U) → (l : L) → Arr i → localVal i l
  range : L → Set V
  compare : (i : U) → (l : L) → localVal i l → V
  compareTyped : ∀ i l x, compare i l x ∈ range l
  changeDom : (i j : U) → (l : L) → Set (localVal i l)
  change : (i j : U) → (l : L) → {x // x ∈ changeDom i j l} → localVal j l

abbrev Sample := (i : U) × (L × Arr i)
def localState (d : Input C D B) (a : LocalDatum B U L Q V Arr) (i : U) (x : Arr i) : State d :=
  prj (genB d.relation d.binding) (a.record i x)
def projection (d : Input C D B) (a : LocalDatum B U L Q V Arr) (x : Sample (L := L) (Arr := Arr)) :
    Q × State d := (a.index x.2.1, localState d a x.1 x.2.2)
def comparison (a : LocalDatum B U L Q V Arr) (x : Sample (L := L) (Arr := Arr)) : V :=
  a.compare x.1 x.2.1 (a.localObs x.1 x.2.1 x.2.2)

structure Descent (d : Input C D B) (a : LocalDatum B U L Q V Arr) : Prop where
  indexSurj : Function.Surjective a.index
  rangeKernel : ∀ l k, a.index l = a.index k → a.range l = a.range k
  coverage : ∀ q s, ∃ i l, ∃ x : Arr i, a.index l = q ∧ localState d a i x = s
  valueKernel : ∀ i j l k (x : Arr i) (y : Arr j),
    a.index l = a.index k → localState d a i x = localState d a j y →
    a.compare i l (a.localObs i l x) = a.compare j k (a.localObs j k y)

theorem actual_projection_surjective (d : Input C D B) (a : LocalDatum B U L Q V Arr)
    (h : Descent d a) : Function.Surjective (projection d a) := by
  rintro ⟨q,s⟩
  obtain ⟨i,l,x,hi,hs⟩ := h.coverage q s
  exact ⟨⟨i,l,x⟩, Prod.ext hi hs⟩

theorem actual_comparison_fiber_invariant (d : Input C D B) (a : LocalDatum B U L Q V Arr)
    (h : Descent d a) (x y : Sample (L := L) (Arr := Arr))
    (same : projection d a x = projection d a y) : comparison a x = comparison a y := by
  exact h.valueKernel x.1 y.1 x.2.1 y.2.1 x.2.2 y.2.2
    (congrArg Prod.fst same) (congrArg Prod.snd same)

theorem native_factor_exists_unique (d : Input C D B) (a : LocalDatum B U L Q V Arr)
    (h : Descent d a) :
    ∃ f : Q × State d → V,
      (∀ x, comparison a x = f (projection d a x)) ∧
      ∀ g, (∀ x, comparison a x = g (projection d a x)) → g = f :=
  LCTR.Trajectory.surjective_fiber_invariant_map_factors_uniquely
    (projection d a) (comparison a) (actual_projection_surjective d a h)
    (actual_comparison_fiber_invariant d a h)

noncomputable def canonical (d : Input C D B) (a : LocalDatum B U L Q V Arr)
    (h : Descent d a) : Q × State d → V := Classical.choose (native_factor_exists_unique d a h)
noncomputable def canonicalRange (a : LocalDatum B U L Q V Arr)
    (surj : Function.Surjective a.index) (q : Q) : Set V := a.range (Classical.choose (surj q))

theorem range_representative_independence (d : Input C D B) (a : LocalDatum B U L Q V Arr)
    (h : Descent d a) (q : Q) (l : L) (hl : a.index l = q) :
    a.range l = canonicalRange a h.indexSurj q :=
  h.rangeKernel l (Classical.choose (h.indexSurj q))
    (hl.trans (Classical.choose_spec (h.indexSurj q)).symm)

theorem canonical_representative_value (d : Input C D B) (a : LocalDatum B U L Q V Arr)
    (h : Descent d a) (q : Q) (s : State d) (i : U) (l : L) (x : Arr i)
    (hi : a.index l = q) (hs : localState d a i x = s) :
    canonical d a h (q,s) = a.compare i l (a.localObs i l x) := by
  have commutes := (Classical.choose_spec (native_factor_exists_unique d a h)).1 ⟨i,l,x⟩
  change a.compare i l (a.localObs i l x) = canonical d a h (a.index l, localState d a i x) at commutes
  rw [hi,hs] at commutes
  exact commutes.symm

theorem canonical_value_typed (d : Input C D B) (a : LocalDatum B U L Q V Arr)
    (h : Descent d a) (q : Q) (s : State d) :
    canonical d a h (q,s) ∈ canonicalRange a h.indexSurj q := by
  obtain ⟨i,l,x,hi,hs⟩ := h.coverage q s
  rw [canonical_representative_value d a h q s i l x hi hs,
    ← range_representative_independence d a h q l hi]
  exact a.compareTyped i l (a.localObs i l x)

noncomputable def typedObservable (d : Input C D B) (a : LocalDatum B U L Q V Arr)
    (h : Descent d a) (q : Q) : State d → canonicalRange a h.indexSurj q :=
  fun s => ⟨canonical d a h (q,s), canonical_value_typed d a h q s⟩

theorem canonical_unique (d : Input C D B) (a : LocalDatum B U L Q V Arr)
    (h : Descent d a) (g : Q × State d → V)
    (commutes : ∀ i l (x : Arr i), g (a.index l, localState d a i x) = a.compare i l (a.localObs i l x)) :
    g = canonical d a h := by
  apply (Classical.choose_spec (native_factor_exists_unique d a h)).2
  intro x
  exact (commutes x.1 x.2.1 x.2.2).symm

def ChangeCommutes (a : LocalDatum B U L Q V Arr) : Prop :=
  ∀ i j l (x : Arr i) (hx : a.localObs i l x ∈ a.changeDom i j l),
    a.compare j l (a.change i j l ⟨a.localObs i l x,hx⟩) = a.compare i l (a.localObs i l x)

theorem local_change_compatibility (d : Input C D B) (a : LocalDatum B U L Q V Arr)
    (h : Descent d a) (hc : ChangeCommutes a) (i j : U) (l : L) (x : Arr i)
    (hx : a.localObs i l x ∈ a.changeDom i j l) :
    (typedObservable d a h (a.index l) (localState d a i x)).val =
      a.compare j l (a.change i j l ⟨a.localObs i l x,hx⟩) :=
  (canonical_representative_value d a h (a.index l) (localState d a i x) i l x rfl rfl).trans
    (hc i j l x hx).symm

theorem native_curve_local_value (d : Input C D B) (a : LocalDatum B U L Q V Arr)
    (h : Descent d a) (inc : IncTrans d) (single : Single d) (fiber : FiberCondition d inc single)
    (rho : RealEmbedding d inc) (t : Domain d) (i : U) (l : L) (x : Arr i)
    (hs : localState d a i x = canonicalTrajectory d single t) :
    (realCurve d inc single fiber rho (typedObservable d a h (a.index l))
      (realEmbedding d inc rho (restrictedProjection d inc t))).val =
      a.compare i l (a.localObs i l x) := by
  have factor := (observable_factorization d inc single fiber rho
    (typedObservable d a h (a.index l))).1 t
  have same := congrArg Subtype.val (factor.1.trans factor.2)
  exact same.symm.trans
    (canonical_representative_value d a h (a.index l) (canonicalTrajectory d single t) i l x rfl hs)

end LCTR.CoreNativeObservables
