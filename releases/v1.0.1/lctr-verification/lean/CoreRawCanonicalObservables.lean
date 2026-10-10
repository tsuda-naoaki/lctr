import CoreObservableInterfaces

namespace LCTR.CoreRawCanonicalObservables
set_option autoImplicit false
open LCTR.CoreTrajectoryDescent LCTR.CoreNativeObservables LCTR.CoreObservableInterfaces
universe u v w
variable {C : Type u} {D : Type v} {B : Type w}
variable {U L QI V : Type} {Arr : U → Type}
variable (r : C → D → B → Prop) (bind : C × D × B → C × D × B → Prop)

noncomputable def canonical (a : LocalDatum B U L QI V Arr) (h : Descends r bind a) :
    QI × Q (genB r bind) → V := Classical.choose (raw_factor_exists_unique r bind a h)
noncomputable def valueRange (a : LocalDatum B U L QI V Arr) (h : Descends r bind a)
    (q : QI) : Set V := canonicalRange a h.1 q

theorem range_representative_independence (a : LocalDatum B U L QI V Arr)
    (h : Descends r bind a) (q : QI) (l : L) (hl : a.index l = q) :
    a.range l = valueRange r bind a h q :=
  h.2.1 l (Classical.choose (h.1 q)) (hl.trans (Classical.choose_spec (h.1 q)).symm)
theorem canonical_representative_value (a : LocalDatum B U L QI V Arr)
    (h : Descends r bind a) (q : QI) (s : Q (genB r bind)) (i : U) (l : L) (x : Arr i)
    (hi : a.index l = q) (hs : state r bind a i x = s) :
    canonical r bind a h (q,s) = common a i l x := by
  have commutes := (Classical.choose_spec (raw_factor_exists_unique r bind a h)).1 ⟨i,l,x⟩
  change common a i l x = canonical r bind a h (a.index l,state r bind a i x) at commutes
  rw [hi,hs] at commutes
  exact commutes.symm
theorem canonical_value_typed (a : LocalDatum B U L QI V Arr)
    (h : Descends r bind a) (q : QI) (s : Q (genB r bind)) :
    canonical r bind a h (q,s) ∈ valueRange r bind a h q := by
  obtain ⟨i,l,x,hi,hs⟩ := h.2.2.1 q s
  rw [canonical_representative_value r bind a h q s i l x hi hs,
    ← range_representative_independence r bind a h q l hi]
  exact common_value_typed a i l x
noncomputable def typedObservable (a : LocalDatum B U L QI V Arr)
    (h : Descends r bind a) (q : QI) : Q (genB r bind) → valueRange r bind a h q :=
  fun s => ⟨canonical r bind a h (q,s),canonical_value_typed r bind a h q s⟩
theorem canonical_unique (a : LocalDatum B U L QI V Arr)
    (h : Descends r bind a) (g : QI × Q (genB r bind) → V)
    (commutes : ∀ i l (x : Arr i), g (a.index l,state r bind a i x) = common a i l x) :
    g = canonical r bind a h := by
  apply (Classical.choose_spec (raw_factor_exists_unique r bind a h)).2
  intro x
  exact (commutes x.1 x.2.1 x.2.2).symm
theorem local_change_compatibility (a : LocalDatum B U L QI V Arr)
    (h : Descends r bind a) (hc : ChangeCommutes a) (i j : U) (l : L)
    (x : {x // x ∈ changedDomain a i j l}) :
    (typedObservable r bind a h (a.index l) (state r bind a i x.val)).val = changed a i j l x :=
  (canonical_representative_value r bind a h (a.index l) (state r bind a i x.val) i l x.val rfl rfl).trans
    ((change_commutes_iff a).mp hc i j l x).symm
theorem whole_family_representation (a : LocalDatum B U L QI V Arr)
    (h : Descends r bind a) :
    (∀ q l, a.index l = q → a.range l = valueRange r bind a h q) ∧
    (∀ i l (x : Arr i),
      (typedObservable r bind a h (a.index l) (state r bind a i x)).val = common a i l x) := by
  refine ⟨?_,?_⟩
  · exact range_representative_independence r bind a h
  · intro i l x
    exact canonical_representative_value r bind a h (a.index l) (state r bind a i x) i l x rfl rfl

end LCTR.CoreRawCanonicalObservables
