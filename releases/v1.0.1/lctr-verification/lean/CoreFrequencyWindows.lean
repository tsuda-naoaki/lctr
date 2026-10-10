import CoreAffineRealization
import CoreAffineFrequency

namespace LCTR.CoreFrequencyWindows
open Set
universe u v w z q p k
set_option autoImplicit false

structure ArrivalData (U : Type u) (J : Type v) (S : Type w)
    (V : U → Type z) (Q : Type q) where
  token : J → Nat → S
  domain : U → Set S
  arrival : ∀ u, {s // s ∈ domain u} → V u
  project : ∀ u, Set.range (arrival u) → Q

structure RawWindow (U : Type u) (J : Type v) where
  position : U
  source : J
  k0 : Nat
  k1 : Nat

variable {U : Type u} {J : Type v} {S : Type w} {V : U → Type z} {Q : Type q}

def endpoint (d : ArrivalData U J S V Q) (u : U) (j : J) (k : Nat)
    (h : d.token j k ∈ d.domain u) : Q :=
  d.project u ⟨d.arrival u ⟨d.token j k,h⟩,⟨⟨d.token j k,h⟩,rfl⟩⟩

theorem endpoint_is_projected_arrival (d : ArrivalData U J S V Q) (u : U) (j : J)
    (k : Nat) (h : d.token j k ∈ d.domain u) :
    ∃ a : Set.range (d.arrival u), a.val = d.arrival u ⟨d.token j k,h⟩ ∧
      endpoint d u j k h = d.project u a :=
  ⟨⟨d.arrival u ⟨d.token j k,h⟩,⟨⟨d.token j k,h⟩,rfl⟩⟩,rfl,rfl⟩

def Admissible (d : ArrivalData U J S V Q) (r : Q → Q → Prop)
    (w : RawWindow U J) : Prop :=
  w.k0 < w.k1 ∧ ∃ h0 : d.token w.source w.k0 ∈ d.domain w.position,
    ∃ h1 : d.token w.source w.k1 ∈ d.domain w.position,
      r (endpoint d w.position w.source w.k0 h0) (endpoint d w.position w.source w.k1 h1)

structure Window (d : ArrivalData U J S V Q) (r : Q → Q → Prop) where
  raw : RawWindow U J
  increasing : raw.k0 < raw.k1
  lower_present : d.token raw.source raw.k0 ∈ d.domain raw.position
  upper_present : d.token raw.source raw.k1 ∈ d.domain raw.position
  ordered : r (endpoint d raw.position raw.source raw.k0 lower_present)
    (endpoint d raw.position raw.source raw.k1 upper_present)

theorem admissibility_iff (d : ArrivalData U J S V Q) (r : Q → Q → Prop)
    (w : RawWindow U J) : Admissible d r w ↔ ∃ x : Window d r, x.raw = w := by
  constructor
  · rintro ⟨h,h0,h1,hr⟩
    exact ⟨⟨w,h,h0,h1,hr⟩,rfl⟩
  · rintro ⟨x,rfl⟩
    exact ⟨x.increasing,x.lower_present,x.upper_present,x.ordered⟩

def toAbstract {d : ArrivalData U J S V Q} {r : Q → Q → Prop}
    (x : Window d r) : LCTR.CoreAffineFrequency.Window Q r where
  k0 := x.raw.k0
  k1 := x.raw.k1
  increasing := x.increasing
  lower := endpoint d x.raw.position x.raw.source x.raw.k0 x.lower_present
  upper := endpoint d x.raw.position x.raw.source x.raw.k1 x.upper_present
  ordered := x.ordered

theorem abstract_window_retains_fields {d : ArrivalData U J S V Q} {r : Q → Q → Prop}
    (x : Window d r) :
    (toAbstract x).k0 = x.raw.k0 ∧ (toAbstract x).k1 = x.raw.k1 ∧
    (toAbstract x).lower = endpoint d x.raw.position x.raw.source x.raw.k0 x.lower_present ∧
    (toAbstract x).upper = endpoint d x.raw.position x.raw.source x.raw.k1 x.upper_present :=
  ⟨rfl,rfl,rfl,rfl⟩

variable {K : Type k} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {P : Type p} {d : ArrivalData U J S V Q} {r : Q → Q → Prop}

def countDifference (x : Window d r) : K := (x.raw.k1-x.raw.k0 : Nat)
def coordinateDifference (A : LCTR.CoreAffineRealization.Data K P) (repr : Q → P)
    (x : Window d r) : K := A.diff (repr (toAbstract x).upper) (repr (toAbstract x).lower)
def frequency (A : LCTR.CoreAffineRealization.Data K P) (repr : Q → P)
    (x : Window d r) : K := countDifference x / coordinateDifference A repr x
def period (A : LCTR.CoreAffineRealization.Data K P) (repr : Q → P)
    (x : Window d r) : K := (frequency A repr x)⁻¹

theorem count_difference_positive (x : Window d r) : 0 < (countDifference x : K) :=
  Nat.cast_pos.mpr (Nat.sub_pos_of_lt x.increasing)

theorem coordinate_difference_positive (A : LCTR.CoreAffineRealization.Data K P)
    (repr : Q → P) (strict : ∀ a b, r a b ↔ A.lt (repr a) (repr b)) (x : Window d r) :
    0 < coordinateDifference A repr x :=
  (A.strict_sign _ _).mp ((strict _ _).mp x.ordered)

theorem frequency_positive (A : LCTR.CoreAffineRealization.Data K P)
    (repr : Q → P) (strict : ∀ a b, r a b ↔ A.lt (repr a) (repr b)) (x : Window d r) :
    0 < frequency A repr x :=
  div_pos (count_difference_positive x) (coordinate_difference_positive A repr strict x)

theorem period_positive_and_product (A : LCTR.CoreAffineRealization.Data K P)
    (repr : Q → P) (strict : ∀ a b, r a b ↔ A.lt (repr a) (repr b)) (x : Window d r) :
    0 < period A repr x ∧ frequency A repr x * period A repr x = 1 :=
  ⟨inv_pos.mpr (frequency_positive A repr strict x),
    mul_inv_cancel₀ (ne_of_gt (frequency_positive A repr strict x))⟩

theorem period_invariance (A : LCTR.CoreAffineRealization.Data K P) (repr : Q → P)
    (x y : Window d r) (h : frequency A repr x = frequency A repr y) :
    period A repr x = period A repr y := congrArg Inv.inv h

def SourceFamily (A : LCTR.CoreAffineRealization.Data K P) (repr : Q → P)
    (j : J) (W : Set (Window d r)) : Prop :=
  W.Nonempty ∧ (∀ x ∈ W, x.raw.source = j) ∧
  (∀ x ∈ W, ∀ y ∈ W, frequency A repr x = frequency A repr y) ∧
  (∀ x ∈ W, ∀ y ∈ W, period A repr x = period A repr y)

theorem source_values_unique (A : LCTR.CoreAffineRealization.Data K P) (repr : Q → P)
    (j : J) (W : Set (Window d r)) (h : SourceFamily A repr j W) :
    ∃! values : K × K, ∀ x ∈ W,
      x.raw.source = j ∧ values = (frequency A repr x, period A repr x) := by
  obtain ⟨x,hx⟩ := h.1
  refine ⟨(frequency A repr x, period A repr x), ?_, ?_⟩
  · intro y hy
    exact ⟨h.2.1 y hy, Prod.ext (h.2.2.1 x hx y hy) (h.2.2.2 x hx y hy)⟩
  · intro values hv
    exact (hv x hx).2

end LCTR.CoreFrequencyWindows
