import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic

namespace LCTR.Chapter03SourceOrderRecovery

universe u v w

abbrev CToken (Source : Type u) := Source × Nat

def cSourceIndex {Source : Type u} (x : CToken Source) : Source := x.1
def cCounter {Source : Type u} (x : CToken Source) : Nat := x.2

theorem ch03_r026_unique_tagged_representation
    {Source : Type u} (x : CToken Source) :
    ∃! p : Source × Nat, p = x := by
  exact ⟨x, rfl, by
    intro y hy
    exact hy⟩

def CWithinLE (k l : Nat) : Prop := k ≤ l

theorem ch03_r029_c_within_source_partial_order :
    (∀ k, CWithinLE k k) ∧
    (∀ a b c, CWithinLE a b → CWithinLE b c → CWithinLE a c) ∧
    (∀ a b, CWithinLE a b → CWithinLE b a → a = b) := by
  constructor
  · intro k
    exact Nat.le_refl k
  constructor
  · intro a b c hab hbc
    exact Nat.le_trans hab hbc
  · intro a b hab hba
    exact Nat.le_antisymm hab hba

theorem ch03_r031_equal_display_does_not_identify_tokens
    {Source : Type u} {Label : Type v}
    (display : CToken Source → Label)
    {j j' : Source} {k l : Nat}
    (hpos : (j, k) ≠ (j', l))
    (_hdisplay : display (j, k) = display (j', l)) :
    (j, k) ≠ (j', l) := by
  exact hpos

structure DToken (Identity : Type u) where
  identity : Identity
  seq : Nat
deriving DecidableEq, Repr

def DLE {Identity : Type u} (x y : DToken Identity) : Prop :=
  x = y ∨ x.seq < y.seq

theorem ch03_r035_d_partial_order
    {Identity : Type u} :
    (∀ x : DToken Identity, DLE x x) ∧
    (∀ x y z : DToken Identity, DLE x y → DLE y z → DLE x z) ∧
    (∀ x y : DToken Identity, DLE x y → DLE y x → x = y) := by
  constructor
  · intro x
    exact Or.inl rfl
  constructor
  · intro x y z hxy hyz
    rcases hxy with hxy | hxy
    · subst y
      exact hyz
    rcases hyz with hyz | hyz
    · subst z
      exact Or.inr hxy
    · exact Or.inr (Nat.lt_trans hxy hyz)
  · intro x y hxy hyx
    rcases hxy with hxy | hxy
    · exact hxy
    rcases hyx with hyx | hyx
    · exact hyx.symm
    · exact False.elim (Nat.lt_asymm hxy hyx)

theorem ch03_r036_d_equal_index_incomparable
    {Identity : Type u} {x y : DToken Identity}
    (hne : x ≠ y) (hseq : x.seq = y.seq) :
    (¬ DLE x y) ∧ (¬ DLE y x) := by
  constructor
  · intro h
    rcases h with hEq | hLt
    · exact hne hEq
    · have hloop : x.seq < x.seq := by
        simpa [hseq] using hLt
      exact (Nat.lt_irrefl _) hloop
  · intro h
    rcases h with hEq | hLt
    · exact hne hEq.symm
    · have hloop : y.seq < y.seq := by
        simpa [hseq] using hLt
      exact (Nat.lt_irrefl _) hloop

def CFamilyLE {Source : Type u} (x y : CToken Source) : Prop :=
  x.1 = y.1 ∧ x.2 ≤ y.2

 
theorem ch03_r029_fixed_source_order_correspondence
    {Source : Type u} (j : Source) (k l : Nat) :
    CFamilyLE (j, k) (j, l) ↔ CWithinLE k l := by
  simp [CFamilyLE, CWithinLE]

theorem ch03_r041_c_family_partial_order
    {Source : Type u} :
    (∀ x : CToken Source, CFamilyLE x x) ∧
    (∀ x y z : CToken Source, CFamilyLE x y → CFamilyLE y z → CFamilyLE x z) ∧
    (∀ x y : CToken Source, CFamilyLE x y → CFamilyLE y x → x = y) := by
  constructor
  · intro x
    exact ⟨rfl, Nat.le_refl _⟩
  constructor
  · intro x y z hxy hyz
    exact ⟨hxy.1.trans hyz.1, Nat.le_trans hxy.2 hyz.2⟩
  · intro x y hxy hyx
    apply Prod.ext
    · exact hxy.1
    · exact Nat.le_antisymm hxy.2 hyx.2

theorem ch03_r042_c_distinct_sources_incomparable
    {Source : Type u} {x y : CToken Source}
    (hdiff : x.1 ≠ y.1) :
    (¬ CFamilyLE x y) ∧ (¬ CFamilyLE y x) := by
  constructor
  · intro h
    exact hdiff h.1
  · intro h
    exact hdiff h.1.symm

def RecordCells (Tok : Type u) [DecidableEq Tok] := Tok → Finset Tok

theorem ch03_r038_record_cells_partition_criterion
    {Tok : Type u} [DecidableEq Tok]
    (W : RecordCells Tok)
    (hnonempty : ∀ x, (W x).Nonempty)
    (hself : ∀ x, x ∈ W x)
    (hclass : ∀ x y, y ∈ W x ↔ W y = W x) :
    (∀ x, x ∈ W x) ∧
    (∀ x, (W x).Nonempty) ∧
    (∀ x y z, z ∈ W x → z ∈ W y → W x = W y) := by
  constructor
  · exact hself
  constructor
  · exact hnonempty
  · intro x y z hzx hzy
    have hx : W z = W x := (hclass x z).mp hzx
    have hy : W z = W y := (hclass y z).mp hzy
    exact hx.symm.trans hy

structure PartialArrival (Tok : Type u) (Arrival : Type v) where
  dom : Set Tok
  val : ∀ x : Tok, x ∈ dom → Arrival

def UniqueRecoverable
    {Tok : Type u} {Arrival : Type v}
    (A : PartialArrival Tok Arrival) (a : Arrival) : Prop :=
  (∃ x : {x : Tok // x ∈ A.dom}, A.val x.1 x.2 = a) ∧
  ∀ x y : {x : Tok // x ∈ A.dom},
    A.val x.1 x.2 = a → A.val y.1 y.2 = a → x = y

theorem ch03_r045_singleton_fiber_recovery
    {Tok : Type u} {Arrival : Type v}
    (A : PartialArrival Tok Arrival) (a : Arrival)
    (h : UniqueRecoverable A a) :
    ∃! x : {x : Tok // x ∈ A.dom}, A.val x.1 x.2 = a := by
  rcases h.1 with ⟨x, hx⟩
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact h.2 y x hy hx

noncomputable def recoverSubtype
    {Tok : Type u} {Arrival : Type v}
    (A : PartialArrival Tok Arrival) (a : Arrival)
    (h : UniqueRecoverable A a) :
    {x : Tok // x ∈ A.dom} :=
  Classical.choose h.1

theorem recoverSubtype_spec
    {Tok : Type u} {Arrival : Type v}
    (A : PartialArrival Tok Arrival) (a : Arrival)
    (h : UniqueRecoverable A a) :
    A.val (recoverSubtype A a h).1 (recoverSubtype A a h).2 = a := by
  exact Classical.choose_spec h.1

 
theorem ch03_r045_fiber_eq_singleton_recovery
    {Tok : Type u} {Arrival : Type v}
    (A : PartialArrival Tok Arrival) (a : Arrival)
    (h : UniqueRecoverable A a) :
    {x : {x : Tok // x ∈ A.dom} | A.val x.1 x.2 = a} =
      ({recoverSubtype A a h} : Set {x : Tok // x ∈ A.dom}) := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    have heq : x = recoverSubtype A a h :=
      h.2 x (recoverSubtype A a h) hx (recoverSubtype_spec A a h)
    simpa [heq]
  · intro hx
    have heq : x = recoverSubtype A a h := by
      simpa using hx
    subst x
    exact recoverSubtype_spec A a h

theorem recover_eq_original
    {Tok : Type u} {Arrival : Type v}
    (A : PartialArrival Tok Arrival)
    (x : Tok) (hx : x ∈ A.dom)
    (h : UniqueRecoverable A (A.val x hx)) :
    (recoverSubtype A (A.val x hx) h).1 = x := by
  have hrec :
      A.val (recoverSubtype A (A.val x hx) h).1
        (recoverSubtype A (A.val x hx) h).2 = A.val x hx :=
    recoverSubtype_spec A (A.val x hx) h
  have hs :
      recoverSubtype A (A.val x hx) h = (⟨x, hx⟩ : {x : Tok // x ∈ A.dom}) :=
    h.2 _ _ hrec rfl
  exact congrArg Subtype.val hs

theorem ch03_r046_c_recovery_preserves_source_index
    {Source : Type u} {Arrival : Type v}
    (A : PartialArrival (CToken Source) Arrival)
    (x : CToken Source) (hx : x ∈ A.dom)
    (h : UniqueRecoverable A (A.val x hx)) :
    cSourceIndex (recoverSubtype A (A.val x hx) h).1 = cSourceIndex x := by
  exact congrArg Prod.fst (recover_eq_original A x hx h)

structure BToken (Position : Type u) (Payload : Type v) where
  objectPos : Position
  payload : Payload

theorem ch03_r046_b_recovery_preserves_object_position
    {Position : Type u} {Payload : Type v} {Arrival : Type w}
    (A : PartialArrival (BToken Position Payload) Arrival)
    (x : BToken Position Payload) (hx : x ∈ A.dom)
    (h : UniqueRecoverable A (A.val x hx)) :
    (recoverSubtype A (A.val x hx) h).1.objectPos = x.objectPos := by
  exact congrArg (fun t => t.objectPos) (recover_eq_original A x hx h)

end LCTR.Chapter03SourceOrderRecovery
