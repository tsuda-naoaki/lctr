import CoreIndexedNativeDeletion
import CorePureWordDisplays

namespace LCTR.CoreFiniteMixedReduction
open LCTR.CoreSourceLoops LCTR.CoreNativeWordFamilies LCTR.CoreSourceMatch
universe u v w
set_option autoImplicit false
variable {U : Type u} {S : Type v} {V : U → Type w}
variable {d : Data U S V} {i j : U}

theorem deletion_preserves_transport_count {p q : Path d i j} (h : Delete d p q) :
    transportCount q=transportCount p := by
  cases h with
  | segment a mid c hs positive =>
    have zero := (source_only_iff mid).mp hs
    simp only [(append_counts _ _).2,zero,Nat.add_zero]

theorem reduction_preserves_transport_count {p q : Path d i j} (h : Reduction d p q) :
    transportCount q=transportCount p := by
  induction h with
  | refl => rfl
  | step del red ih => exact ih.trans (deletion_preserves_transport_count del)

theorem terminal_classification {p q : Path d i j} (hm : Mixed p)
    (hr : Reduction d p q) (hi : Irreducible q) :
    (Mixed q ∧ Irreducible q) ∨ ∃ t : TransportWord d i j, t.val=q := by
  have positive : 0<transportCount q := by
    rw [reduction_preserves_transport_count hr]
    exact hm.2
  by_cases hs : sourceCount q=0
  · exact Or.inr ⟨⟨q,(transport_only_iff q).mpr hs⟩,rfl⟩
  · exact Or.inl ⟨⟨Nat.pos_of_ne_zero hs,positive⟩,hi⟩

def Trace (p q : Path d i j) (N : Nat) (f : Nat → Path d i j) : Prop :=
  f 0=p ∧ f N=q ∧
  (∀ n, n<N → Delete d (f n) (f (n+1))) ∧
  (∀ n, n≤N → Reduction d p (f n))

theorem reduction_trace {p q : Path d i j} (h : Reduction d p q) :
    ∃ N f, Trace p q N f := by
  induction h with
  | refl p =>
    refine ⟨0,fun _ => p,rfl,rfl,?_,?_⟩
    · intro n hn
      omega
    · intro n hn
      exact .refl p
  | @step p q r del red ih =>
    obtain ⟨N,f,h0,hN,steps,reach⟩ := ih
    let g : Nat → Path d i j := fun n => match n with | 0 => p | n+1 => f n
    refine ⟨N+1,g,rfl,hN,?_,?_⟩
    · intro n hn
      cases n with
      | zero => simpa only [g,h0] using del
      | succ n => exact steps n (by omega)
    · intro n hn
      cases n with
      | zero => exact .refl p
      | succ n => exact .step del (reach n (by omega))

theorem trace_domain_extension {p q : Path d i j} {N : Nat} {f : Nat → Path d i j}
    (h : Trace p q N f) (n : Nat) (hn : n≤N) (a : ImageAt d.arrival i) :
    p.domain a → (f n).domain a := by
  rintro ⟨b,hb⟩
  exact ⟨b,reduction_extends_action d (h.2.2.2 n hn) a b hb⟩

theorem trace_exact_on_old_domain {p q : Path d i j} {N : Nat} {f : Nat → Path d i j}
    (h : Trace p q N f) (n : Nat) (hn : n≤N) (a : ImageAt d.arrival i)
    (ha : p.domain a) (b : ImageAt d.arrival j) :
    (f n).action a b ↔ p.action a b :=
  reduction_exact_on_old_domain d (h.2.2.2 n hn) a ha b

theorem mixed_reduction_trace (p : Path d i i) (hm : Mixed p) :
    ∃ N f, Trace p (f N) N f ∧
      ((Mixed (f N) ∧ Irreducible (f N)) ∨
        ∃ t : TransportWord d i i, t.val=f N) := by
  obtain ⟨q,hr,hi⟩ := finite_source_reduction d p
  obtain ⟨N,f,h⟩ := reduction_trace hr
  refine ⟨N,f,?_,?_⟩
  · simpa only [h.2.1] using h
  · simpa only [h.2.1] using terminal_classification hm hr hi

theorem terminal_transport_display (t : TransportWord d i i) :
    (CorePureWordDisplays.directions t.val).map CorePureWordDisplays.transportKind =
      (CoreWordEncoding.decode t.val).kinds ∧
    (CorePureWordDisplays.transportDisplay t).2.1.length=length t.val+1 ∧
    (CorePureWordDisplays.transportDisplay t).2.2.length=length t.val :=
  ⟨CorePureWordDisplays.transport_kinds_recovered t.val t.property,
    CorePureWordDisplays.native_position_length t.val,CorePureWordDisplays.direction_length t.val⟩

theorem mixed_indexed_trace (p : Path d i i) (hm : Mixed p) :
    ∃ N, ∃ f : Nat → Path d i i,
      f 0=p ∧
      (∀ n, n<N → CoreIndexedDeletion.IndexedDelete Kind.src i
        (CoreIndexedNativeDeletion.view (f n)) (CoreIndexedNativeDeletion.view (f (n+1)))) ∧
      ((Mixed (f N) ∧ ¬∃ es, CoreIndexedDeletion.IndexedDelete Kind.src i
        (CoreIndexedNativeDeletion.view (f N)) es) ∨ ∃ t : TransportWord d i i, t.val=f N) ∧
      (∀ n, n≤N → ∀ a : ImageAt d.arrival i, p.domain a →
        (f n).domain a ∧ ∀ b : ImageAt d.arrival i, ((f n).action a b ↔ p.action a b)) := by
  obtain ⟨N,f,h,terminal⟩ := mixed_reduction_trace p hm
  refine ⟨N,f,h.1,?_,?_,?_⟩
  · intro n hn
    exact (CoreIndexedNativeDeletion.native_delete_iff _ _).mp (h.2.2.1 n hn)
  · rcases terminal with ⟨mix,irr⟩|pure
    · exact Or.inl ⟨mix,(CoreIndexedNativeDeletion.irreducible_iff_no_indexed _).mp irr⟩
    · exact Or.inr pure
  · intro n hn a ha
    exact ⟨trace_domain_extension h n hn a ha,fun b => trace_exact_on_old_domain h n hn a ha b⟩

end LCTR.CoreFiniteMixedReduction
