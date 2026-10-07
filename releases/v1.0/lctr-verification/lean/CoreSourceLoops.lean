import CoreComparisonIntegration

namespace LCTR.CoreSourceLoops
open LCTR.Chapter03SourceOrderRecovery LCTR.CoreSourceMatch LCTR.CoreComparisonIntegration
universe u v w
set_option autoImplicit false

structure Data (U : Type u) (S : Type v) (V : U → Type w) where
  arrival : ∀ i, PartialArrival S (V i)
  unique : L1 arrival
  transport : ∀ i j, ImageAt arrival i → ImageAt arrival j → Prop
  admissible : U → U → Prop
  transportInjective : TransportPartialInjection arrival transport admissible

variable {U : Type u} {S : Type v} {V : U → Type w}

noncomputable def system (d : Data U S V) :=
  comparisonSystem d.arrival d.unique d.transport d.admissible d.transportInjective

abbrev Path (d : Data U S V) := LCTR.CoreTypedWords.Word (system d)

def length {d : Data U S V} {i j : U} : Path d i j → Nat
  | .nil _ => 0
  | .cons _ tail => 1 + length tail

def SourceOnly {d : Data U S V} {i j : U} : Path d i j → Prop
  | .nil _ => True
  | .cons e tail => e.val = .src ∧ SourceOnly tail

def TransportOnly {d : Data U S V} {i j : U} : Path d i j → Prop
  | .nil _ => True
  | .cons e tail => e.val ≠ .src ∧ TransportOnly tail

theorem append_length {d : Data U S V} {i j k : U} (p : Path d i j) (q : Path d j k) :
    length (p.append q) = length p + length q := by
  induction p with
  | nil => simp [LCTR.CoreTypedWords.Word.append,length]
  | cons e tail ih => simp [LCTR.CoreTypedWords.Word.append,length,ih,Nat.add_assoc]

theorem source_path_preserves_recovery (d : Data U S V) {i j : U} (p : Path d i j)
    (hs : SourceOnly p) (a : ImageAt d.arrival i) (b : ImageAt d.arrival j)
    (act : p.action a b) :
    (localRecovery d.arrival d.unique i a).val = (localRecovery d.arrival d.unique j b).val := by
  induction p with
  | nil => exact congrArg (fun x => (localRecovery d.arrival d.unique _ x).val) act
  | @cons i j k e tail ih =>
    obtain ⟨c,edge,rest⟩ := act
    change Atom d.arrival d.unique d.transport e.val i j a c at edge
    rw [hs.1] at edge
    exact ((srcGraph_iff_same_recovery d.arrival d.unique i j a c).mp edge).trans
      (ih hs.2 c b rest)

theorem source_loop_identity (d : Data U S V) (i : U) (p : Path d i i)
    (hs : SourceOnly p) (a b : ImageAt d.arrival i) (act : p.action a b) : a = b :=
  recovery_injective d.arrival d.unique i (source_path_preserves_recovery d p hs a b act)

theorem delete_source_loop_action (d : Data U S V) {i j k : U}
    (p : Path d i j) (loop : Path d j j) (q : Path d j k) (hs : SourceOnly loop)
    (a : ImageAt d.arrival i) (b : ImageAt d.arrival k)
    (act : ((p.append loop).append q).action a b) : (p.append q).action a b := by
  obtain ⟨c,left,right⟩ := (LCTR.CoreTypedWords.append_action (p.append loop) q a b).mp act
  obtain ⟨x,hp,hl⟩ := (LCTR.CoreTypedWords.append_action p loop a c).mp left
  have eq := source_loop_identity d j loop hs x c hl
  subst c
  exact (LCTR.CoreTypedWords.append_action p q a b).mpr ⟨x,hp,right⟩

inductive Delete (d : Data U S V) {i k : U} : Path d i k → Path d i k → Prop
  | segment {j : U} (p : Path d i j) (loop : Path d j j) (q : Path d j k)
      (source : SourceOnly loop) (nonempty : 0 < length loop) :
      Delete d ((p.append loop).append q) (p.append q)

theorem deletion_strictly_shortens (d : Data U S V) {i k : U} {p q : Path d i k}
    (h : Delete d p q) : length q < length p := by
  cases h with
  | segment p loop q hs hn => simp only [append_length]; omega

theorem deletion_extends_action (d : Data U S V) {i k : U} {p q : Path d i k}
    (h : Delete d p q) (a : ImageAt d.arrival i) (b : ImageAt d.arrival k) :
    p.action a b → q.action a b := by
  cases h with
  | segment p loop q hs hn => exact delete_source_loop_action d p loop q hs a b

theorem deletion_extends_domain (d : Data U S V) {i k : U} {p q : Path d i k}
    (h : Delete d p q) (a : ImageAt d.arrival i) : p.domain a → q.domain a := by
  rintro ⟨b,hab⟩
  exact ⟨b,deletion_extends_action d h a b hab⟩

theorem deletion_exact_on_old_domain (d : Data U S V) {i k : U} {p q : Path d i k}
    (h : Delete d p q) (a : ImageAt d.arrival i) (ha : p.domain a) (b : ImageAt d.arrival k) :
    q.action a b ↔ p.action a b := by
  constructor
  · intro hq
    obtain ⟨c,hc⟩ := ha
    have e := LCTR.CoreTypedWords.action_functional q a c b (deletion_extends_action d h a c hc) hq
    exact e ▸ hc
  · exact deletion_extends_action d h a b

inductive Reduction (d : Data U S V) {i k : U} : Path d i k → Path d i k → Prop
  | refl (p) : Reduction d p p
  | step {p q r} : Delete d p q → Reduction d q r → Reduction d p r

def Irreducible {d : Data U S V} {i k : U} (p : Path d i k) : Prop :=
  ¬ ∃ q, Delete d p q

theorem finite_source_reduction (d : Data U S V) {i k : U} (p : Path d i k) :
    ∃ q, Reduction d p q ∧ Irreducible q := by
  classical
  generalize hn : length p = n
  induction n using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases irreducible : Irreducible p
    · exact ⟨p,.refl p,irreducible⟩
    · obtain ⟨q,hq⟩ : ∃ q, Delete d p q := by simpa [Irreducible] using irreducible
      have shorter : length q < n := hn ▸ deletion_strictly_shortens d hq
      obtain ⟨r,hr,terminal⟩ := ih (length q) shorter q rfl
      exact ⟨r,.step hq hr,terminal⟩

theorem reduction_extends_action (d : Data U S V) {i k : U} {p q : Path d i k}
    (h : Reduction d p q) (a : ImageAt d.arrival i) (b : ImageAt d.arrival k) :
    p.action a b → q.action a b := by
  induction h with
  | refl => exact id
  | step del red ih => exact fun hp => ih (deletion_extends_action d del a b hp)

theorem reduction_exact_on_old_domain (d : Data U S V) {i k : U} {p q : Path d i k}
    (h : Reduction d p q) (a : ImageAt d.arrival i) (ha : p.domain a) (b : ImageAt d.arrival k) :
    q.action a b ↔ p.action a b := by
  constructor
  · intro hq
    obtain ⟨c,hc⟩ := ha
    have e := LCTR.CoreTypedWords.action_functional q a c b (reduction_extends_action d h a c hc) hq
    exact e ▸ hc
  · exact reduction_extends_action d h a b

def PureLoopIdentity (d : Data U S V) : Prop :=
  ∀ i (p : Path d i i), TransportOnly p →
    ∀ a b : ImageAt d.arrival i, p.action a b → a=b

def IrreducibleMixedIdentity (d : Data U S V) : Prop :=
  ∀ i (p : Path d i i), Irreducible p → ¬ SourceOnly p → ¬ TransportOnly p →
    ∀ a b : ImageAt d.arrival i, p.action a b → a=b

theorem pure_and_irreducible_mixed_give_all_loops (d : Data U S V)
    (pure : PureLoopIdentity d) (mixed : IrreducibleMixedIdentity d) :
    LCTR.CoreTypedWords.LoopIdentity (system d) := by
  intro i p a b act
  classical
  obtain ⟨q,reduction,terminal⟩ := finite_source_reduction d p
  have hq := reduction_extends_action d reduction a b act
  by_cases hs : SourceOnly q
  · exact source_loop_identity d i q hs a b hq
  · by_cases ht : TransportOnly q
    · exact pure i q ht a b hq
    · exact mixed i q terminal hs ht a b hq

theorem pure_iff_all_loops_under_mixed (d : Data U S V) (mixed : IrreducibleMixedIdentity d) :
    PureLoopIdentity d ↔ LCTR.CoreTypedWords.LoopIdentity (system d) :=
  ⟨fun pure => pure_and_irreducible_mixed_give_all_loops d pure mixed,
    fun loops i p _ a b h => loops i p a b h⟩

theorem gluing_iff_local_injectivity (d : Data U S V) (mixed : IrreducibleMixedIdentity d) :
    PureLoopIdentity d ↔ ∀ i, Function.Injective (fun a : ImageAt d.arrival i =>
      Quotient.mk (LCTR.CoreTypedWords.orbitSetoid (system d)) ⟨i,a⟩) :=
  (pure_iff_all_loops_under_mixed d mixed).trans
    (LCTR.CoreTypedWords.loop_identity_iff_local_projection_injective (system d))

end LCTR.CoreSourceLoops
