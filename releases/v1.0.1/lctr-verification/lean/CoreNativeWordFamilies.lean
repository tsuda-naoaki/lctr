import CoreSourceLoops
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace LCTR.CoreNativeWordFamilies
noncomputable section
open LCTR.CoreTypedWords LCTR.CoreSourceLoops LCTR.CoreSourceMatch
open LCTR.CoreComparisonIntegration
universe u v w
set_option autoImplicit false
variable {U : Type u} {S : Type v} {V : U → Type w}
variable {d : Data U S V} {i j k : U}

def sourceWeight : Kind → Nat
  | .src => 1
  | .trPlus => 0
  | .trMinus => 0

def transportWeight : Kind → Nat
  | .src => 0
  | .trPlus => 1
  | .trMinus => 1

def sourceCount {d : Data U S V} {i j : U} : Path d i j → Nat
  | .nil _ => 0
  | .cons e p => sourceWeight e.val + sourceCount p

def transportCount {d : Data U S V} {i j : U} : Path d i j → Nat
  | .nil _ => 0
  | .cons e p => transportWeight e.val + transportCount p

theorem length_partition (p : Path d i j) :
    length p = sourceCount p + transportCount p := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    simp only [length, sourceCount, transportCount, ih]
    cases e.val <;> simp [sourceWeight, transportWeight] <;> omega

theorem source_only_iff (p : Path d i j) : SourceOnly p ↔ transportCount p = 0 := by
  induction p with
  | nil => simp [SourceOnly, transportCount]
  | cons e p ih =>
    simp only [SourceOnly, transportCount, ih]
    cases e.val <;> simp [transportWeight]

theorem transport_only_iff (p : Path d i j) : TransportOnly p ↔ sourceCount p = 0 := by
  induction p with
  | nil => simp [TransportOnly, sourceCount]
  | cons e p ih =>
    simp only [TransportOnly, sourceCount, ih]
    cases e.val <;> simp [sourceWeight]

theorem append_counts (p : Path d i j) (q : Path d j k) :
    sourceCount (p.append q) = sourceCount p + sourceCount q ∧
    transportCount (p.append q) = transportCount p + transportCount q := by
  induction p with
  | nil => simp [Word.append, sourceCount, transportCount]
  | cons e p ih =>
    simp only [Word.append, sourceCount, transportCount, (ih q).1, (ih q).2, Nat.add_assoc]
    exact ⟨trivial, trivial⟩

theorem reverse_counts (p : Path d i j) :
    sourceCount p.reverse = sourceCount p ∧ transportCount p.reverse = transportCount p := by
  induction p with
  | nil => exact ⟨rfl,rfl⟩
  | cons e p ih =>
    simp only [Word.reverse, (append_counts _ _).1, (append_counts _ _).2,
      sourceCount, transportCount, ih.1, ih.2, Nat.add_zero]
    change sourceCount p + sourceWeight (reverseKind e.val) =
        sourceWeight e.val + sourceCount p ∧
      transportCount p + transportWeight (reverseKind e.val) =
        transportWeight e.val + transportCount p
    cases e.val <;> simp [reverseKind,sourceWeight,transportWeight,Nat.add_comm]

theorem pure_families_closed (p : Path d i j) (q : Path d j k) :
    (SourceOnly (p.append q) ↔ SourceOnly p ∧ SourceOnly q) ∧
    (TransportOnly (p.append q) ↔ TransportOnly p ∧ TransportOnly q) ∧
    (SourceOnly p.reverse ↔ SourceOnly p) ∧
    (TransportOnly p.reverse ↔ TransportOnly p) := by
  simp only [source_only_iff, transport_only_iff, (append_counts p q).1,
    (append_counts p q).2, (reverse_counts p).1, (reverse_counts p).2, Nat.add_eq_zero_iff]
  exact ⟨trivial,trivial,trivial,trivial⟩

abbrev SourceWord (d : Data U S V) (i j : U) := {p : Path d i j // SourceOnly p}
abbrev TransportWord (d : Data U S V) (i j : U) := {p : Path d i j // TransportOnly p}

def sourceEmpty (d : Data U S V) (i : U) : SourceWord d i i := ⟨.nil i,trivial⟩
def transportEmpty (d : Data U S V) (i : U) : TransportWord d i i := ⟨.nil i,trivial⟩
def sourceAppend (p : SourceWord d i j) (q : SourceWord d j k) : SourceWord d i k :=
  ⟨p.val.append q.val, ((pure_families_closed p.val q.val).1).mpr ⟨p.property,q.property⟩⟩
def transportAppend (p : TransportWord d i j) (q : TransportWord d j k) : TransportWord d i k :=
  ⟨p.val.append q.val, ((pure_families_closed p.val q.val).2.1).mpr ⟨p.property,q.property⟩⟩
def sourceReverse (p : SourceWord d i j) : SourceWord d j i :=
  ⟨p.val.reverse, ((pure_families_closed p.val (.nil j)).2.2.1).mpr p.property⟩
def transportReverse (p : TransportWord d i j) : TransportWord d j i :=
  ⟨p.val.reverse, ((pure_families_closed p.val (.nil j)).2.2.2).mpr p.property⟩

theorem standard_embeddings_injective :
    Function.Injective (Subtype.val : SourceWord d i j → Path d i j) ∧
    Function.Injective (Subtype.val : TransportWord d i j → Path d i j) :=
  ⟨Subtype.val_injective,Subtype.val_injective⟩

theorem standard_embeddings_operations (p : SourceWord d i j) (q : SourceWord d j k)
    (r : TransportWord d i j) (s : TransportWord d j k) :
    (sourceAppend p q).val = p.val.append q.val ∧
    (transportAppend r s).val = r.val.append s.val ∧
    (sourceReverse p).val = p.val.reverse ∧
    (transportReverse r).val = r.val.reverse ∧
    (sourceEmpty d i).val = LCTR.CoreTypedWords.Word.nil i ∧
    (transportEmpty d i).val = LCTR.CoreTypedWords.Word.nil i :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem source_action_laws (p : SourceWord d i j) (q : SourceWord d j k)
    (a : ImageAt d.arrival i) (b : ImageAt d.arrival j) (c : ImageAt d.arrival k) :
    ((sourceReverse p).val.action b a ↔ p.val.action a b) ∧
    ((sourceAppend p q).val.domain a ↔ ∃ z, p.val.action a z ∧ q.val.domain z) ∧
    ((sourceAppend p q).val.action a c ↔ ∃ z, p.val.action a z ∧ q.val.action z c) ∧
    (∀ a', (sourceEmpty d i).val.action a a' ↔ a=a') :=
  ⟨reverse_action p.val a b,append_domain p.val q.val a,append_action p.val q.val a c,
    fun _ => Iff.rfl⟩

theorem transport_action_laws (p : TransportWord d i j) (q : TransportWord d j k)
    (a : ImageAt d.arrival i) (b : ImageAt d.arrival j) (c : ImageAt d.arrival k) :
    ((transportReverse p).val.action b a ↔ p.val.action a b) ∧
    ((transportAppend p q).val.domain a ↔ ∃ z, p.val.action a z ∧ q.val.domain z) ∧
    ((transportAppend p q).val.action a c ↔ ∃ z, p.val.action a z ∧ q.val.action z c) ∧
    (∀ a', (transportEmpty d i).val.action a a' ↔ a=a') :=
  ⟨reverse_action p.val a b,append_domain p.val q.val a,append_action p.val q.val a c,
    fun _ => Iff.rfl⟩

theorem extended_action_laws (p : Path d i j) (q : Path d j k)
    (a : ImageAt d.arrival i) (b : ImageAt d.arrival j) (c : ImageAt d.arrival k) :
    (p.reverse.action b a ↔ p.action a b) ∧
    ((p.append q).domain a ↔ ∃ z, p.action a z ∧ q.domain z) ∧
    ((p.append q).action a c ↔ ∃ z, p.action a z ∧ q.action z c) ∧
    (∀ a', (LCTR.CoreTypedWords.Word.nil (W := system d) i).action a a' ↔ a=a') :=
  ⟨reverse_action p a b,append_domain p q a,append_action p q a c,fun _ => Iff.rfl⟩

theorem native_partial_injectivity (p : Path d i j) :
    (∀ a b c, p.action a b → p.action a c → b=c) ∧
    (∀ a b c, p.action a c → p.action b c → a=b) :=
  ⟨action_functional p,action_injective p⟩

def Mixed (p : Path d i j) : Prop := 0 < sourceCount p ∧ 0 < transportCount p

def Case (p : Path d i j) : Fin 4 → Prop
  | ⟨0,_⟩ => length p = 0
  | ⟨1,_⟩ => 0 < length p ∧ TransportOnly p
  | ⟨2,_⟩ => 0 < length p ∧ SourceOnly p
  | ⟨3,_⟩ => Mixed p

theorem four_cases_exist_unique (p : Path d i j) : ∃! c : Fin 4, Case p c := by
  have hlen := length_partition p
  have hs := source_only_iff p
  have ht := transport_only_iff p
  by_cases sn : sourceCount p = 0 <;> by_cases tn : transportCount p = 0
  · refine ⟨0,?_,?_⟩
    · change length p = 0; omega
    · intro c hc
      fin_cases c <;> simp only [Case, Mixed, hs, ht] at hc <;> first | rfl | omega
  · refine ⟨1,?_,?_⟩
    · change 0 < length p ∧ TransportOnly p
      exact ⟨by omega, ht.mpr sn⟩
    · intro c hc
      fin_cases c <;> simp only [Case, Mixed, hs, ht] at hc <;> first | rfl | omega
  · refine ⟨2,?_,?_⟩
    · change 0 < length p ∧ SourceOnly p
      exact ⟨by omega, hs.mpr tn⟩
    · intro c hc
      fin_cases c <;> simp only [Case, Mixed, hs, ht] at hc <;> first | rfl | omega
  · refine ⟨3,?_,?_⟩
    · change 0 < sourceCount p ∧ 0 < transportCount p
      omega
    · intro c hc
      fin_cases c <;> simp only [Case, Mixed, hs, ht] at hc <;> first | rfl | omega

theorem unique_pure_preimages (p : Path d i j) :
    (TransportOnly p → ∃! q : TransportWord d i j, q.val=p) ∧
    (SourceOnly p → ∃! q : SourceWord d i j, q.val=p) := by
  constructor
  · intro h
    exact ⟨⟨p,h⟩,rfl,fun q hq => Subtype.ext hq⟩
  · intro h
    exact ⟨⟨p,h⟩,rfl,fun q hq => Subtype.ext hq⟩

theorem common_pure_family_iff_empty (p : Path d i j) :
    SourceOnly p ∧ TransportOnly p ↔ length p = 0 := by
  rw [source_only_iff,transport_only_iff]
  have h := length_partition p
  omega

end
end LCTR.CoreNativeWordFamilies
