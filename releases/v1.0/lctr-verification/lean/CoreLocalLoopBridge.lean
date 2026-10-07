import CoreLocalLoopSpecification
import CoreLocalLoopRealization

namespace LCTR.CoreLocalLoopBridge
open Set LCTR.CoreSourceMatch LCTR.CoreSourceLoops
open LCTR.CoreAbstractWordEncoding LCTR.CoreLocalLoopSpecification
universe u v w
set_option autoImplicit false
variable {U : Type u} {S : Type v} {V : U → Type w}
variable {d : Data U S V} {i j : U}

def encode {d : Data U S V} {i j : U} : Raw (step d.admissible) i j → Path d i j
  | .nil i => .nil i
  | .cons true h p => .cons ⟨.trPlus,h⟩ (encode p)
  | .cons false h p => .cons ⟨.trMinus,h⟩ (encode p)

theorem encoded_pure (p : Raw (step d.admissible) i j) : TransportOnly (encode p) := by
  induction p with
  | nil => trivial
  | cons sign h p ih =>
    cases sign <;> simp only [encode,TransportOnly,ih,and_true] <;> intro bad <;> cases bad

theorem length_preserved (p : Raw (step d.admissible) i j) :
    length (encode p)=p.edges.length := by
  induction p with
  | nil => rfl
  | cons sign h p ih => cases sign <;> simp only [encode,length,Raw.edges,List.length_cons,ih,Nat.add_comm]

def decode {d : Data U S V} {i j : U} : (p : Path d i j) → TransportOnly p →
    Raw (step d.admissible) i j
  | .nil i,_ => .nil i
  | .cons ⟨.src,_⟩ _,h => False.elim (h.1 rfl)
  | .cons ⟨.trPlus,h⟩ p,hp => .cons true h (decode p hp.2)
  | .cons ⟨.trMinus,h⟩ p,hp => .cons false h (decode p hp.2)

theorem decode_encode (p : Raw (step d.admissible) i j) :
    decode (encode p) (encoded_pure p)=p := by
  induction p with
  | nil => rfl
  | cons sign h p ih => cases sign <;> simp only [encode,decode,ih]

theorem encode_decode (p : Path d i j) (hp : TransportOnly p) : encode (decode p hp)=p := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    rcases e with ⟨kind,h⟩
    cases kind with
    | src => exact False.elim (hp.1 rfl)
    | trPlus => simp only [decode,encode,ih hp.2]
    | trMinus => simp only [decode,encode,ih hp.2]

theorem encoding_injective : Function.Injective
    (encode : Raw (step d.admissible) i j → Path d i j) := by
  intro p q h
  have eq : (⟨encode p,encoded_pure p⟩ : {r : Path d i j // TransportOnly r}) =
      ⟨encode q,encoded_pure q⟩ := Subtype.ext h
  have e := congrArg (fun r : {r : Path d i j // TransportOnly r} => decode r.val r.property) eq
  simpa only [decode_encode] using e

abbrev InputSpec (d : Data U S V) (b : U) :=
  CoreLocalLoopSpecification.Spec d.admissible (fun _ => (Set.univ : Set (ImageAt d.arrival b))) b

def nativeSpec (s : InputSpec d i) : CoreLocalLoopRealization.Spec d :=
  ⟨i,encode s.word,encoded_pure s.word,s.domain⟩

theorem native_spec_fields (s : InputSpec d i) :
    (nativeSpec s).base=i ∧ (nativeSpec s).word=encode s.word ∧ (nativeSpec s).domain=s.domain :=
  ⟨rfl,rfl,rfl⟩

theorem native_spec_positive (s : InputSpec d i) : 0 < length (nativeSpec s).word := by
  change 0 < length (encode s.word)
  rw [length_preserved]
  exact List.length_pos_iff.mpr s.positive

theorem candidate_partial_injection (p : Raw (step d.admissible) i j) :
    (∀ a b c, (encode p).action a b → (encode p).action a c → b=c) ∧
    (∀ a b c, (encode p).action a c → (encode p).action b c → a=b) :=
  ⟨CoreTypedWords.action_functional (encode p),CoreTypedWords.action_injective (encode p)⟩

end LCTR.CoreLocalLoopBridge
