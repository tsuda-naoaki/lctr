import CoreNativeWordFamilies

namespace LCTR.CoreWordEncoding
open LCTR.CoreSourceMatch LCTR.CoreSourceLoops
universe u v w
set_option autoImplicit false
variable {U : Type u} {S : Type v} {V : U → Type w}
variable {d : Data U S V} {i j : U}

def encode {d : Data U S V} {i j : U} : Word d.admissible i j → Path d i j
  | .nil i => .nil i
  | .cons k h p => .cons ⟨k,h⟩ (encode p)

def decode {d : Data U S V} {i j : U} : Path d i j → Word d.admissible i j
  | .nil i => .nil i
  | .cons e p => .cons e.val e.property (decode p)

theorem decode_encode (p : Word d.admissible i j) : decode (encode p) = p := by
  induction p with
  | nil => rfl
  | cons k h p ih => simp only [encode,decode,ih]

theorem encode_decode (p : Path d i j) : encode (decode p) = p := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    simp only [encode,decode,ih]
    rcases e with ⟨k,h⟩
    rfl

def pathEquiv (d : Data U S V) (i j : U) : Word d.admissible i j ≃ Path d i j where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode

theorem encoding_bijective : Function.Bijective (encode : Word d.admissible i j → Path d i j) :=
  (pathEquiv d i j).bijective

theorem action_preservation (p : Word d.admissible i j)
    (a : ImageAt d.arrival i) (b : ImageAt d.arrival j) :
    (encode p).action a b ↔ p.action d.arrival d.unique d.transport a b := by
  induction p with
  | nil => exact Iff.rfl
  | cons k h p ih =>
    change (∃ c, Atom d.arrival d.unique d.transport k _ _ a c ∧ (encode p).action c b) ↔
      (∃ c, Atom d.arrival d.unique d.transport k _ _ a c ∧ p.action d.arrival d.unique d.transport c b)
    simp only [ih]

theorem domain_preservation (p : Word d.admissible i j) (a : ImageAt d.arrival i) :
    (encode p).domain a ↔ ∃ b, p.action d.arrival d.unique d.transport a b := by
  simp only [LCTR.CoreTypedWords.Word.domain,action_preservation]

def edges {adm : U → U → Prop} {i j : U} : Word adm i j → List (U × Kind)
  | .nil _ => []
  | @Word.cons _ _ _ j _ k _ p => (j,k) :: edges p

theorem positions_from_edges {adm : U → U → Prop} {i j : U} (p : Word adm i j) :
    p.positions = i :: (edges p).map Prod.fst := by
  induction p with
  | nil => rfl
  | cons k h p ih => simp only [Word.positions,edges,List.map_cons,ih]

theorem kinds_from_edges {adm : U → U → Prop} {i j : U} (p : Word adm i j) :
    p.kinds = (edges p).map Prod.snd := by
  induction p with
  | nil => rfl
  | cons k h p ih => simp only [Word.kinds,edges,List.map_cons,ih]

theorem edges_injective {adm : U → U → Prop} {i j : U} (p : Word adm i j) :
    ∀ q : Word adm i j, edges p = edges q → p=q := by
  induction p with
  | nil =>
    intro q he
    cases q with
    | nil => rfl
    | cons k h q => simp [edges] at he
  | @cons i j k kind h p ih =>
    intro q he
    cases q with
    | nil => simp [edges] at he
    | @cons _ j' _ kind' h' q =>
      simp only [edges,List.cons.injEq,Prod.mk.injEq] at he
      obtain ⟨⟨hj,hkind⟩,ht⟩ := he
      subst j'
      subst kind'
      have eq := ih q ht
      subst q
      rfl

def displayTuple {adm : U → U → Prop} {i j : U} (p : Word adm i j) :
    Nat × List U × List Kind := (p.kinds.length,p.positions,p.kinds)

theorem displayed_tuple_injective {adm : U → U → Prop} {i j : U} :
    Function.Injective (displayTuple : Word adm i j → Nat × List U × List Kind) := by
  intro p q h
  have pos := congrArg (fun x : Nat × List U × List Kind => x.2.1) h
  have kinds := congrArg (fun x : Nat × List U × List Kind => x.2.2) h
  change p.positions = q.positions at pos
  change p.kinds = q.kinds at kinds
  rw [positions_from_edges,positions_from_edges] at pos
  rw [kinds_from_edges,kinds_from_edges] at kinds
  apply edges_injective p q
  exact (List.zip_of_prod rfl rfl).trans
    ((congrArg₂ List.zip (List.cons.inj pos).2 kinds).trans
      (List.zip_of_prod rfl rfl).symm)

theorem tuple_lengths {adm : U → U → Prop} {i j : U} (p : Word adm i j) :
    p.positions.length = p.kinds.length + 1 := by
  rw [positions_from_edges,kinds_from_edges]
  simp only [List.length_cons,List.length_map]

theorem native_length_preserved (p : Word d.admissible i j) :
    length (encode p) = p.kinds.length := by
  induction p with
  | nil => rfl
  | cons k h p ih => simp only [encode,length,Word.kinds,List.length_cons,ih,Nat.add_comm]

theorem native_display_injective :
    Function.Injective (fun p : Path d i j => displayTuple (decode p)) := by
  intro p q h
  have raw := displayed_tuple_injective h
  have native := congrArg encode raw
  simpa only [encode_decode] using native

theorem native_display_unique (p : Path d i j) :
    ∃! q : Word d.admissible i j, encode q=p ∧ displayTuple q=displayTuple (decode p) := by
  refine ⟨decode p,⟨encode_decode p,rfl⟩,?_⟩
  intro q h
  exact displayed_tuple_injective h.2

end LCTR.CoreWordEncoding
