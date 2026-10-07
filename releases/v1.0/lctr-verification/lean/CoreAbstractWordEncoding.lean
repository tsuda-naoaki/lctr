import CoreTypedWords

namespace LCTR.CoreAbstractWordEncoding
open LCTR.CoreTypedWords
universe u v w
set_option autoImplicit false

structure Data (U : Type u) (Y : U → Type v) (K : Type w) where
  adm : K → U → U → Prop
  reverse : ∀ {i j}, {k // adm k i j} → {k // adm k j i}
  invol : ∀ {i j} (e : {k // adm k i j}), reverse (reverse e) = e
  act : ∀ {i j}, {k // adm k i j} → Y i → Y j → Prop
  functional : ∀ {i j} (e : {k // adm k i j}) {x y z}, act e x y → act e x z → y=z
  converse : ∀ {i j} (e : {k // adm k i j}) x y, act (reverse e) y x ↔ act e x y

variable {U : Type u} {Y : U → Type v} {K : Type w}

def Data.system (d : Data U Y K) : System U Y where
  Atom i j := {k // d.adm k i j}
  reverse := d.reverse
  reverse_reverse := d.invol
  act := d.act
  functional := d.functional
  reverse_graph := d.converse

inductive Raw (adm : K → U → U → Prop) : U → U → Type (max u w)
  | nil (i : U) : Raw adm i i
  | cons {i j z} (k : K) : adm k i j → Raw adm j z → Raw adm i z

def encode {d : Data U Y K} {i j : U} : Raw d.adm i j → Word d.system i j
  | .nil i => .nil i
  | .cons k h p => .cons ⟨k,h⟩ (encode p)

def decode {d : Data U Y K} {i j : U} : Word d.system i j → Raw d.adm i j
  | .nil i => .nil i
  | .cons e p => .cons e.val e.property (decode p)

theorem decode_encode {d : Data U Y K} {i j : U} (p : Raw d.adm i j) :
    decode (encode p) = p := by
  induction p with
  | nil => rfl
  | cons k h p ih => simp only [encode,decode,ih]

theorem encode_decode {d : Data U Y K} {i j : U} (p : Word d.system i j) :
    encode (decode p) = p := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    simp only [encode,decode,ih]
    cases e
    rfl

theorem encoding_bijective (d : Data U Y K) (i j : U) :
    Function.Bijective (encode : Raw d.adm i j → Word d.system i j) := by
  constructor
  · intro p q h
    simpa only [decode_encode] using congrArg decode h
  · intro p
    exact ⟨decode p,encode_decode p⟩

def Raw.edges {adm : K → U → U → Prop} {i j : U} : Raw adm i j → List (U × K)
  | .nil _ => []
  | @Raw.cons _ _ _ i j z k h p => (j,k) :: p.edges

def Raw.positions {adm : K → U → U → Prop} {i j : U} (p : Raw adm i j) : List U :=
  i :: p.edges.map Prod.fst

def Raw.kinds {adm : K → U → U → Prop} {i j : U} (p : Raw adm i j) : List K :=
  p.edges.map Prod.snd

def Raw.display {adm : K → U → U → Prop} {i j : U} (p : Raw adm i j) :
    Nat × List U × List K := (p.edges.length,p.positions,p.kinds)

theorem edges_injective {adm : K → U → U → Prop} {i j : U} (p : Raw adm i j) :
    ∀ q : Raw adm i j, p.edges = q.edges → p=q := by
  induction p with
  | nil =>
    intro q h
    cases q with
    | nil => rfl
    | cons k hk q => simp [Raw.edges] at h
  | @cons i j z k hk p ih =>
    intro q h
    cases q with
    | nil => simp [Raw.edges] at h
    | @cons _ j' _ k' hk' q =>
      simp only [Raw.edges,List.cons.injEq,Prod.mk.injEq] at h
      obtain ⟨⟨hj,hk⟩,ht⟩ := h
      subst j'
      subst k'
      have e := ih q ht
      subst q
      rfl

theorem displayed_tuple_injective {adm : K → U → U → Prop} {i j : U} :
    Function.Injective (Raw.display : Raw adm i j → Nat × List U × List K) := by
  intro p q h
  have pos := congrArg (fun x : Nat × List U × List K => x.2.1) h
  have kinds := congrArg (fun x : Nat × List U × List K => x.2.2) h
  change i :: p.edges.map Prod.fst = i :: q.edges.map Prod.fst at pos
  change p.edges.map Prod.snd = q.edges.map Prod.snd at kinds
  apply edges_injective p q
  exact (List.zip_of_prod rfl rfl).trans
    ((congrArg₂ List.zip (List.cons.inj pos).2 kinds).trans
      (List.zip_of_prod rfl rfl).symm)

theorem tuple_lengths {adm : K → U → U → Prop} {i j : U} (p : Raw adm i j) :
    p.positions.length = p.edges.length + 1 ∧ p.kinds.length = p.edges.length := by
  simp [Raw.positions,Raw.kinds]

def validEdges (adm : K → U → U → Prop) : U → List (U × K) → U → Prop
  | i, [], j => i=j
  | i, (j,k)::es, z => adm k i j ∧ validEdges adm j es z

theorem edges_valid {adm : K → U → U → Prop} {i j : U} (p : Raw adm i j) :
    validEdges adm i p.edges j := by
  induction p with
  | nil => rfl
  | cons k h p ih => exact ⟨h,ih⟩

theorem tuple_reconstruction {adm : K → U → U → Prop} {i j : U} (es : List (U × K)) :
    validEdges adm i es j ↔ ∃ p : Raw adm i j, p.edges=es := by
  constructor
  · intro h
    induction es generalizing i with
    | nil =>
      change i=j at h
      subst j
      exact ⟨.nil i,rfl⟩
    | cons e es ih =>
      obtain ⟨a,k⟩ := e
      obtain ⟨hk,ht⟩ := h
      obtain ⟨p,hp⟩ := ih ht
      exact ⟨.cons k hk p,by simp only [Raw.edges,hp]⟩
  · rintro ⟨p,rfl⟩
    exact edges_valid p

def Raw.action {d : Data U Y K} {i j : U} : Raw d.adm i j → Y i → Y j → Prop
  | .nil _,a,b => a=b
  | .cons k h p,a,b => ∃ c, d.act ⟨k,h⟩ a c ∧ p.action c b

theorem action_preservation {d : Data U Y K} {i j : U} (p : Raw d.adm i j)
    (a : Y i) (b : Y j) : (encode p).action a b ↔ p.action a b := by
  induction p with
  | nil => exact Iff.rfl
  | cons k h p ih =>
    change (∃ c, d.act ⟨k,h⟩ a c ∧ (encode p).action c b) ↔
      (∃ c, d.act ⟨k,h⟩ a c ∧ p.action c b)
    simp only [ih]

def Raw.append {adm : K → U → U → Prop} {i j z : U} : Raw adm i j → Raw adm j z → Raw adm i z
  | .nil _,q => q
  | .cons k h p,q => .cons k h (p.append q)

theorem append_display {adm : K → U → U → Prop} {i j z : U}
    (p : Raw adm i j) (q : Raw adm j z) : (p.append q).edges = p.edges ++ q.edges := by
  induction p with
  | nil => rfl
  | cons k h p ih => simp only [Raw.append,Raw.edges,ih,List.cons_append]

theorem append_encoding {d : Data U Y K} {i j z : U}
    (p : Raw d.adm i j) (q : Raw d.adm j z) : encode (p.append q) = (encode p).append (encode q) := by
  induction p with
  | nil => rfl
  | cons k h p ih => simp only [Raw.append,encode,Word.append,ih]

def Raw.reverse {d : Data U Y K} {i j : U} : Raw d.adm i j → Raw d.adm j i
  | .nil i => .nil i
  | .cons k h p => p.reverse.append (.cons (d.reverse ⟨k,h⟩).val (d.reverse ⟨k,h⟩).property (.nil _))

theorem reverse_encoding {d : Data U Y K} {i j : U} (p : Raw d.adm i j) :
    encode p.reverse = (encode p).reverse := by
  induction p with
  | nil => rfl
  | cons k h p ih => simp only [Raw.reverse,append_encoding,encode,Word.reverse,ih,Data.system]

def rawSupport {adm : K → U → U → Prop} {i j : U} (p : Raw adm i j) : Set K := {k | k ∈ p.kinds}

def loopFamily {adm : K → U → U → Prop}
    (F : Set (Σ i j, Raw adm i j)) : Set (Σ i j, Raw adm i j) :=
  {p | p ∈ F ∧ p.1=p.2.1}

end LCTR.CoreAbstractWordEncoding
