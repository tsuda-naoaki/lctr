import Mathlib.Data.Quot
import Mathlib.Data.Set.Basic

namespace LCTR.CoreTypedWords
universe u v w
set_option autoImplicit false

structure System (U : Type u) (Y : U → Type v) where
  Atom : U → U → Type w
  reverse : ∀ {i j}, Atom i j → Atom j i
  reverse_reverse : ∀ {i j} (e : Atom i j), reverse (reverse e) = e
  act : ∀ {i j}, Atom i j → Y i → Y j → Prop
  functional : ∀ {i j} (e : Atom i j) {x y z}, act e x y → act e x z → y=z
  reverse_graph : ∀ {i j} (e : Atom i j) (x : Y i) (y : Y j),
    act (reverse e) y x ↔ act e x y

variable {U : Type u} {Y : U → Type v}

inductive Word (W : System.{u,v,w} U Y) : U → U → Type (max u w)
  | nil (i : U) : Word W i i
  | cons {i j k} : W.Atom i j → Word W j k → Word W i k

def Word.append {W : System U Y} {i j k : U} : Word W i j → Word W j k → Word W i k
  | .nil _, z => z
  | .cons e tail, z => .cons e (tail.append z)

def Word.reverse {W : System U Y} {i j : U} : Word W i j → Word W j i
  | .nil i => .nil i
  | .cons e tail => tail.reverse.append (.cons (W.reverse e) (.nil _))

def Word.action {W : System U Y} {i j : U} : Word W i j → Y i → Y j → Prop
  | .nil _, a, b => a=b
  | .cons e tail, a, b => ∃ c, W.act e a c ∧ tail.action c b

def Word.domain {W : System U Y} {i j : U} (p : Word W i j) (a : Y i) : Prop :=
  ∃ b, p.action a b

theorem empty_action (W : System U Y) (i : U) (a b : Y i) :
    (Word.nil (W := W) i).action a b ↔ a=b := Iff.rfl

theorem append_action {W : System U Y} {i j k : U}
    (p : Word W i j) (q : Word W j k) (a : Y i) (b : Y k) :
    (p.append q).action a b ↔ ∃ c, p.action a c ∧ q.action c b := by
  induction p with
  | nil => simp [Word.append, Word.action]
  | cons e tail ih =>
    simp only [Word.append, Word.action, ih]
    constructor
    · rintro ⟨x,hx,c,hc,hb⟩
      exact ⟨c,⟨x,hx,hc⟩,hb⟩
    · rintro ⟨c,⟨x,hx,hc⟩,hb⟩
      exact ⟨x,hx,c,hc,hb⟩

theorem append_domain {W : System U Y} {i j k : U}
    (p : Word W i j) (q : Word W j k) (a : Y i) :
    (p.append q).domain a ↔ ∃ c, p.action a c ∧ q.domain c := by
  simp only [Word.domain, append_action]
  constructor
  · rintro ⟨b,c,hc,hb⟩
    exact ⟨c,hc,b,hb⟩
  · rintro ⟨c,hc,b,hb⟩
    exact ⟨b,c,hc,hb⟩

theorem reverse_action {W : System U Y} {i j : U}
    (p : Word W i j) (a : Y i) (b : Y j) : p.reverse.action b a ↔ p.action a b := by
  induction p with
  | nil => exact eq_comm
  | cons e tail ih =>
    simp only [Word.reverse, append_action, Word.action]
    constructor
    · rintro ⟨c,hc,d,hd,hda⟩
      subst d
      exact ⟨c,(W.reverse_graph e a c).mp hd,(ih c b).mp hc⟩
    · rintro ⟨c,hc,hb⟩
      exact ⟨c,(ih c b).mpr hb,a,(W.reverse_graph e a c).mpr hc,rfl⟩

theorem action_functional {W : System U Y} {i j : U} (p : Word W i j)
    (a : Y i) (b c : Y j) (hb : p.action a b) (hc : p.action a c) : b=c := by
  induction p with
  | nil => exact hb.symm.trans hc
  | cons e tail ih =>
    obtain ⟨x,hx,hxb⟩ := hb
    obtain ⟨y,hy,hyc⟩ := hc
    have eq := W.functional e hx hy
    subst y
    exact ih x b c hxb hyc

theorem action_injective {W : System U Y} {i j : U} (p : Word W i j)
    (a b : Y i) (c : Y j) (ha : p.action a c) (hb : p.action b c) : a=b :=
  action_functional p.reverse c a b ((reverse_action p a c).mpr ha) ((reverse_action p b c).mpr hb)

theorem reverse_domain {W : System U Y} {i j : U} (p : Word W i j) (b : Y j) :
    p.reverse.domain b ↔ ∃ a, p.action a b := by
  simp only [Word.domain, reverse_action]

def Orbit (W : System U Y) (p q : Sigma Y) : Prop :=
  ∃ word : Word W p.1 q.1, word.action p.2 q.2

theorem orbit_equivalence (W : System U Y) : Equivalence (Orbit W) := by
  constructor
  · intro p
    exact ⟨.nil p.1,rfl⟩
  · intro p q h
    obtain ⟨word,hw⟩ := h
    exact ⟨word.reverse,(reverse_action word _ _).mpr hw⟩
  · intro p q r hp hq
    obtain ⟨first,hf⟩ := hp
    obtain ⟨second,hs⟩ := hq
    exact ⟨first.append second,(append_action first second _ _).mpr ⟨q.2,hf,hs⟩⟩

def orbitSetoid (W : System U Y) : Setoid (Sigma Y) := ⟨Orbit W,orbit_equivalence W⟩

def LoopIdentity (W : System U Y) : Prop :=
  ∀ i (word : Word W i i) (a b : Y i), word.action a b → a=b

theorem loop_identity_iff_local_projection_injective (W : System U Y) :
    LoopIdentity W ↔ ∀ i, Function.Injective (fun a : Y i => Quotient.mk (orbitSetoid W) ⟨i,a⟩) := by
  constructor
  · intro loops i a b hab
    obtain ⟨word,hw⟩ := Quotient.exact hab
    exact loops i word a b hw
  · intro inj i word a b hab
    apply inj i
    exact Quotient.sound (show Orbit W ⟨i,a⟩ ⟨i,b⟩ from ⟨word,hab⟩)

def eraseTag {X : Type v} (A : U → Set X) (p : Sigma (fun i => A i)) :
    {x : X // ∃ i, x ∈ A i} := ⟨p.2.val, p.1, p.2.property⟩

theorem disjoint_union_tag_bridge {X : Type v} (A : U → Set X)
    (hd : ∀ i j x, x ∈ A i → x ∈ A j → i=j) : Function.Bijective (eraseTag A) := by
  constructor
  · rintro ⟨i,a⟩ ⟨j,b⟩ hab
    have e : a.val=b.val := congrArg Subtype.val hab
    have ij := hd i j a.val a.property (e ▸ b.property)
    subst j
    have ab : a=b := Subtype.ext e
    subst b
    rfl
  · intro x
    obtain ⟨i,hi⟩ := x.property
    exact ⟨⟨i,⟨x.val,hi⟩⟩,rfl⟩

theorem overlapping_regions_lose_tags :
    ¬ Function.Injective (eraseTag (fun (_ : Bool) => (Set.univ : Set Unit))) := by
  intro h
  have e := h (show eraseTag (fun (_ : Bool) => (Set.univ : Set Unit))
      ⟨false,⟨(),trivial⟩⟩ = eraseTag (fun (_ : Bool) => (Set.univ : Set Unit))
      ⟨true,⟨(),trivial⟩⟩ from rfl)
  have bad : false = true := congrArg Sigma.fst e
  cases bad

end LCTR.CoreTypedWords
