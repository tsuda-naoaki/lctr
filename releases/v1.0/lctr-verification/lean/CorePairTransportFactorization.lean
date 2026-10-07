import Mathlib.Data.Set.Function
import Mathlib.Data.Fin.VecNotation

namespace LCTR.CorePairTransportFactorization
set_option autoImplicit false
open Set
universe u v w
variable {I : Type u} {X : I → Type v} {Y : I → Type w}
abbrev PairInput := (i : I) → X i
abbrev PairOutput := (i : I) → Y i
def projection (D : Set (PairInput (X:=X))) (i : I) : Set (X i) :=
  {a | ∃ x ∈ D, x i=a}

structure Factorization (R : PairInput (X:=X) → PairOutput (Y:=Y) → Prop) where
  domain : Set (PairInput (X:=X))
  map : (i : I) → projection domain i → Y i
  injective : ∀ i, Function.Injective (map i)
  graph : ∀ x y, R x y ↔ ∃ hx : x ∈ domain,
    ∀ i, y i = map i ⟨x i,⟨x,hx,rfl⟩⟩

variable (R : PairInput (X:=X) → PairOutput (Y:=Y) → Prop)
def component (i : I) (a : X i) (b : Y i) : Prop :=
  ∃ x y, R x y ∧ x i=a ∧ y i=b

variable (f : Factorization R)
theorem domain_forced : f.domain = {x | ∃ y, R x y} := by
  ext x
  constructor
  · intro hx
    exact ⟨fun i => f.map i ⟨x i,⟨x,hx,rfl⟩⟩,(f.graph x _).mpr ⟨hx,fun _ => rfl⟩⟩
  · rintro ⟨y,h⟩
    exact ((f.graph x y).mp h).choose

theorem component_graph_exact (i : I) (a : X i) (b : Y i) :
    component R i a b ↔ ∃ ha : a ∈ projection f.domain i, f.map i ⟨a,ha⟩=b := by
  constructor
  · rintro ⟨x,y,h,hx,hy⟩
    obtain ⟨hd,hm⟩ := (f.graph x y).mp h
    subst a
    exact ⟨⟨x,hd,rfl⟩,(hm i).symm.trans hy⟩
  · rintro ⟨ha,hm⟩
    obtain ⟨x,hx,eq⟩ := ha
    subst a
    let y : PairOutput (Y:=Y) := fun j => f.map j ⟨x j,⟨x,hx,rfl⟩⟩
    exact ⟨x,y,(f.graph x y).mpr ⟨hx,fun _ => rfl⟩,rfl,hm⟩

include f in
theorem component_functional (i : I) (a : X i) (b c : Y i)
    (hb : component R i a b) (hc : component R i a c) : b=c := by
  obtain ⟨ha,eqb⟩ := (component_graph_exact R f i a b).mp hb
  obtain ⟨_,eqc⟩ := (component_graph_exact R f i a c).mp hc
  exact eqb.symm.trans eqc

include f in
theorem component_injective (i : I) (a b : X i) (c : Y i)
    (ha : component R i a c) (hb : component R i b c) : a=b := by
  obtain ⟨pa,eqa⟩ := (component_graph_exact R f i a c).mp ha
  obtain ⟨pb,eqb⟩ := (component_graph_exact R f i b c).mp hb
  exact congrArg Subtype.val (f.injective i (eqa.trans eqb.symm))

theorem factorization_unique (g : Factorization R) : f=g := by
  have hd : f.domain=g.domain := (domain_forced R f).trans (domain_forced R g).symm
  cases f with
  | mk D fm fi fg =>
    cases g with
    | mk E gm gi gg =>
      change D=E at hd
      subst E
      have same : fm=gm := by
        funext i a
        obtain ⟨x,hx,hxa⟩ := a.property
        have hr := (fg x (fun j => fm j ⟨x j,⟨x,hx,rfl⟩⟩)).mpr ⟨hx,fun _ => rfl⟩
        obtain ⟨_,he⟩ := (gg x _).mp hr
        have ar : (⟨x i,⟨x,hx,rfl⟩⟩ : projection D i) = a := Subtype.ext hxa
        have eq := he i
        simpa only [ar] using eq
      cases same
      rfl

theorem existence_unique_iff : Nonempty (Factorization R) ↔ ∃! _f : Factorization R, True := by
  constructor
  · rintro ⟨f⟩
    exact ⟨f,trivial,fun g _ => factorization_unique R g f⟩
  · rintro ⟨f,_,_⟩
    exact ⟨f⟩

def coupled : (Fin 2 → Bool) → (Fin 2 → Bool) → Prop :=
  fun x y => (x=![false,false] ∧ y=![false,false]) ∨ (x=![false,true] ∧ y=![true,true])

theorem joint_function_does_not_ensure_component_factorization :
    (∀ x y z, coupled x y → coupled x z → y=z) ∧ ¬ Nonempty (Factorization coupled) := by
  constructor
  · intro x y z hy hz
    rcases hy with ⟨hx,rfl⟩ | ⟨hx,rfl⟩ <;> rcases hz with ⟨hx',rfl⟩ | ⟨hx',rfl⟩
    · rfl
    · have bad := congrFun (hx.symm.trans hx') 1
      simp at bad
    · have bad := congrFun (hx.symm.trans hx') 1
      simp at bad
    · rfl
  · rintro ⟨f⟩
    have h0 : component coupled 0 false false :=
      ⟨![false,false],![false,false],Or.inl ⟨rfl,rfl⟩,rfl,rfl⟩
    have h1 : component coupled 0 false true :=
      ⟨![false,true],![true,true],Or.inr ⟨rfl,rfl⟩,rfl,rfl⟩
    have bad := component_functional coupled f 0 false false true h0 h1
    cases bad

end LCTR.CorePairTransportFactorization
