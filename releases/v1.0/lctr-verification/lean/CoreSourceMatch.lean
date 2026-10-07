import Chapter03SourceOrderRecovery
import LCTR.Section4_02MutualArrivalOrdSep
import CorePreorderQuotient

namespace LCTR.CoreSourceMatch

open LCTR.Chapter03SourceOrderRecovery
universe u v w
set_option autoImplicit false

variable {U : Type u} {S : Type v} {V : U → Type w}

def ImageAt (A : ∀ u, PartialArrival S (V u)) (u : U) :=
  Set.range (fun x : {s // s ∈ (A u).dom} => (A u).val x.val x.property)

def L1 (A : ∀ u, PartialArrival S (V u)) : Prop :=
  ∀ u (a : ImageAt A u), UniqueRecoverable (A u) a.val

abbrev Tagged (A : ∀ u, PartialArrival S (V u)) := Sigma (fun u => ImageAt A u)

noncomputable def localRecovery (A : ∀ u, PartialArrival S (V u)) (h : L1 A)
    (u : U) (a : ImageAt A u) := recoverSubtype (A u) a.val (h u a)

noncomputable def recover (A : ∀ u, PartialArrival S (V u)) (h : L1 A)
    (p : Tagged A) : S := (localRecovery A h p.1 p.2).val

theorem l1_iff_injective (A : ∀ u, PartialArrival S (V u)) :
    L1 A ↔ ∀ u, Function.Injective (fun x : {s // s ∈ (A u).dom} => (A u).val x.val x.property) := by
  constructor
  · intro h u x y hxy
    have hu := h u ⟨(A u).val x.val x.property, ⟨x, rfl⟩⟩
    exact hu.2 x y rfl hxy.symm
  · intro hi u a
    refine ⟨a.property, ?_⟩
    intro x y hx hy
    exact hi u (hx.trans hy.symm)

theorem arrival_recovery (A : ∀ u, PartialArrival S (V u)) (h : L1 A)
    (u : U) (a : ImageAt A u) :
    (A u).val (localRecovery A h u a).val (localRecovery A h u a).property = a.val :=
  recoverSubtype_spec (A u) a.val (h u a)

noncomputable def srcMatch (A : ∀ u, PartialArrival S (V u)) (h : L1 A)
    (u v : U) (a : ImageAt A u) (hd : (localRecovery A h u a).val ∈ (A v).dom) : ImageAt A v :=
  ⟨(A v).val (localRecovery A h u a).val hd, ⟨⟨_, hd⟩, rfl⟩⟩

theorem recover_srcMatch (A : ∀ u, PartialArrival S (V u)) (h : L1 A)
    (u v : U) (a : ImageAt A u) (hd : (localRecovery A h u a).val ∈ (A v).dom) :
    (localRecovery A h v (srcMatch A h u v a hd)).val = (localRecovery A h u a).val :=
  recover_eq_original (A v) _ hd (h v (srcMatch A h u v a hd))

theorem same_source_native_match (A : ∀ u, PartialArrival S (V u)) (h : L1 A)
    (u v : U) (a : ImageAt A u) (b : ImageAt A v)
    (heq : (localRecovery A h u a).val = (localRecovery A h v b).val) :
    ∃ hd : (localRecovery A h u a).val ∈ (A v).dom, srcMatch A h u v a hd = b := by
  have hd : (localRecovery A h u a).val ∈ (A v).dom := heq ▸ (localRecovery A h v b).property
  refine ⟨hd, Subtype.ext ?_⟩
  have e : (⟨(localRecovery A h u a).val, hd⟩ : {s // s ∈ (A v).dom}) =
      localRecovery A h v b := Subtype.ext heq
  have f := congrArg (fun x : {s // s ∈ (A v).dom} => (A v).val x.val x.property) e
  exact f.trans (arrival_recovery A h v b)

def SrcGraph (A : ∀ u, PartialArrival S (V u)) (h : L1 A)
    (u v : U) (a : ImageAt A u) (b : ImageAt A v) : Prop :=
  ∃ hd : (localRecovery A h u a).val ∈ (A v).dom, srcMatch A h u v a hd = b

theorem srcGraph_iff_same_recovery (A : ∀ u, PartialArrival S (V u)) (h : L1 A)
    (u v : U) (a : ImageAt A u) (b : ImageAt A v) :
    SrcGraph A h u v a b ↔ (localRecovery A h u a).val = (localRecovery A h v b).val := by
  constructor
  · rintro ⟨hd, rfl⟩
    exact (recover_srcMatch A h u v a hd).symm
  · exact same_source_native_match A h u v a b

theorem source_match_inverse_graph (A : ∀ u, PartialArrival S (V u)) (h : L1 A)
    (u v : U) (a : ImageAt A u) (b : ImageAt A v) :
    SrcGraph A h u v a b ↔ SrcGraph A h v u b a := by
  rw [srcGraph_iff_same_recovery, srcGraph_iff_same_recovery]
  exact eq_comm

theorem recovery_injective (A : ∀ u, PartialArrival S (V u)) (h : L1 A) (u : U) :
    Function.Injective (fun a : ImageAt A u => (localRecovery A h u a).val) := by
  intro a b hab
  have e : localRecovery A h u a = localRecovery A h u b := Subtype.ext hab
  have f := congrArg (fun x : {s // s ∈ (A u).dom} => (A u).val x.val x.property) e
  apply Subtype.ext
  exact (arrival_recovery A h u a).symm.trans (f.trans (arrival_recovery A h u b))

theorem source_match_functional (A : ∀ u, PartialArrival S (V u)) (h : L1 A)
    (u v : U) (a : ImageAt A u) (b c : ImageAt A v)
    (hb : SrcGraph A h u v a b) (hc : SrcGraph A h u v a c) : b=c := by
  apply recovery_injective A h v
  exact ((srcGraph_iff_same_recovery A h u v a b).mp hb).symm.trans
    ((srcGraph_iff_same_recovery A h u v a c).mp hc)

theorem source_match_injective (A : ∀ u, PartialArrival S (V u)) (h : L1 A)
    (u v : U) (a b : ImageAt A u) (c : ImageAt A v)
    (ha : SrcGraph A h u v a c) (hb : SrcGraph A h u v b c) : a=b := by
  exact source_match_functional A h v u c a b
    ((source_match_inverse_graph A h u v a c).mp ha)
    ((source_match_inverse_graph A h u v b c).mp hb)

inductive Kind where | src | trPlus | trMinus

def Admissible (adm : U → U → Prop) : Kind → U → U → Prop
  | .src, _, _ => True
  | .trPlus, u, v => adm u v
  | .trMinus, u, v => adm v u

inductive Word (adm : U → U → Prop) : U → U → Type u
  | nil (u : U) : Word adm u u
  | cons {u v z : U} (k : Kind) : Admissible adm k u v → Word adm v z → Word adm u z

def Word.kinds {adm : U → U → Prop} {u v : U} : Word adm u v → List Kind
  | .nil _ => []
  | .cons k _ rest => k :: rest.kinds

def Word.positions {adm : U → U → Prop} {u v : U} : Word adm u v → List U
  | .nil u => [u]
  | @Word.cons _ _ u _ _ _ _ rest => u :: rest.positions

def sourceWord (adm : U → U → Prop) (u v : U) : Word adm u v :=
  .cons .src trivial (.nil v)

theorem sourceWord_encoding (adm : U → U → Prop) (u v : U) :
    (sourceWord adm u v).kinds = [.src] ∧ (sourceWord adm u v).positions = [u,v] := ⟨rfl,rfl⟩

def Atom (A : ∀ u, PartialArrival S (V u)) (h : L1 A)
    (transport : ∀ u v, ImageAt A u → ImageAt A v → Prop) :
    Kind → ∀ u v, ImageAt A u → ImageAt A v → Prop
  | .src, u, v => SrcGraph A h u v
  | .trPlus, u, v => transport u v
  | .trMinus, u, v => fun a b => transport v u b a

def Word.action (A : ∀ u, PartialArrival S (V u)) (h : L1 A)
    (transport : ∀ u v, ImageAt A u → ImageAt A v → Prop)
    {adm : U → U → Prop} {u v : U} : Word adm u v → ImageAt A u → ImageAt A v → Prop
  | .nil _, a, b => a = b
  | .cons k _ rest, a, b => ∃ mid, Atom A h transport k _ _ a mid ∧ rest.action A h transport mid b

theorem sourceWord_action (A : ∀ u, PartialArrival S (V u)) (h : L1 A)
    (transport : ∀ u v, ImageAt A u → ImageAt A v → Prop) (adm : U → U → Prop)
    (u v : U) (a : ImageAt A u) (b : ImageAt A v) :
    (sourceWord adm u v).action A h transport a b ↔ SrcGraph A h u v a b := by
  simp [sourceWord, Word.action, Atom]

def Orbit (A : ∀ u, PartialArrival S (V u)) (h : L1 A)
    (transport : ∀ u v, ImageAt A u → ImageAt A v → Prop) (adm : U → U → Prop)
    (p q : Tagged A) : Prop := ∃ word : Word adm p.1 q.1, word.action A h transport p.2 q.2

theorem equal_recovery_orbit (A : ∀ u, PartialArrival S (V u)) (h : L1 A)
    (transport : ∀ u v, ImageAt A u → ImageAt A v → Prop) (adm : U → U → Prop)
    (p q : Tagged A) (heq : recover A h p = recover A h q) : Orbit A h transport adm p q := by
  refine ⟨sourceWord adm p.1 q.1, ?_⟩
  exact (sourceWord_action A h transport adm p.1 q.1 p.2 q.2).mpr
    (same_source_native_match A h p.1 q.1 p.2 q.2 heq)

theorem mutual_arrival_order_separation (A : ∀ u, PartialArrival S (V u)) (h : L1 A)
    (transport : ∀ u v, ImageAt A u → ImageAt A v → Prop) (adm : U → U → Prop)
    (r : S → S → Prop) (anti : ∀ {s t}, r s t → r t s → s=t) :
    LCTR.Section402MutualArrivalOrdSep.OrdSep (Orbit A h transport adm)
      (LCTR.Section402MutualArrivalOrdSep.Pullback (recover A h) r) := by
  apply LCTR.Section402MutualArrivalOrdSep.ordSep_of_recovery_antisymmetry
    (recover A h) r (Orbit A h transport adm) anti
  intro p q heq
  exact equal_recovery_orbit A h transport adm p q heq

def singletonArrival (u : Bool) : PartialArrival Bool Unit :=
  ⟨{u}, fun _ _ => ()⟩

theorem singleton_l1 : L1 singletonArrival := by
  apply (l1_iff_injective singletonArrival).mpr
  intro u x y _
  apply Subtype.ext
  exact (Set.mem_singleton_iff.mp x.property).trans (Set.mem_singleton_iff.mp y.property).symm

def unitImage (u : Bool) : ImageAt singletonArrival u := ⟨(), ⟨⟨u,rfl⟩,rfl⟩⟩

theorem equal_display_not_source_match :
    (unitImage false).val = (unitImage true).val ∧
    ¬ SrcGraph singletonArrival singleton_l1 false true (unitImage false) (unitImage true) := by
  refine ⟨rfl, ?_⟩
  intro h
  have eq := (srcGraph_iff_same_recovery _ _ _ _ _ _).mp h
  have hf : (localRecovery singletonArrival singleton_l1 false (unitImage false)).val = false :=
    Set.mem_singleton_iff.mp (localRecovery singletonArrival singleton_l1 false (unitImage false)).property
  have ht : (localRecovery singletonArrival singleton_l1 true (unitImage true)).val = true :=
    Set.mem_singleton_iff.mp (localRecovery singletonArrival singleton_l1 true (unitImage true)).property
  have bad : false = true := hf.symm.trans (eq.trans ht)
  cases bad

end LCTR.CoreSourceMatch
