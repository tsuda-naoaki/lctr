import CoreTypedWords
import CoreTaggedLifts
import CoreSourceMatch

namespace LCTR.CorePartialSequences
universe u v w z
set_option autoImplicit false

structure Graph (A : Type v) (B : Type w) where
  rel : A → B → Prop
  functional : ∀ {a b c}, rel a b → rel a c → b=c
  injective : ∀ {a b c}, rel a c → rel b c → a=b

variable {A : Type v} {B : Type w} {C : Type z}

theorem graph_ext {f g : Graph A B} (h : ∀ a b, f.rel a b ↔ g.rel a b) : f=g := by
  cases f with
  | mk fr ff fi =>
    cases g with
    | mk gr gf gi =>
      have e : fr=gr := funext (fun a => funext (fun b => propext (h a b)))
      cases e
      rfl

def Graph.reverse (f : Graph A B) : Graph B A where
  rel := fun b a => f.rel a b
  functional := f.injective
  injective := f.functional

def Graph.domain (f : Graph A B) : Set A := {a | ∃ b, f.rel a b}
def Graph.image (f : Graph A B) : Set B := {b | ∃ a, f.rel a b}

def Graph.comp (f : Graph A B) (g : Graph B C) : Graph A C where
  rel := fun a c => ∃ b, f.rel a b ∧ g.rel b c
  functional := by
    rintro a b c ⟨x,hx,hb⟩ ⟨y,hy,hc⟩
    have e := f.functional hx hy
    subst y
    exact g.functional hb hc
  injective := by
    rintro a b c ⟨x,hx,hc⟩ ⟨y,hy,hd⟩
    have e := g.injective hc hd
    subst y
    exact f.injective hx hy

def graphOf (f : LCTR.CoreTaggedLifts.PartialInjection A B) : Graph A B where
  rel := fun a b => ∃ h : a ∈ f.domain, f.value ⟨a,h⟩ = b
  functional := by
    rintro a b c ⟨ha,hb⟩ ⟨ha',hc⟩
    exact hb.symm.trans hc
  injective := by
    rintro a b c ⟨ha,hac⟩ ⟨hb,hbc⟩
    exact congrArg Subtype.val (f.injective (hac.trans hbc.symm))

theorem partial_graph_domain (f : LCTR.CoreTaggedLifts.PartialInjection A B) :
    (graphOf f).domain = f.domain := by
  ext a
  constructor
  · rintro ⟨b,h,hb⟩
    exact h
  · intro h
    exact ⟨f.value ⟨a,h⟩,h,rfl⟩

theorem partial_graph_value (f : LCTR.CoreTaggedLifts.PartialInjection A B)
    (a : f.domain) (b : B) : (graphOf f).rel a.val b ↔ f.value a=b := by
  constructor
  · rintro ⟨h,hb⟩
    exact hb
  · intro hb
    exact ⟨a.property,hb⟩

theorem reverse_domain_is_image (f : Graph A B) : f.reverse.domain = f.image := rfl

theorem inverse_composition_on_domain (f : Graph A B) (a c : A) :
    (f.comp f.reverse).rel a c ↔ a=c ∧ a ∈ f.domain := by
  constructor
  · rintro ⟨b,hab,hcb⟩
    exact ⟨f.injective hab hcb,b,hab⟩
  · rintro ⟨rfl,b,hab⟩
    exact ⟨b,hab,hab⟩

theorem composition_domain (f : Graph A B) (g : Graph B C) (a : A) :
    a ∈ (f.comp g).domain ↔ ∃ b, f.rel a b ∧ b ∈ g.domain := by
  constructor
  · rintro ⟨c,b,hab,hbc⟩
    exact ⟨b,hab,c,hbc⟩
  · rintro ⟨b,hab,c,hbc⟩
    exact ⟨c,b,hab,hbc⟩

variable {U : Type u} {Y : U → Type v}

def allPartialGraphs (U : Type u) (Y : U → Type v) : LCTR.CoreTypedWords.System U Y where
  Atom := fun i j => Graph (Y i) (Y j)
  reverse := Graph.reverse
  reverse_reverse := fun _ => rfl
  act := Graph.rel
  functional := fun e => e.functional
  reverse_graph := fun _ _ _ => Iff.rfl

abbrev Sequence (Y : U → Type v) := LCTR.CoreTypedWords.Word (allPartialGraphs U Y)

def sequenceGraph {i j : U} (p : Sequence Y i j) : Graph (Y i) (Y j) where
  rel := p.action
  functional := fun {a b c} => LCTR.CoreTypedWords.action_functional p a b c
  injective := fun {a b c} => LCTR.CoreTypedWords.action_injective p a b c

theorem empty_sequence (i : U) (a b : Y i) :
    (sequenceGraph (LCTR.CoreTypedWords.Word.nil (W := allPartialGraphs U Y) i)).rel a b ↔ a=b :=
  Iff.rfl

theorem sequence_append {i j k : U} (p : Sequence Y i j) (q : Sequence Y j k) :
    sequenceGraph (p.append q) = (sequenceGraph p).comp (sequenceGraph q) :=
  graph_ext (LCTR.CoreTypedWords.append_action p q)

theorem sequence_append_domain {i j k : U} (p : Sequence Y i j) (q : Sequence Y j k)
    (a : Y i) :
    a ∈ (sequenceGraph (p.append q)).domain ↔
      ∃ b, (sequenceGraph p).rel a b ∧ b ∈ (sequenceGraph q).domain := by
  rw [sequence_append]
  exact composition_domain _ _ a

theorem sequence_reverse {i j : U} (p : Sequence Y i j) :
    sequenceGraph p.reverse = (sequenceGraph p).reverse := by
  apply graph_ext
  intro b a
  exact LCTR.CoreTypedWords.reverse_action p a b

theorem sequence_inverse_identity {i j : U} (p : Sequence Y i j) (a c : Y i) :
    (sequenceGraph (p.append p.reverse)).rel a c ↔ a=c ∧ a ∈ (sequenceGraph p).domain := by
  rw [sequence_append,sequence_reverse]
  exact inverse_composition_on_domain _ a c

theorem sequence_partial_injectivity {i j : U} (p : Sequence Y i j) :
    (∀ a b c, (sequenceGraph p).rel a b → (sequenceGraph p).rel a c → b=c) ∧
    (∀ a b c, (sequenceGraph p).rel a c → (sequenceGraph p).rel b c → a=b) :=
  ⟨fun _ _ _ => (sequenceGraph p).functional,fun _ _ _ => (sequenceGraph p).injective⟩

open LCTR.CoreTaggedLifts LCTR.CoreSourceMatch LCTR.Chapter03SourceOrderRecovery

def tagGraph (i j : U) (f : Graph A B) : Graph (TaggedAt i A) (TaggedAt j B) where
  rel := fun a b => f.rel ((untag i A) a) ((untag j B) b)
  functional := fun hb hc => (untag j B).injective (f.functional hb hc)
  injective := fun ha hb => (untag i A).injective (f.injective ha hb)

theorem tagged_graph_reverse (i j : U) (f : Graph A B) :
    (tagGraph i j f).reverse = tagGraph j i f.reverse := rfl

variable {S : Type w} {V : U → Type z}

noncomputable def sourcePartial (arr : ∀ i, PartialArrival S (V i)) (h : L1 arr)
    (i j : U) : PartialInjection (ImageAt arr i) (ImageAt arr j) where
  domain := {a | (localRecovery arr h i a).val ∈ (arr j).dom}
  value := fun a => srcMatch arr h i j a.val a.property
  injective := by
    intro a b hab
    apply Subtype.ext
    exact source_match_injective arr h i j a.val b.val
      (srcMatch arr h i j a.val a.property) ⟨a.property,rfl⟩ ⟨b.property,hab.symm⟩

theorem source_partial_graph (arr : ∀ i, PartialArrival S (V i)) (h : L1 arr)
    (i j : U) (a : ImageAt arr i) (b : ImageAt arr j) :
    (graphOf (sourcePartial arr h i j)).rel a b ↔ SrcGraph arr h i j a b := Iff.rfl

theorem source_reverse (arr : ∀ i, PartialArrival S (V i)) (h : L1 arr) (i j : U) :
    graphOf (sourcePartial arr h j i) = (graphOf (sourcePartial arr h i j)).reverse := by
  apply graph_ext
  intro b a
  exact (source_match_inverse_graph arr h i j a b).symm

noncomputable def sourceTerm (arr : ∀ i, PartialArrival S (V i)) (h : L1 arr) (i j : U) :=
  tagGraph i j (graphOf (sourcePartial arr h i j))

theorem source_term_inverse (arr : ∀ i, PartialArrival S (V i)) (h : L1 arr) (i j : U) :
    sourceTerm arr h j i = (sourceTerm arr h i j).reverse := by
  unfold sourceTerm
  rw [source_reverse,tagged_graph_reverse]

theorem source_term_domain (arr : ∀ i, PartialArrival S (V i)) (h : L1 arr) (i j : U)
    (a : TaggedAt i (ImageAt arr i)) :
    a ∈ (sourceTerm arr h i j).domain ↔
      (localRecovery arr h i ((untag i _) a)).val ∈ (arr j).dom := by
  constructor
  · rintro ⟨b,hd,hb⟩
    exact hd
  · intro hd
    exact ⟨(untag j _).symm (srcMatch arr h i j ((untag i _) a) hd),hd,rfl⟩

theorem source_term_composition_identity (arr : ∀ i, PartialArrival S (V i)) (h : L1 arr)
    (i j : U) (a c : TaggedAt i (ImageAt arr i)) :
    ((sourceTerm arr h i j).comp (sourceTerm arr h j i)).rel a c ↔
      a=c ∧ a ∈ (sourceTerm arr h i j).domain := by
  rw [source_term_inverse]
  exact inverse_composition_on_domain _ a c

def emptySource : PartialInjection Empty Unit where
  domain := Set.univ
  value := fun a => nomatch a.val
  injective := fun a => nomatch a.val

theorem empty_carrier_supported : (graphOf emptySource).domain = Set.univ :=
  partial_graph_domain emptySource

end LCTR.CorePartialSequences
