import CoreAbstractWordEncoding

namespace LCTR.CoreLocalLoopSpecification
open Set LCTR.CoreAbstractWordEncoding
universe u v
set_option autoImplicit false
variable {U : Type u} {V : Type v}

def step (adm : U → U → Prop) (sign : Bool) (i j : U) : Prop :=
  if sign then adm i j else adm j i

theorem directed_step (adm : U → U → Prop) (sign : Bool) (i j : U) :
    step adm sign i j ↔ (sign=true ∧ adm i j) ∨ (sign=false ∧ adm j i) := by
  cases sign <;> simp [step]

structure Spec (adm : U → U → Prop) (image : U → Set V) (base : U) where
  word : Raw (step adm) base base
  positive : word.edges ≠ []
  domain : Set V
  typed : domain ⊆ image base

variable {adm : U → U → Prop} {image : U → Set V} {base : U}

def display (s : Spec adm image base) : (Nat × List U × List Bool) × Set V :=
  (s.word.display,s.domain)

theorem specification_shape (s : Spec adm image base) :
    0 < s.word.edges.length ∧ s.word.positions.length=s.word.edges.length+1 ∧
    s.word.kinds.length=s.word.edges.length ∧ s.domain ⊆ image base := by
  exact ⟨List.length_pos_iff.mpr s.positive,(tuple_lengths s.word).1,
    (tuple_lengths s.word).2,s.typed⟩

theorem display_injective : Function.Injective
    (display : Spec adm image base → (Nat × List U × List Bool) × Set V) := by
  intro s t h
  have hw : s.word=t.word := displayed_tuple_injective (congrArg Prod.fst h)
  have hd : s.domain=t.domain := congrArg Prod.snd h
  cases s
  cases t
  cases hw
  cases hd
  rfl

theorem tuple_reconstruction (es : List (U × Bool)) (D : Set V) :
    (validEdges (step adm) base es base ∧ es ≠ [] ∧ D ⊆ image base) ↔
    ∃! s : Spec adm image base, s.word.edges=es ∧ s.domain=D := by
  constructor
  · rintro ⟨valid,positive,typed⟩
    obtain ⟨w,hw⟩ := (CoreAbstractWordEncoding.tuple_reconstruction es).mp valid
    let s : Spec adm image base := ⟨w,by simpa only [hw] using positive,D,typed⟩
    refine ⟨s,⟨hw,rfl⟩,?_⟩
    intro t ht
    apply display_injective
    have ew : t.word=w := edges_injective t.word w (ht.1.trans hw.symm)
    exact Prod.ext (congrArg Raw.display ew) ht.2
  · rintro ⟨s,hs,_⟩
    exact ⟨hs.1 ▸ edges_valid s.word,hs.1 ▸ s.positive,hs.2 ▸ s.typed⟩

theorem separate_lists_reconstruction (ps : List U) (signs : List Bool)
    (same_length : ps.length=signs.length) (D : Set V)
    (valid : validEdges (step adm) base (ps.zip signs) base)
    (positive : ps ≠ []) (typed : D ⊆ image base) :
    ∃! s : Spec adm image base,
      display s=((ps.length,base::ps,signs),D) := by
  have nz : ps.zip signs ≠ [] := by
    intro h
    have len := congrArg List.length h
    simp only [List.length_zip,same_length,min_self,List.length_nil] at len
    have pz : ps.length=0 := same_length.trans len
    exact positive (List.length_eq_zero_iff.mp pz)
  obtain ⟨s,hs,_⟩ := (tuple_reconstruction (ps.zip signs) D).mp ⟨valid,nz,typed⟩
  have hp : (ps.zip signs).map Prod.fst=ps := List.map_fst_zip same_length.le
  have hk : (ps.zip signs).map Prod.snd=signs := List.map_snd_zip same_length.ge
  have ds : display s=((ps.length,base::ps,signs),D) := by
    simp only [display,Raw.display,Raw.positions,Raw.kinds,hs.1,hs.2,hp,hk,
      List.length_zip,← same_length,min_self]
  exact ⟨s,ds,fun t ht => display_injective (ht.trans ds.symm)⟩

theorem zero_length_excluded (s : Spec adm image base) : s.word.edges.length ≠ 0 :=
  Nat.ne_of_gt (specification_shape s).1

def restrict (s : Spec adm image base) (D : Set V) (h : D ⊆ image base) : Spec adm image base :=
  ⟨s.word,s.positive,D,h⟩

theorem domain_replacement_retains_word (s : Spec adm image base) (D : Set V)
    (h : D ⊆ image base) : (restrict s D h).word=s.word ∧ (restrict s D h).domain=D :=
  ⟨rfl,rfl⟩

theorem empty_domain_allowed (s : Spec adm image base) :
    ∃ t : Spec adm image base, t.word=s.word ∧ t.domain=∅ :=
  ⟨restrict s ∅ (Set.empty_subset _),rfl,rfl⟩

def taggedDomain (s : Spec adm image base) : Set (U × V) :=
  {p | p.1=base ∧ p.2 ∈ s.domain}

theorem tagged_domain_exact (s : Spec adm image base) :
    taggedDomain s = {base} ×ˢ s.domain ∧ taggedDomain s ⊆ {base} ×ˢ image base := by
  constructor
  · rfl
  · intro p hp
    exact ⟨hp.1,s.typed hp.2⟩

end LCTR.CoreLocalLoopSpecification
