import CoreExactStructure
import CoreAffineFrequency

namespace LCTR.CoreRecordCells
open Set LCTR.CoreExactStructure LCTR.CoreSourceMatch LCTR.CoreAffineFrequency
universe u v w z a b
set_option autoImplicit false
noncomputable section

variable {U : Type u} {D : Type v} {V : U → Type w} {P : Type z} [LinearOrder P]

structure Representation (d : Input U D V) (P : Type z) [LinearOrder P] where
  globalInc : GlobalInc d
  embedding : GlobalQ d globalInc → P
  order_embedding : ∀ x y, embedding x < embedding y ↔ globalOrder d globalInc x y

def arrivalImage (d : Input U D V) (i : U) (x : (d.arrival i).dom) : ImageAt d.arrival i :=
  ⟨(d.arrival i).val x.val x.property, ⟨x, rfl⟩⟩

def arrivalClass (d : Input U D V) (i : U) (x : (d.arrival i).dom) : Canonical d :=
  canonicalProjection d ⟨i, arrivalImage d i x⟩

def orderClass (d : Input U D V) (g : GlobalInc d) (i : U)
    (x : (d.arrival i).dom) : GlobalQ d g := globalProjection d g (arrivalClass d i x)

def recordValue (d : Input U D V) (r : Representation d P) (i : U)
    (x : (d.arrival i).dom) : P := represented d r.globalInc r.embedding (arrivalClass d i x)

theorem representation_injective (d : Input U D V) (r : Representation d P) :
    Function.Injective r.embedding := by
  intro x y h
  by_contra hne
  rcases (actual_global_quotient_linear d r.globalInc).2.2 hne with hxy | hyx
  · have := (r.order_embedding x y).mpr hxy
    exact (lt_irrefl _ (h ▸ this))
  · have := (r.order_embedding y x).mpr hyx
    exact (lt_irrefl _ (h ▸ this))

theorem record_value_factorization (d : Input U D V) (r : Representation d P)
    (i : U) (x : (d.arrival i).dom) :
    recordValue d r i x = r.embedding (orderClass d r.globalInc i x) := rfl

theorem record_value_kernel (d : Input U D V) (r : Representation d P)
    (i j : U) (x : (d.arrival i).dom) (y : (d.arrival j).dom) :
    recordValue d r i x = recordValue d r j y ↔
      orderClass d r.globalInc i x = orderClass d r.globalInc j y :=
  (representation_injective d r).eq_iff

def cellTokens (d : Input U D V) (W : D → Set D) (i : U) (x : D) : Set D :=
  W x ∩ (d.arrival i).dom

def cellImage (d : Input U D V) (r : Representation d P) (W : D → Set D)
    (i : U) (x : D) : Set P := recordValue d r i '' {y | y.val ∈ W x}

theorem cell_image_membership (d : Input U D V) (r : Representation d P)
    (W : D → Set D) (i : U) (x : D) (p : P) :
    p ∈ cellImage d r W i x ↔
      ∃ y : (d.arrival i).dom, y.val ∈ W x ∧ recordValue d r i y = p := Iff.rfl

theorem cell_image_nonempty (d : Input U D V) (r : Representation d P)
    (W : D → Set D) (i : U) (x : D) :
    (cellImage d r W i x).Nonempty ↔ (cellTokens d W i x).Nonempty := by
  constructor
  · rintro ⟨p,y,hy,rfl⟩
    exact ⟨y.val,hy,y.property⟩
  · rintro ⟨y,hy,ha⟩
    exact ⟨recordValue d r i ⟨y,ha⟩, ⟨y,ha⟩,hy,rfl⟩

structure Extrema (S : Set P) where
  lower : P
  upper : P
  lower_mem : lower ∈ S
  upper_mem : upper ∈ S
  lower_bound : ∀ p ∈ S, lower ≤ p
  upper_bound : ∀ p ∈ S, p ≤ upper

def HasExt (S : Set P) : Prop := Nonempty (Extrema S)

theorem has_ext_iff (S : Set P) : HasExt S ↔
    S.Nonempty ∧ ∃ l ∈ S, ∃ h ∈ S, ∀ p ∈ S, l ≤ p ∧ p ≤ h := by
  constructor
  · rintro ⟨e⟩
    exact ⟨⟨e.lower,e.lower_mem⟩,e.lower,e.lower_mem,e.upper,e.upper_mem,
      fun p hp => ⟨e.lower_bound p hp,e.upper_bound p hp⟩⟩
  · rintro ⟨_,l,hl,h,hh,hb⟩
    exact ⟨⟨l,h,hl,hh,fun p hp => (hb p hp).1,fun p hp => (hb p hp).2⟩⟩

theorem extrema_unique (S : Set P) (e f : Extrema S) :
    e.lower = f.lower ∧ e.upper = f.upper :=
  ⟨le_antisymm (e.lower_bound f.lower f.lower_mem) (f.lower_bound e.lower e.lower_mem),
   le_antisymm (f.upper_bound e.upper e.upper_mem) (e.upper_bound f.upper f.upper_mem)⟩

theorem extrema_ordered (S : Set P) (e : Extrema S) : e.lower ≤ e.upper :=
  e.lower_bound e.upper e.upper_mem

variable {K : Type a} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def affineWidth (A : AffineData K P) {S : Set P} (e : Extrema S) : K := A.diff e.upper e.lower

theorem width_nonnegative (A : AffineData K P) (S : Set P) (e : Extrema S) :
    0 ≤ affineWidth A e := (difference_nonnegative A _ _).mp (extrema_ordered S e)

theorem width_witness_independent (A : AffineData K P) (S : Set P) (e f : Extrema S) :
    affineWidth A e = affineWidth A f := by
  obtain ⟨hl,hu⟩ := extrema_unique S e f
  exact congrArg₂ A.diff hu hl

def spanOnDomain (A : AffineData K P) (S : Set P) (h : HasExt S) : K :=
  affineWidth A (Classical.choice h)

theorem span_agrees_with_every_witness (A : AffineData K P) (S : Set P)
    (h : HasExt S) (e : Extrema S) : spanOnDomain A S h = affineWidth A e :=
  width_witness_independent A S (Classical.choice h) e

theorem empty_has_no_extrema : ¬ HasExt (∅ : Set P) := by
  rintro ⟨e⟩
  exact e.lower_mem

theorem singleton_width_zero (A : AffineData K P) (p : P) (e : Extrema ({p} : Set P)) :
    affineWidth A e = 0 := by
  have hl : e.lower = p := e.lower_mem
  have hu : e.upper = p := e.upper_mem
  change A.diff e.upper e.lower = 0
  rw [hl,hu]
  exact difference_reflexive A p

def widthAdmissible (d : Input U D V) (r : Representation d P) (W : D → Set D)
    (A : AffineData K P) (g : {x : K // 0 ≤ x}) : Prop :=
  ∀ i x, ((cellTokens d W i x).Nonempty → HasExt (cellImage d r W i x)) ∧
    ∀ h : HasExt (cellImage d r W i x), spanOnDomain A (cellImage d r W i x) h ≤ g.val

theorem width_admissibility_contract (d : Input U D V) (r : Representation d P)
    (W : D → Set D) (A : AffineData K P) (g : {x : K // 0 ≤ x}) :
    widthAdmissible d r W A g ↔ ∀ i x,
      ((cellTokens d W i x).Nonempty → HasExt (cellImage d r W i x)) ∧
      ∀ e : Extrema (cellImage d r W i x), affineWidth A e ≤ g.val := by
  constructor
  · intro h i x
    refine ⟨(h i x).1, fun e => ?_⟩
    have b := (h i x).2 ⟨e⟩
    exact (span_agrees_with_every_witness A _ ⟨e⟩ e) ▸ b
  · intro h i x
    refine ⟨(h i x).1,fun he => ?_⟩
    exact (h i x).2 (Classical.choice he)

theorem admissible_nonempty_cell_has_bounded_width (d : Input U D V)
    (r : Representation d P) (W : D → Set D) (A : AffineData K P)
    (g : {x : K // 0 ≤ x}) (adm : widthAdmissible d r W A g)
    (i : U) (x : D) (hne : (cellTokens d W i x).Nonempty) :
    ∃ e : Extrema (cellImage d r W i x), 0 ≤ affineWidth A e ∧ affineWidth A e ≤ g.val := by
  obtain ⟨e⟩ := (adm i x).1 hne
  exact ⟨e,width_nonnegative A _ e,((width_admissibility_contract d r W A g).mp adm i x).2 e⟩

variable {C : Type b} {VC : U → Type w}

def associatedRecordImage (d : Input U D V) (r : Representation d P) (W : D → Set D)
    (rel : C → D → Prop) (i : U) (x : C) : Set P :=
  {p | ∃ y : (d.arrival i).dom, rel x y.val ∧ p ∈ cellImage d r W i y.val}

theorem associated_image_nonempty (d : Input U D V) (r : Representation d P)
    (W : D → Set D) (rel : C → D → Prop) (i : U) (x : C) :
    (associatedRecordImage d r W rel i x).Nonempty ↔
      ∃ y : (d.arrival i).dom, rel x y.val ∧ (cellTokens d W i y.val).Nonempty := by
  constructor
  · rintro ⟨p,y,hxy,hp⟩
    exact ⟨y,hxy,(cell_image_nonempty d r W i y.val).mp ⟨p,hp⟩⟩
  · rintro ⟨y,hxy,hy⟩
    obtain ⟨p,hp⟩ := (cell_image_nonempty d r W i y.val).mpr hy
    exact ⟨p,y,hxy,hp⟩

def separates (c : Input U C VC) (cg : GlobalInc c) (d : Input U D V)
    (r : Representation d P) (W : D → Set D) (rel : C → D → Prop) : Prop :=
  ∀ i (x y : (c.arrival i).dom), orderClass c cg i x ≠ orderClass c cg i y →
    (associatedRecordImage d r W rel i x.val).Nonempty ∧
    (associatedRecordImage d r W rel i y.val).Nonempty ∧
    Disjoint (associatedRecordImage d r W rel i x.val) (associatedRecordImage d r W rel i y.val)

theorem separation_exact_contract (c : Input U C VC) (cg : GlobalInc c)
    (d : Input U D V) (r : Representation d P) (W : D → Set D) (rel : C → D → Prop) :
    separates c cg d r W rel ↔ ∀ i (x y : (c.arrival i).dom),
      orderClass c cg i x ≠ orderClass c cg i y →
        (associatedRecordImage d r W rel i x.val).Nonempty ∧
        (associatedRecordImage d r W rel i y.val).Nonempty ∧
        associatedRecordImage d r W rel i x.val ∩ associatedRecordImage d r W rel i y.val = ∅ := by
  simp only [separates,Set.disjoint_iff_inter_eq_empty]

theorem collision_excludes_separation (c : Input U C VC) (cg : GlobalInc c)
    (d : Input U D V) (r : Representation d P) (W : D → Set D) (rel : C → D → Prop)
    (i : U) (x y : (c.arrival i).dom) (hne : orderClass c cg i x ≠ orderClass c cg i y)
    (p : P) (hx : p ∈ associatedRecordImage d r W rel i x.val)
    (hy : p ∈ associatedRecordImage d r W rel i y.val) : ¬ separates c cg d r W rel := by
  intro h
  exact Set.disjoint_left.mp (h i x y hne).2.2 hx hy

theorem missing_record_excludes_separation (c : Input U C VC) (cg : GlobalInc c)
    (d : Input U D V) (r : Representation d P) (W : D → Set D) (rel : C → D → Prop)
    (i : U) (x y : (c.arrival i).dom) (hne : orderClass c cg i x ≠ orderClass c cg i y)
    (empty : associatedRecordImage d r W rel i x.val = ∅) : ¬ separates c cg d r W rel := by
  intro h
  obtain ⟨p,hp⟩ := (h i x y hne).1
  rw [empty] at hp
  exact hp

end
end LCTR.CoreRecordCells
