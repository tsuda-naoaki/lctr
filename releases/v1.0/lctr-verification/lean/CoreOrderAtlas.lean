import CoreUniversalFactorization

namespace LCTR.CoreOrderAtlas
open Set LCTR.OrderEmbeddingBridgeV1 LCTR.TransitiveIncomparabilityQuotientCore
open LCTR.CoreRepresentationImages LCTR.CoreUniversalFactorization
universe u v

structure StrictData (S : Type u) where
  lt : S → S → Prop
  irrefl : ∀ x, ¬ lt x x
  trans : ∀ {x y z}, lt x y → lt y z → lt x z

structure Domain {S : Type u} (d : StrictData S) where
  carrier : Set S
  incTrans : ∀ {x y z : carrier},
    Inc (fun a b : carrier => d.lt a.val b.val) x y →
    Inc (fun a b : carrier => d.lt a.val b.val) y z →
    Inc (fun a b : carrier => d.lt a.val b.val) x z

def restricted {S : Type u} (d : StrictData S) (A : Domain d) (x y : A.carrier) : Prop :=
  d.lt x.val y.val

abbrev Q {S : Type u} (d : StrictData S) (A : Domain d) :=
  IncQuotient (restricted d A) (fun x => d.irrefl x.val) A.incTrans

def projection {S : Type u} (d : StrictData S) (A : Domain d) (x : A.carrier) : Q d A :=
  proj (restricted d A) (fun x => d.irrefl x.val) A.incTrans x

def order {S : Type u} (d : StrictData S) (A : Domain d) : Q d A → Q d A → Prop :=
  quotientLt (restricted d A) (fun x => d.irrefl x.val) A.incTrans

theorem projection_onto {S : Type u} (d : StrictData S) (A : Domain d) :
    Function.Surjective (projection d A) :=
  proj_surjective (restricted d A) (fun x => d.irrefl x.val) A.incTrans

theorem projection_kernel {S : Type u} (d : StrictData S) (A : Domain d) (x y : A.carrier) :
    projection d A x = projection d A y ↔ Inc d.lt x.val y.val :=
  proj_eq_iff_inc (restricted d A) (fun x => d.irrefl x.val) A.incTrans x y

theorem projection_order {S : Type u} (d : StrictData S) (A : Domain d) (x y : A.carrier) :
    order d A (projection d A x) (projection d A y) ↔ d.lt x.val y.val :=
  quotientLt_proj_iff (restricted d A) (fun x => d.irrefl x.val)
    (fun hxy hyz => d.trans hxy hyz) A.incTrans x y

theorem quotient_strict_linear {S : Type u} (d : StrictData S) (A : Domain d) :
    (∀ q, ¬ order d A q q) ∧
    (∀ {x y z}, order d A x y → order d A y z → order d A x z) ∧
    (∀ {x y}, x ≠ y → order d A x y ∨ order d A y x) :=
  quotient_strict_linear_components (restricted d A) (fun x => d.irrefl x.val)
    (fun hxy hyz => d.trans hxy hyz) A.incTrans

def inclusion {S : Type u} (d : StrictData S) (A B : Domain d)
    (h : A.carrier ⊆ B.carrier) : Q d A → Q d B :=
  Quotient.map (fun x : A.carrier => (⟨x.val,h x.property⟩ : B.carrier))
    (fun _ _ hxy => hxy)

theorem inclusion_commutes {S : Type u} (d : StrictData S) (A B : Domain d)
    (h : A.carrier ⊆ B.carrier) (x : A.carrier) :
    inclusion d A B h (projection d A x) = projection d B ⟨x.val,h x.property⟩ := rfl

theorem inclusion_injective {S : Type u} (d : StrictData S) (A B : Domain d)
    (h : A.carrier ⊆ B.carrier) : Function.Injective (inclusion d A B h) := by
  intro p q same
  obtain ⟨x,rfl⟩ := projection_onto d A p
  obtain ⟨y,rfl⟩ := projection_onto d A q
  exact (projection_kernel d A x y).mpr
    ((projection_kernel d B ⟨x.val,h x.property⟩ ⟨y.val,h y.property⟩).mp same)

theorem inclusion_order {S : Type u} (d : StrictData S) (A B : Domain d)
    (h : A.carrier ⊆ B.carrier) (p q : Q d A) :
    order d B (inclusion d A B h p) (inclusion d A B h q) ↔ order d A p q := by
  obtain ⟨x,rfl⟩ := projection_onto d A p
  obtain ⟨y,rfl⟩ := projection_onto d A q
  exact (projection_order d B ⟨x.val,h x.property⟩ ⟨y.val,h y.property⟩).trans
    (projection_order d A x y).symm

theorem inclusion_compose {S : Type u} (d : StrictData S) (A B C : Domain d)
    (h : A.carrier ⊆ B.carrier) (k : B.carrier ⊆ C.carrier) :
    inclusion d B C k ∘ inclusion d A B h = inclusion d A C (fun {_} hx => k (h hx)) := by
  funext p
  obtain ⟨x,rfl⟩ := projection_onto d A p
  rfl

theorem inclusion_unique {S : Type u} (d : StrictData S) (A B : Domain d)
    (h : A.carrier ⊆ B.carrier) (f : Q d A → Q d B)
    (commutes : ∀ x, f (projection d A x) = projection d B ⟨x.val,h x.property⟩) :
    f = inclusion d A B h := by
  funext p
  obtain ⟨x,rfl⟩ := projection_onto d A p
  exact commutes x

theorem composite_chart_contract {S : Type u} {X : Type v} (d : StrictData S)
    (A : Domain d) (receive : X → A.carrier) (onto : Function.Surjective receive) :
    Function.Surjective (projection d A ∘ receive) ∧
    (∀ x y, projection d A (receive x) = projection d A (receive y) ↔
      Inc d.lt (receive x).val (receive y).val) ∧
    (∀ x y, order d A (projection d A (receive x)) (projection d A (receive y)) ↔
      d.lt (receive x).val (receive y).val) :=
  ⟨(projection_onto d A).comp onto, fun x y => projection_kernel d A (receive x) (receive y),
    fun x y => projection_order d A (receive x) (receive y)⟩

abbrev Overlap {S : Type u} {d : StrictData S} (A B : Domain d) :=
  {x : S // x ∈ A.carrier ∧ x ∈ B.carrier}

def leftProjection {S : Type u} (d : StrictData S) (A B : Domain d) (x : Overlap A B) : Q d A :=
  projection d A ⟨x.val,x.property.1⟩

def rightProjection {S : Type u} (d : StrictData S) (A B : Domain d) (x : Overlap A B) : Q d B :=
  projection d B ⟨x.val,x.property.2⟩

theorem overlap_kernel {S : Type u} (d : StrictData S) (A B : Domain d) (x y : Overlap A B) :
    leftProjection d A B x = leftProjection d A B y ↔
    rightProjection d A B x = rightProjection d A B y :=
  (projection_kernel d A ⟨x.val,x.property.1⟩ ⟨y.val,y.property.1⟩).trans
    (projection_kernel d B ⟨x.val,x.property.2⟩ ⟨y.val,y.property.2⟩).symm

noncomputable def overlapChange {S : Type u} (d : StrictData S) (A B : Domain d) :
    range (leftProjection d A B) ≃ range (rightProjection d A B) :=
  imageEquiv (leftProjection d A B) (rightProjection d A B) (overlap_kernel d A B)

theorem overlap_change_commutes {S : Type u} (d : StrictData S) (A B : Domain d) (x : Overlap A B) :
    overlapChange d A B (imageProjection (leftProjection d A B) x) =
      imageProjection (rightProjection d A B) x :=
  imageMap_commutes _ _ (fun x y => (overlap_kernel d A B x y).mp) x

theorem overlap_order {S : Type u} (d : StrictData S) (A B : Domain d)
    (a b : range (leftProjection d A B)) :
    order d B (overlapChange d A B a).val (overlapChange d A B b).val ↔
      order d A a.val b.val := by
  obtain ⟨x,rfl⟩ := imageProjection_surjective (leftProjection d A B) a
  obtain ⟨y,rfl⟩ := imageProjection_surjective (leftProjection d A B) b
  rw [overlap_change_commutes,overlap_change_commutes]
  exact (projection_order d B ⟨x.val,x.property.2⟩ ⟨y.val,y.property.2⟩).trans
    (projection_order d A ⟨x.val,x.property.1⟩ ⟨y.val,y.property.1⟩).symm

theorem native_order_factor {S : Type u} {Y : Type v} (d : StrictData S) (A : Domain d)
    (f : A.carrier → Y) (kernel : ∀ x y, f x = f y ↔ Inc d.lt x.val y.val)
    (lt : Y → Y → Prop) (ord : ∀ x y, lt (f x) (f y) ↔ d.lt x.val y.val) :
    ∃! F : Q d A ≃ range f,
      (∀ x, F (projection d A x) = imageProjection f x) ∧
      (∀ a b, lt (F a).val (F b).val ↔ order d A a b) :=
  quotient_factor_exists_unique (restricted d A) (fun x => d.irrefl x.val)
    (fun hxy hyz => d.trans hxy hyz) A.incTrans f kernel lt ord

theorem inverse_change_commutes {S : Type u} (d : StrictData S) (A B : Domain d)
    (x : Overlap A B) :
    (overlapChange d A B).symm (imageProjection (rightProjection d A B) x) =
      imageProjection (leftProjection d A B) x := by
  rw [← overlap_change_commutes d A B x, Equiv.symm_apply_apply]

theorem self_change_identity {S : Type u} (d : StrictData S) (A : Domain d)
    (p : range (leftProjection d A A)) : (overlapChange d A A p).val = p.val := by
  obtain ⟨x,rfl⟩ := imageProjection_surjective (leftProjection d A A) p
  rw [overlap_change_commutes]
  rfl

noncomputable def continueOverlap {S : Type u} (d : StrictData S) (A B C : Domain d)
    (x : S) (ha : x ∈ A.carrier) (hb : x ∈ B.carrier) (hc : x ∈ C.carrier) :
    range (leftProjection d B C) :=
  ⟨(overlapChange d A B (imageProjection (leftProjection d A B) ⟨x,ha,hb⟩)).val,
    ⟨⟨x,hb,hc⟩, by rw [overlap_change_commutes]; rfl⟩⟩

theorem continue_overlap_exact {S : Type u} (d : StrictData S) (A B C : Domain d)
    (x : S) (ha : x ∈ A.carrier) (hb : x ∈ B.carrier) (hc : x ∈ C.carrier) :
    continueOverlap d A B C x ha hb hc = imageProjection (leftProjection d B C) ⟨x,hb,hc⟩ := by
  apply Subtype.ext
  change (overlapChange d A B (imageProjection (leftProjection d A B) ⟨x,ha,hb⟩)).val = _
  rw [overlap_change_commutes]
  rfl

theorem triple_overlap_cocycle {S : Type u} (d : StrictData S) (A B C : Domain d)
    (x : S) (ha : x ∈ A.carrier) (hb : x ∈ B.carrier) (hc : x ∈ C.carrier) :
    (overlapChange d B C (continueOverlap d A B C x ha hb hc)).val =
      (overlapChange d A C (imageProjection (leftProjection d A C) ⟨x,ha,hc⟩)).val := by
  rw [continue_overlap_exact, overlap_change_commutes, overlap_change_commutes]
  rfl

end LCTR.CoreOrderAtlas
