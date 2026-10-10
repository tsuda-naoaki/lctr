import Mathlib.Data.Set.Prod

namespace LCTR.CoreJointInputData
set_option autoImplicit false
open Set
universe u v w z

structure SourceData (Z : Type u) (B : Type v) (V : Type w) where
  domain : Set (Z → B)
  relation : Set ((Z → B) × V)
  typed : ∀ p ∈ relation, p.1 ∈ domain

variable {Z : Type u} {B : Type v} {V : Type w}

def emptyData (A : Set (Z → B)) : SourceData Z B V := ⟨A,∅,by simp⟩

theorem relation_domain (d : SourceData Z B V) (x : Z → B) (v : V)
    (h : (x,v) ∈ d.relation) : x ∈ d.domain := d.typed _ h

theorem source_components (d : SourceData Z B V) :
    (d.domain,d.relation).1 = d.domain ∧ (d.domain,d.relation).2 = d.relation := ⟨rfl,rfl⟩

theorem empty_relation_allowed (A : Set (Z → B)) :
    (emptyData (V := V) A).domain = A ∧ (emptyData (V := V) A).relation = ∅ := ⟨rfl,rfl⟩

def predicateData (A : Set (Z → B)) (P : (Z → B) → Prop)
    (typed : ∀ x, P x → x ∈ A) : SourceData Z B Unit :=
  ⟨A,{p | P p.1},fun p hp => typed p.1 hp⟩

theorem predicate_membership (A : Set (Z → B)) (P : (Z → B) → Prop)
    (typed : ∀ x, P x → x ∈ A) (x : Z → B) :
    (x,()) ∈ (predicateData A P typed).relation ↔ P x := Iff.rfl

theorem predicate_value_unique (v : Unit) : v = () := Subsingleton.elim _ _

structure JointData (Context : Type u) (Roles : Context → Type v)
    (Z : Type w) (B : Type z) (R : Type) (Value : R → Type) where
  context : Context
  roles : Roles context
  indices : Set R
  indicesNonempty : indices.Nonempty
  datum : ∀ r : indices, SourceData Z B (Value r.val)

variable {Context : Type u} {Roles : Context → Type v}
variable {R : Type} {Value : R → Type} {Z' : Type w} {B' : Type z}

def assemble (ctx : Context) (roles : Roles ctx) (indices : Set R)
    (hne : indices.Nonempty) (data : ∀ r : indices, SourceData Z' B' (Value r.val)) :
    JointData Context Roles Z' B' R Value := ⟨ctx,roles,indices,hne,data⟩

theorem bundle_context (ctx : Context) (roles : Roles ctx) (indices : Set R)
    (hne : indices.Nonempty) (data : ∀ r : indices, SourceData Z' B' (Value r.val)) :
    (assemble ctx roles indices hne data).context = ctx := rfl

theorem bundle_roles (ctx : Context) (roles : Roles ctx) (indices : Set R)
    (hne : indices.Nonempty) (data : ∀ r : indices, SourceData Z' B' (Value r.val)) :
    (assemble ctx roles indices hne data).roles = roles := rfl

theorem bundle_indices (ctx : Context) (roles : Roles ctx) (indices : Set R)
    (hne : indices.Nonempty) (data : ∀ r : indices, SourceData Z' B' (Value r.val)) :
    (assemble ctx roles indices hne data).indices = indices := rfl

theorem bundle_datum (ctx : Context) (roles : Roles ctx) (indices : Set R)
    (hne : indices.Nonempty) (data : ∀ r : indices, SourceData Z' B' (Value r.val))
    (r : indices) : (assemble ctx roles indices hne data).datum r = data r := rfl

theorem selected_index_exists (d : JointData Context Roles Z' B' R Value) :
    ∃ r, r ∈ d.indices := d.indicesNonempty

theorem indexed_relation_domain (d : JointData Context Roles Z' B' R Value)
    (r : d.indices) (x : Z' → B') (v : Value r.val)
    (h : (x,v) ∈ (d.datum r).relation) : x ∈ (d.datum r).domain :=
  relation_domain (d.datum r) x v h

theorem empty_value_relation (d : SourceData Z B Empty) : d.relation = ∅ := by
  ext p
  exact p.2.elim

theorem relation_not_forced_total :
    ∃ d : SourceData Unit Unit Unit, d.domain.Nonempty ∧ d.relation = ∅ :=
  ⟨emptyData Set.univ,⟨fun _ => (),Set.mem_univ _⟩,rfl⟩

end LCTR.CoreJointInputData
