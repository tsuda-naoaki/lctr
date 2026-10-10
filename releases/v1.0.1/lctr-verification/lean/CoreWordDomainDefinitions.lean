import CoreTypedWords

namespace LCTR.CoreWordDomainDefinitions
set_option autoImplicit false
open Set LCTR.CoreTypedWords
universe u v w
variable {X : Type v} {U : Type u} {Y : U → Type v}

def relationDomain (r : X → X → Prop) : Set X := {x | ∃ y, r x y}
def relationFix (r : X → X → Prop) : Set X := {x | r x x}

theorem fix_subset_domain (r : X → X → Prop) : relationFix r ⊆ relationDomain r :=
  fun x h => ⟨x,h⟩

theorem identity_iff_fixed_domain (r : X → X → Prop)
    (functional : ∀ x y z, r x y → r x z → y=z) :
    relationFix r = relationDomain r ↔ ∀ x y, r x y → y=x := by
  constructor
  · intro eq x y h
    have hd : x ∈ relationDomain r := ⟨y,h⟩
    have hf : r x x := by rw [← eq] at hd; exact hd
    exact functional x y x h hf
  · intro identity
    apply Set.Subset.antisymm (fix_subset_domain r)
    rintro x ⟨y,h⟩
    have eq := identity x y h
    subst y
    exact h

theorem empty_identity :
    relationFix (fun (_ _ : X) => False) = relationDomain (fun (_ _ : X) => False) := by
  ext x
  simp [relationFix,relationDomain]

theorem loop_identity_exact (W : System.{u,v,w} U Y) :
    LoopIdentity W ↔ ∀ i (p : Word W i i), relationFix p.action = relationDomain p.action := by
  constructor
  · intro h i p
    apply (identity_iff_fixed_domain p.action (action_functional p)).mpr
    exact fun x y hxy => (h i p x y hxy).symm
  · intro h i p x y hxy
    exact ((identity_iff_fixed_domain p.action (action_functional p)).mp (h i p) x y hxy).symm

def erasedOrbit (A : U → Set X) (W : System U (fun i => A i)) (x y : X) : Prop :=
  ∃ p q : Sigma (fun i => A i), p.2.val=x ∧ q.2.val=y ∧ Orbit W p q

theorem erased_orbit_word_witness (A : U → Set X) (W : System U (fun i => A i)) (x y : X) :
    erasedOrbit A W x y ↔
      ∃ i j, ∃ (hx : x ∈ A i) (hy : y ∈ A j),
        ∃ p : Word W i j, p.action ⟨x,hx⟩ ⟨y,hy⟩ := by
  constructor
  · rintro ⟨⟨i,⟨x,hx⟩⟩,⟨j,⟨y,hy⟩⟩,rfl,rfl,p,h⟩
    exact ⟨i,j,hx,hy,p,h⟩
  · rintro ⟨i,j,hx,hy,p,h⟩
    exact ⟨⟨i,⟨x,hx⟩⟩,⟨j,⟨y,hy⟩⟩,rfl,rfl,p,h⟩

theorem erased_orbit_exact_if_disjoint (A : U → Set X) (W : System U (fun i => A i))
    (disj : ∀ i j x, x ∈ A i → x ∈ A j → i=j)
    (p q : Sigma (fun i => A i)) : erasedOrbit A W p.2.val q.2.val ↔ Orbit W p q := by
  constructor
  · rintro ⟨a,b,ha,hb,hab⟩
    have ap : a=p := (disjoint_union_tag_bridge A disj).1 (Subtype.ext ha)
    have bq : b=q := (disjoint_union_tag_bridge A disj).1 (Subtype.ext hb)
    subst a
    subst b
    exact hab
  · intro h
    exact ⟨p,q,rfl,rfl,h⟩

def restricted (W : System.{u,v,w} U Y)
    (P : ∀ {i j}, W.Atom i j → Prop)
    (stable : ∀ {i j} (a : W.Atom i j), P a → P (W.reverse a)) : System U Y where
  Atom i j := {a : W.Atom i j // P a}
  reverse a := ⟨W.reverse a.val,stable a.val a.property⟩
  reverse_reverse a := Subtype.ext (W.reverse_reverse a.val)
  act a := W.act a.val
  functional a := W.functional a.val
  reverse_graph a := W.reverse_graph a.val

theorem restricted_action (W : System.{u,v,w} U Y)
    (P : ∀ {i j}, W.Atom i j → Prop)
    (stable : ∀ {i j} (a : W.Atom i j), P a → P (W.reverse a))
    {i j : U} (a : (restricted W P stable).Atom i j) (x : Y i) (y : Y j) :
    (restricted W P stable).act a x y ↔ W.act a.val x y := Iff.rfl

theorem restricted_inverse (W : System.{u,v,w} U Y)
    (P : ∀ {i j}, W.Atom i j → Prop)
    (stable : ∀ {i j} (a : W.Atom i j), P a → P (W.reverse a))
    {i j : U} (a : (restricted W P stable).Atom i j) :
    ((restricted W P stable).reverse a).val = W.reverse a.val ∧
    (restricted W P stable).reverse ((restricted W P stable).reverse a)=a :=
  ⟨rfl,(restricted W P stable).reverse_reverse a⟩

end LCTR.CoreWordDomainDefinitions
