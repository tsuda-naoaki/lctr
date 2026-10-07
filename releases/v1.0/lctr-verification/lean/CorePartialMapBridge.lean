import Mathlib.Data.Set.Basic

namespace LCTR.CorePartialMapBridge
open Set
set_option autoImplicit false
universe u v w
variable {A : Type u} {B : Type v} {C : Type w}

structure PartialMap (A : Type u) (B : Type v) where
  domain : Set A
  value : domain → B

def graph (f : PartialMap A B) (a : A) (b : B) : Prop :=
  ∃ h : a ∈ f.domain, f.value ⟨a,h⟩ = b

def compose (r : A → B → Prop) (s : B → C → Prop) (a : A) (c : C) : Prop :=
  ∃ b, r a b ∧ s b c

theorem map_graph_domain (f : PartialMap A B) (a : A) :
    (∃ b, graph f a b) ↔ a ∈ f.domain := by
  constructor
  · rintro ⟨b,h,e⟩
    exact h
  · intro h
    exact ⟨f.value ⟨a,h⟩,h,rfl⟩

theorem map_graph_value (f : PartialMap A B) (a : f.domain) (b : B) :
    graph f a.val b ↔ f.value a = b := by
  constructor
  · rintro ⟨h,e⟩
    exact e
  · intro e
    exact ⟨a.property,e⟩

theorem general_composition_domain (r : A → B → Prop) (s : B → C → Prop) (a : A) :
    (∃ c, compose r s a c) ↔ ∃ b, r a b ∧ ∃ c, s b c := by
  constructor
  · rintro ⟨c,b,hr,hs⟩
    exact ⟨b,hr,c,hs⟩
  · rintro ⟨b,hr,c,hs⟩
    exact ⟨c,b,hr,hs⟩

theorem partial_map_composition (f : PartialMap A B) (g : PartialMap B C) (a : A) (c : C) :
    compose (graph f) (graph g) a c ↔
      ∃ (ha : a ∈ f.domain) (hb : f.value ⟨a,ha⟩ ∈ g.domain),
        g.value ⟨f.value ⟨a,ha⟩,hb⟩ = c := by
  constructor
  · rintro ⟨b,⟨ha,e⟩,⟨hb,hc⟩⟩
    subst b
    exact ⟨ha,hb,hc⟩
  · rintro ⟨ha,hb,hc⟩
    exact ⟨f.value ⟨a,ha⟩,⟨ha,rfl⟩,⟨hb,hc⟩⟩

theorem composition_functional (f : PartialMap A B) (g : PartialMap B C)
    (a : A) (c d : C) (hc : compose (graph f) (graph g) a c)
    (hd : compose (graph f) (graph g) a d) : c=d := by
  obtain ⟨ha,hb,hc⟩ := (partial_map_composition f g a c).mp hc
  obtain ⟨ha',hb',hd⟩ := (partial_map_composition f g a d).mp hd
  exact hc.symm.trans hd

theorem empty_domain_composition (f : PartialMap A B) (g : PartialMap B C)
    (empty : f.domain = ∅) (a : A) (c : C) :
    ¬ compose (graph f) (graph g) a c := by
  rintro ⟨b,⟨ha,_⟩,_⟩
  rw [empty] at ha
  exact ha

def collapsing : PartialMap Bool Unit := ⟨univ,fun _ => ()⟩
def unitIdentity : PartialMap Unit Unit := ⟨univ,fun x => x.val⟩

theorem noninjective_composition_control :
    compose (graph collapsing) (graph unitIdentity) false () ∧
    compose (graph collapsing) (graph unitIdentity) true () ∧ false ≠ true := by
  exact ⟨⟨(),⟨trivial,rfl⟩,⟨trivial,rfl⟩⟩,
    ⟨(),⟨trivial,rfl⟩,⟨trivial,rfl⟩⟩,Bool.false_ne_true⟩

end LCTR.CorePartialMapBridge
