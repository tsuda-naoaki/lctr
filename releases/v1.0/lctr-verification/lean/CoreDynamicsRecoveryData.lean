import CoreDynamicsInterfaces

namespace LCTR.CoreDynamicsRecoveryData
open Set LCTR.CoreDynamicsInterfaces LCTR.CoreSourceMatch LCTR.Chapter03SourceOrderRecovery
universe u v w
set_option autoImplicit false

variable {R : Type u} {S : R → Type v} {V : R → Type w}

structure Recovery (arr : ArrivalFamily R S V) where
  map : ∀ r, ImageAt (fun (_ : Unit) => arr r) () → {s // s ∈ (arr r).dom}
  rightInverse : ∀ r a, (arr r).val (map r a).val (map r a).property = a.val

noncomputable def chooseRecovery (arr : ArrivalFamily R S V) : Recovery arr where
  map := fun _ a => Classical.choose a.property
  rightInverse := fun _ a => Classical.choose_spec a.property

theorem recovery_exists (arr : ArrivalFamily R S V) : Nonempty (Recovery arr) :=
  ⟨chooseRecovery arr⟩

variable (x : ReceptionData R S V) (rec : Recovery x.arrival)

def recover (a : ArrivalTuple x.arrival) : ∀ r, S r := fun r => (rec.map r (a r)).val

theorem recovery_domain (r : R) (a : ArrivalTuple x.arrival) :
    recover x rec a r ∈ (x.arrival r).dom := (rec.map r (a r)).property

theorem recovery_right_inverse (r : R) (a : ArrivalTuple x.arrival) :
    (x.arrival r).val (recover x rec a r) (recovery_domain x rec r a) = (a r).val :=
  rec.rightInverse r (a r)

theorem recovery_injective : Function.Injective (recover x rec) := by
  intro a b h
  funext r
  apply Subtype.ext
  have hr := congrFun h r
  have eq := congrArg (fun t : {s // s ∈ (x.arrival r).dom} =>
    (x.arrival r).val t.val t.property) (Subtype.ext hr)
  exact (rec.rightInverse r (a r)).symm.trans (eq.trans (rec.rightInverse r (b r)))

def localBinding (bind : ArrivalTuple x.arrival → ArrivalTuple x.arrival → Prop)
    (a b : ArrivalTuple x.arrival) : Prop :=
  a ∈ x.localRelation ∧ b ∈ x.localRelation ∧ bind a b

def sourceBinding (bind : ArrivalTuple x.arrival → ArrivalTuple x.arrival → Prop)
    (s t : ∀ r, S r) : Prop :=
  s ∈ x.sourceRelation ∧ t ∈ x.sourceRelation ∧
    ∃ a b, localBinding x bind a b ∧ recover x rec a = s ∧ recover x rec b = t

theorem local_binding_exact (bind : ArrivalTuple x.arrival → ArrivalTuple x.arrival → Prop)
    (a b : ArrivalTuple x.arrival) :
    localBinding x bind a b ↔ a ∈ x.localRelation ∧ b ∈ x.localRelation ∧ bind a b := Iff.rfl

theorem source_binding_typed (bind : ArrivalTuple x.arrival → ArrivalTuple x.arrival → Prop)
    (s t : ∀ r, S r) (h : sourceBinding x rec bind s t) :
    s ∈ x.sourceRelation ∧ t ∈ x.sourceRelation := ⟨h.1,h.2.1⟩

theorem source_binding_exact (bind : ArrivalTuple x.arrival → ArrivalTuple x.arrival → Prop)
    (s t : ∀ r, S r) : sourceBinding x rec bind s t ↔
    s ∈ x.sourceRelation ∧ t ∈ x.sourceRelation ∧
    ∃ a b, localBinding x bind a b ∧ recover x rec a = s ∧ recover x rec b = t := Iff.rfl

theorem source_binding_pullback (bind : ArrivalTuple x.arrival → ArrivalTuple x.arrival → Prop)
    (a b : ArrivalTuple x.arrival) :
    sourceBinding x rec bind (recover x rec a) (recover x rec b) ↔
    recover x rec a ∈ x.sourceRelation ∧ recover x rec b ∈ x.sourceRelation ∧
    localBinding x bind a b := by
  constructor
  · rintro ⟨ha,hb,c,d,hcd,hca,hdb⟩
    have ca := recovery_injective x rec hca
    have db := recovery_injective x rec hdb
    subst c; subst d
    exact ⟨ha,hb,hcd⟩
  · rintro ⟨ha,hb,hab⟩
    exact ⟨ha,hb,a,b,hab,rfl,rfl⟩

def generated (bind : ArrivalTuple x.arrival → ArrivalTuple x.arrival → Prop)
    (r : R) (s t : S r) : Prop :=
  ∃ a b, sourceBinding x rec bind a b ∧ a r = s ∧ b r = t

theorem generated_exact (bind : ArrivalTuple x.arrival → ArrivalTuple x.arrival → Prop)
    (r : R) (s t : S r) : generated x rec bind r s t ↔
    ∃ a ∈ x.sourceRelation, ∃ b ∈ x.sourceRelation,
      sourceBinding x rec bind a b ∧ a r = s ∧ b r = t := by
  constructor
  · rintro ⟨a,b,h,hs,ht⟩
    exact ⟨a,h.1,b,h.2.1,h,hs,ht⟩
  · rintro ⟨a,_,b,_,h,hs,ht⟩
    exact ⟨a,b,h,hs,ht⟩

theorem generated_endpoint_arrived
    (bind : ArrivalTuple x.arrival → ArrivalTuple x.arrival → Prop)
    (r : R) (s t : S r) (h : generated x rec bind r s t) :
    s ∈ (x.arrival r).dom ∧ t ∈ (x.arrival r).dom := by
  obtain ⟨a,b,⟨_,_,c,d,_,rfl,rfl⟩,rfl,rfl⟩ := h
  exact ⟨recovery_domain x rec r c,recovery_domain x rec r d⟩

def package {Q : Type} (role : Q → R)
    (bind : ArrivalTuple x.arrival → ArrivalTuple x.arrival → Prop)
    (closure : ∀ q, S (role q) → S (role q) → Prop) :=
  (x,rec,localBinding x bind,sourceBinding x rec bind,
    fun q => (generated x rec bind (role q),closure q))

theorem package_components {Q : Type} (role : Q → R)
    (bind : ArrivalTuple x.arrival → ArrivalTuple x.arrival → Prop)
    (closure : ∀ q, S (role q) → S (role q) → Prop) :
    (package x rec role bind closure).1 = x ∧
    (package x rec role bind closure).2.1 = rec ∧
    (package x rec role bind closure).2.2.1 = localBinding x bind ∧
    (package x rec role bind closure).2.2.2.1 = sourceBinding x rec bind ∧
    (package x rec role bind closure).2.2.2.2 =
      (fun q => (generated x rec bind (role q),closure q)) := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem right_inverse_not_injectivity :
    (∀ a : Unit, (fun _ : Bool => ()) ((fun _ : Unit => false) a) = a) ∧
    ¬Function.Injective (fun _ : Bool => ()) := by
  constructor
  · intro a; cases a; rfl
  · intro h
    have hf : (false : Bool) = true := h rfl
    cases hf

end LCTR.CoreDynamicsRecoveryData
