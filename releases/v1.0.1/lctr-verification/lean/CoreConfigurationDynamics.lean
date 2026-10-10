import CoreOperationalConfiguration
import CoreSourceMatch

namespace LCTR.CoreConfigurationDynamics
set_option autoImplicit false
open Set LCTR.CoreOperationalConfiguration LCTR.CoreSourceMatch

variable (x : Configuration) (o : x.1.reception.Node)
abbrev direct (r : SourceRole) (_ : Unit) := x.2.arrival o r
abbrev SourceTuple := (r : SourceRole) → Token x.2.schema r
abbrev DomainTuple := (r : SourceRole) → {t // t ∈ (x.2.arrival o r).dom}
abbrev ReceivedTuple := (r : SourceRole) → ImageAt (direct x o r) ()
def Unique : Prop := ∀ r, L1 (direct x o r)

def forget (a : DomainTuple x o) : SourceTuple x := fun r => (a r).val
def receive (a : DomainTuple x o) : ReceivedTuple x o :=
  fun r => ⟨(x.2.arrival o r).val (a r).val (a r).property, ⟨a r,rfl⟩⟩
noncomputable def recoverTuple (h : Unique x o) (a : ReceivedTuple x o) : DomainTuple x o :=
  fun r => localRecovery (direct x o r) (h r) () (a r)

variable (h : Unique x o)
theorem receive_recover (a : ReceivedTuple x o) :
    receive x o (recoverTuple x o h a) = a := by
  funext r
  exact Subtype.ext (arrival_recovery (direct x o r) (h r) () (a r))

theorem recover_receive (a : DomainTuple x o) :
    recoverTuple x o h (receive x o a) = a := by
  funext r
  apply (l1_iff_injective (direct x o r)).mp (h r) ()
  exact arrival_recovery (direct x o r) (h r) () (receive x o a r)

theorem recovered_source_injective :
    Function.Injective (fun a : ReceivedTuple x o => forget x o (recoverTuple x o h a)) := by
  intro a b same
  funext r
  exact recovery_injective (direct x o r) (h r) () (congrFun same r)

theorem received_body_source_position (a : DomainTuple x o) :
    x.2.schema.bodyPosition (forget x o (recoverTuple x o h (receive x o a)) .body) =
      x.2.schema.bodyPosition (a .body).val := by
  rw [recover_receive]
  rfl

def ExactDescent (R : Set (SourceTuple x)) (L : Set (ReceivedTuple x o)) : Prop :=
  L = receive x o '' {a : DomainTuple x o | forget x o a ∈ R}

theorem exact_descent_pullback (R : Set (SourceTuple x)) (L : Set (ReceivedTuple x o))
    (hd : ExactDescent x o R L) (a : ReceivedTuple x o) :
    a ∈ L ↔ forget x o (recoverTuple x o h a) ∈ R := by
  rw [hd]
  constructor
  · rintro ⟨p,hp,rfl⟩
    rw [recover_receive]
    exact hp
  · intro ha
    exact ⟨recoverTuple x o h a,ha,receive_recover x o h a⟩

def sourceBinding (L : Set (ReceivedTuple x o))
    (bind : ReceivedTuple x o → ReceivedTuple x o → Prop)
    (s t : SourceTuple x) : Prop :=
  ∃ a ∈ L, ∃ b ∈ L, bind a b ∧ forget x o (recoverTuple x o h a)=s ∧
    forget x o (recoverTuple x o h b)=t

theorem source_binding_typed (R : Set (SourceTuple x)) (L : Set (ReceivedTuple x o))
    (hd : ExactDescent x o R L) (bind : ReceivedTuple x o → ReceivedTuple x o → Prop)
    (s t : SourceTuple x) (hb : sourceBinding x o h L bind s t) : s∈R ∧ t∈R := by
  obtain ⟨a,ha,b,hb,_,rfl,rfl⟩ := hb
  exact ⟨(exact_descent_pullback x o h R L hd a).mp ha,
    (exact_descent_pullback x o h R L hd b).mp hb⟩

theorem source_binding_pullback (L : Set (ReceivedTuple x o))
    (bind : ReceivedTuple x o → ReceivedTuple x o → Prop) (a b : ReceivedTuple x o) :
    sourceBinding x o h L bind (forget x o (recoverTuple x o h a))
      (forget x o (recoverTuple x o h b)) ↔ a∈L ∧ b∈L ∧ bind a b := by
  constructor
  · rintro ⟨c,hc,d,hd,he,ca,db⟩
    have ac := recovered_source_injective x o h ca
    have bd := recovered_source_injective x o h db
    subst c
    subst d
    exact ⟨hc,hd,he⟩
  · rintro ⟨ha,hb,hab⟩
    exact ⟨a,ha,b,hb,hab,rfl,rfl⟩

def generated (R : Set (SourceTuple x)) (L : Set (ReceivedTuple x o))
    (bind : ReceivedTuple x o → ReceivedTuple x o → Prop) (r : SourceRole)
    (s t : Token x.2.schema r) : Prop :=
  ∃ a ∈ R, ∃ b ∈ R, sourceBinding x o h L bind a b ∧ a r=s ∧ b r=t

theorem generated_is_local_binding_image (R : Set (SourceTuple x))
    (L : Set (ReceivedTuple x o)) (hd : ExactDescent x o R L)
    (bind : ReceivedTuple x o → ReceivedTuple x o → Prop) (r : SourceRole)
    (s t : Token x.2.schema r) :
    generated x o h R L bind r s t ↔
      ∃ a ∈ L, ∃ b ∈ L, bind a b ∧
        (forget x o (recoverTuple x o h a)) r=s ∧
        (forget x o (recoverTuple x o h b)) r=t := by
  constructor
  · rintro ⟨p,_,q,_,⟨a,ha,b,hb,hab,rfl,rfl⟩,ps,qt⟩
    exact ⟨a,ha,b,hb,hab,ps,qt⟩
  · rintro ⟨a,ha,b,hb,hab,hs,ht⟩
    exact ⟨_,(exact_descent_pullback x o h R L hd a).mp ha,
      _,(exact_descent_pullback x o h R L hd b).mp hb,
      ⟨a,ha,b,hb,hab,rfl,rfl⟩,hs,ht⟩

theorem generated_endpoint_arrived (R : Set (SourceTuple x))
    (L : Set (ReceivedTuple x o)) (hd : ExactDescent x o R L)
    (bind : ReceivedTuple x o → ReceivedTuple x o → Prop) (r : SourceRole)
    (s t : Token x.2.schema r) (hg : generated x o h R L bind r s t) :
    s ∈ (x.2.arrival o r).dom ∧ t ∈ (x.2.arrival o r).dom := by
  obtain ⟨a,_,b,_,_,hs,ht⟩ := (generated_is_local_binding_image x o h R L hd bind r s t).mp hg
  exact ⟨hs ▸ (recoverTuple x o h a r).property,ht ▸ (recoverTuple x o h b r).property⟩

end LCTR.CoreConfigurationDynamics
