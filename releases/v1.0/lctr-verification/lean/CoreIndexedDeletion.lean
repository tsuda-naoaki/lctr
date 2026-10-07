import CoreAbstractWordEncoding
import Mathlib.Data.List.TakeDrop

namespace LCTR.CoreIndexedDeletion
open LCTR.CoreAbstractWordEncoding
universe u v
set_option autoImplicit false
variable {U : Type u} {K : Type v}

def terminal (i : U) : List (U × K) → U
  | [] => i
  | (j,_)::es => terminal j es

def slice (es : List (U × K)) (a b : Nat) := (es.drop a).take (b-a)
def erase (es : List (U × K)) (a b : Nat) := es.take a ++ es.drop b
def sourceOnly (src : K) (es : List (U × K)) : Prop := ∀ e ∈ es, e.2=src
def node (i : U) (es : List (U × K)) (r : Nat) := terminal i (es.take r)

theorem terminal_append (i : U) (p q : List (U × K)) :
    terminal i (p++q)=terminal (terminal i p) q := by
  induction p generalizing i with
  | nil => rfl
  | cons e p ih => exact ih e.1

theorem valid_append (adm : K → U → U → Prop) (i j : U) (p q : List (U × K)) :
    validEdges adm i (p++q) j ↔
      validEdges adm i p (terminal i p) ∧ validEdges adm (terminal i p) q j := by
  induction p generalizing i with
  | nil => simp [validEdges,terminal]
  | cons e p ih =>
    obtain ⟨a,k⟩ := e
    simp only [List.cons_append,validEdges,terminal,ih,and_assoc]

theorem cut_decomposition (es : List (U × K)) (a b : Nat) (ab : a ≤ b) :
    (es.take a ++ slice es a b) ++ es.drop b=es := by
  have sum : a+(b-a)=b := Nat.add_sub_of_le ab
  rw [slice,← List.take_add,sum,List.take_append_drop]

theorem cut_lengths (es : List (U × K)) (a b : Nat) (ab : a ≤ b) (bound : b ≤ es.length) :
    (es.take a).length=a ∧ (slice es a b).length=b-a ∧
    (erase es a b).length=es.length-(b-a) := by
  have al : a ≤ es.length := ab.trans bound
  simp only [slice,erase,List.length_append,List.length_take,List.length_drop,
    Nat.min_eq_left al]
  constructor
  · trivial
  constructor
  · omega
  · omega

theorem erased_display (i : U) (es : List (U × K)) (a b : Nat) :
    i::(erase es a b).map Prod.fst =
      i::((es.map Prod.fst).take a ++ (es.map Prod.fst).drop b) ∧
    (erase es a b).map Prod.snd =
      (es.map Prod.snd).take a ++ (es.map Prod.snd).drop b := by
  simp only [erase,List.map_append,List.map_take,List.map_drop]
  exact ⟨trivial,trivial⟩

theorem node_display (i : U) (es : List (U × K)) (r : Nat) (bound : r ≤ es.length) :
    node i es r=(i::es.map Prod.fst)[r]'(by simp; omega) := by
  induction es generalizing i r with
  | nil =>
    have hz : r=0 := by simpa using bound
    subst r
    rfl
  | cons e es ih =>
    cases r with
    | zero => rfl
    | succ r =>
      simpa only [node,List.take_succ_cons,terminal,List.map_cons,List.getElem_cons_succ]
        using ih e.1 r (by simpa using bound)

theorem slice_source_iff (src : K) (es : List (U × K)) (a b : Nat)
    (ab : a ≤ b) (bound : b ≤ es.length) :
    sourceOnly src (slice es a b) ↔
      ∀ n, a≤n → ∀ hb : n<b, (es[n]'(Nat.lt_of_lt_of_le hb bound)).2=src := by
  have len := (cut_lengths es a b ab bound).2.1
  constructor
  · intro only n ha hb
    have hn : n-a < (slice es a b).length := by rw [len]; omega
    have eq := only ((slice es a b)[n-a]) (List.getElem_mem hn)
    simpa only [slice,List.getElem_take,List.getElem_drop,Nat.add_sub_of_le ha] using eq
  · intro all e he
    obtain ⟨n,hn,eq⟩ := List.getElem_of_mem he
    have nb : a+n<b := by rw [len] at hn; omega
    have value := all (a+n) (by omega) nb
    rw [← eq]
    simpa only [slice,List.getElem_take,List.getElem_drop] using value

def IndexedDelete (src : K) (i : U) (es fs : List (U × K)) : Prop :=
  ∃ a b, a<b ∧ b≤es.length ∧ node i es a=node i es b ∧
    sourceOnly src (slice es a b) ∧ fs=erase es a b

def SegmentDelete (src : K) (i : U) (es fs : List (U × K)) : Prop :=
  ∃ p mid q, es=(p++mid)++q ∧ fs=p++q ∧ mid≠[] ∧ sourceOnly src mid ∧
    terminal i p=terminal i (p++mid)

theorem indexed_to_segment (src : K) (i : U) (es fs : List (U × K)) :
    IndexedDelete src i es fs → SegmentDelete src i es fs := by
  rintro ⟨a,b,ab,bound,closed,only,eq⟩
  have al := (cut_lengths es a b ab.le bound).2.1
  have nz : slice es a b ≠ [] := by
    intro h
    rw [h,List.length_nil] at al
    omega
  refine ⟨es.take a,slice es a b,es.drop b,(cut_decomposition es a b ab.le).symm,eq,nz,only,?_⟩
  have sum : a+(b-a)=b := Nat.add_sub_of_le ab.le
  simpa only [node,slice,← List.take_add,sum] using closed

theorem segment_to_indexed (src : K) (i : U) (es fs : List (U × K)) :
    SegmentDelete src i es fs → IndexedDelete src i es fs := by
  rintro ⟨p,mid,q,rfl,rfl,nz,only,closed⟩
  have pos : 0<mid.length := List.length_pos_iff.mpr nz
  have pref : ((p++mid)++q).take p.length=p := by
    rw [List.append_assoc,List.take_append_length]
  have upto : ((p++mid)++q).take (p.length+mid.length)=p++mid := by
    simpa only [List.length_append] using (List.take_append_length (l₁:=p++mid) (l₂:=q))
  have suf : ((p++mid)++q).drop (p.length+mid.length)=q := by
    simpa only [List.length_append] using (List.drop_append_length (l₁:=p++mid) (l₂:=q))
  have middle : slice ((p++mid)++q) p.length (p.length+mid.length)=mid := by
    simp only [slice,Nat.add_sub_cancel_left,List.append_assoc,List.drop_append_length,
      List.take_append_length]
  refine ⟨p.length,p.length+mid.length,by omega,by simp only [List.length_append]; omega,?_,?_,?_⟩
  · simpa only [node,pref,upto] using closed
  · simpa only [middle] using only
  · simp only [erase,pref,suf]

theorem indexed_iff_segment (src : K) (i : U) (es fs : List (U × K)) :
    IndexedDelete src i es fs ↔ SegmentDelete src i es fs :=
  ⟨indexed_to_segment src i es fs,segment_to_indexed src i es fs⟩

theorem deletion_preserves_typing (adm : K → U → U → Prop) (src : K)
    (i j : U) (es fs : List (U × K)) (valid : validEdges adm i es j)
    (del : IndexedDelete src i es fs) : validEdges adm i fs j := by
  obtain ⟨p,mid,q,rfl,rfl,_,_,closed⟩ := indexed_to_segment src i es fs del
  have outer := (valid_append adm i j (p++mid) q).mp valid
  have inner := (valid_append adm i (terminal i (p++mid)) p mid).mp outer.1
  apply (valid_append adm i j p q).mpr
  exact ⟨inner.1,closed ▸ outer.2⟩

theorem no_deletion_equivalence (src : K) (i : U) (es : List (U × K)) :
    (¬∃ fs, IndexedDelete src i es fs) ↔ (¬∃ fs, SegmentDelete src i es fs) := by
  simp only [indexed_iff_segment]

end LCTR.CoreIndexedDeletion
