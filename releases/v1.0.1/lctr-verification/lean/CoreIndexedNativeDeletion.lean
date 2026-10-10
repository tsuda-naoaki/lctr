import CoreIndexedDeletion
import CoreWordEncoding

namespace LCTR.CoreIndexedNativeDeletion
open LCTR.CoreSourceLoops LCTR.CoreSourceMatch LCTR.CoreAbstractWordEncoding
open LCTR.CoreIndexedDeletion
universe u v w
set_option autoImplicit false
variable {U : Type u} {S : Type v} {V : U → Type w}
variable {d : CoreSourceLoops.Data U S V} {i j k : U}

def view (p : Path d i j) : List (U × Kind) := CoreWordEncoding.edges (CoreWordEncoding.decode p)

theorem view_valid (p : Path d i j) : validEdges (Admissible d.admissible) i (view p) j := by
  induction p with
  | nil => rfl
  | cons e p ih => exact ⟨e.property,ih⟩

theorem view_reconstruction (es : List (U × Kind))
    (h : validEdges (Admissible d.admissible) i es j) : ∃ p : Path d i j, view p=es := by
  induction es generalizing i with
  | nil =>
    change i=j at h
    subst j
    exact ⟨.nil i,rfl⟩
  | cons e es ih =>
    obtain ⟨a,kind⟩ := e
    obtain ⟨hk,ht⟩ := h
    obtain ⟨p,hp⟩ := ih ht
    exact ⟨.cons ⟨kind,hk⟩ p,by simpa only [view,CoreWordEncoding.decode,CoreWordEncoding.edges] using congrArg (List.cons (a,kind)) hp⟩

theorem view_injective : Function.Injective (view : Path d i j → List (U × Kind)) := by
  intro p q h
  have raw := CoreWordEncoding.edges_injective (CoreWordEncoding.decode p) (CoreWordEncoding.decode q) h
  have eq := congrArg CoreWordEncoding.encode raw
  simpa only [CoreWordEncoding.encode_decode] using eq

theorem view_append (p : Path d i j) (q : Path d j k) : view (p.append q)=view p++view q := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    simpa only [view,CoreWordEncoding.decode,CoreWordEncoding.edges,CoreTypedWords.Word.append,
      List.cons_append] using congrArg (List.cons (_,e.val)) (ih q)

theorem view_length (p : Path d i j) : (view p).length=length p := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    change (view p).length+1=1+length p
    rw [ih,Nat.add_comm]

theorem view_source (p : Path d i j) : SourceOnly p ↔ sourceOnly Kind.src (view p) := by
  induction p with
  | nil => simp [SourceOnly,sourceOnly,view,CoreWordEncoding.decode,CoreWordEncoding.edges]
  | cons e p ih =>
    simp only [SourceOnly,ih,view,CoreWordEncoding.decode,CoreWordEncoding.edges,
      sourceOnly,List.mem_cons,forall_eq_or_imp]

theorem view_terminal (p : Path d i j) : terminal i (view p)=j := by
  induction p with
  | nil => rfl
  | cons e p ih => exact ih

theorem native_to_indexed (p q : Path d i k) (h : Delete d p q) :
    IndexedDelete Kind.src i (view p) (view q) := by
  apply (indexed_iff_segment Kind.src i (view p) (view q)).mpr
  cases h with
  | segment p mid q hs positive =>
    have nz : view mid ≠ [] := by
      intro h
      have len := view_length mid
      rw [h,List.length_nil] at len
      omega
    refine ⟨view p,view mid,view q,?_,view_append p q,nz,(view_source mid).mp hs,?_⟩
    · simp only [view_append]
    · rw [← view_append,view_terminal,view_terminal]

theorem indexed_to_native (p q : Path d i k)
    (h : IndexedDelete Kind.src i (view p) (view q)) : Delete d p q := by
  obtain ⟨a,mid,c,ep,eq,nz,only,closed⟩ := indexed_to_segment Kind.src i (view p) (view q) h
  have valid : validEdges (Admissible d.admissible) i ((a++mid)++c) k := ep ▸ view_valid p
  have outer := (valid_append (Admissible d.admissible) i k (a++mid) c).mp valid
  have inner := (valid_append (Admissible d.admissible) i (terminal i (a++mid)) a mid).mp outer.1
  have mid_typed : validEdges (Admissible d.admissible) (terminal i a) mid (terminal i a) :=
    closed.symm ▸ inner.2
  have tail_typed : validEdges (Admissible d.admissible) (terminal i a) c k :=
    closed.symm ▸ outer.2
  obtain ⟨pa,ha⟩ := view_reconstruction a inner.1
  obtain ⟨pm,hm⟩ := view_reconstruction mid mid_typed
  obtain ⟨pc,hc⟩ := view_reconstruction c tail_typed
  have hp : (pa.append pm).append pc=p := by
    apply view_injective
    simp only [view_append,ha,hm,hc,ep]
  have hq : pa.append pc=q := by
    apply view_injective
    simp only [view_append,ha,hc,eq]
  have hs : SourceOnly pm := (view_source pm).mpr (hm.symm ▸ only)
  have hn : 0<length pm := by
    rw [← view_length,hm]
    exact List.length_pos_iff.mpr nz
  simpa only [hp,hq] using Delete.segment pa pm pc hs hn

theorem native_delete_iff (p q : Path d i k) :
    Delete d p q ↔ IndexedDelete Kind.src i (view p) (view q) :=
  ⟨native_to_indexed p q,indexed_to_native p q⟩

theorem irreducible_iff_no_indexed (p : Path d i k) :
    Irreducible p ↔ ¬∃ fs, IndexedDelete Kind.src i (view p) fs := by
  constructor
  · intro h hp
    obtain ⟨fs,hf⟩ := hp
    have typed := deletion_preserves_typing (Admissible d.admissible) Kind.src i k (view p) fs (view_valid p) hf
    obtain ⟨q,hq⟩ := view_reconstruction fs typed
    exact h ⟨q,indexed_to_native p q (hq.symm ▸ hf)⟩
  · intro h hp
    obtain ⟨q,hq⟩ := hp
    exact h ⟨view q,native_to_indexed p q hq⟩

theorem indexed_action_extension (p q : Path d i k)
    (h : IndexedDelete Kind.src i (view p) (view q)) (a : ImageAt d.arrival i) (b : ImageAt d.arrival k) :
    p.action a b → q.action a b := deletion_extends_action d (indexed_to_native p q h) a b

theorem indexed_exact_on_old_domain (p q : Path d i k)
    (h : IndexedDelete Kind.src i (view p) (view q)) (a : ImageAt d.arrival i)
    (ha : p.domain a) (b : ImageAt d.arrival k) : q.action a b ↔ p.action a b :=
  deletion_exact_on_old_domain d (indexed_to_native p q h) a ha b

end LCTR.CoreIndexedNativeDeletion
