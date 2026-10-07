import CoreWordEncoding

namespace LCTR.CorePureWordDisplays
open LCTR.CoreSourceMatch LCTR.CoreSourceLoops LCTR.CoreNativeWordFamilies LCTR.CoreWordEncoding
universe u v w
set_option autoImplicit false
variable {U : Type u} {S : Type v} {V : U → Type w}
variable {d : Data U S V} {i j : U}

theorem native_position_length (p : Path d i j) :
    (decode p).positions.length = length p + 1 := by
  have len := native_length_preserved (decode p)
  rw [encode_decode] at len
  rw [tuple_lengths,← len]

theorem source_kind_list_constant (p : Path d i j) (hs : SourceOnly p) :
    (decode p).kinds = List.replicate (length p) Kind.src := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    simp only [decode,Word.kinds,length]
    rw [hs.1,ih hs.2,Nat.add_comm,List.replicate_succ]

def sourceDisplay (p : SourceWord d i j) : Nat × List U := (length p.val,(decode p.val).positions)

theorem source_positions_suffice (p q : SourceWord d i j)
    (hp : (decode p.val).positions = (decode q.val).positions) : p=q := by
  have hl := congrArg List.length hp
  rw [native_position_length,native_position_length] at hl
  have len : length p.val = length q.val := Nat.add_right_cancel hl
  have kinds : (decode p.val).kinds = (decode q.val).kinds := by
    rw [source_kind_list_constant p.val p.property,source_kind_list_constant q.val q.property,len]
  apply Subtype.ext
  apply native_display_injective
  exact Prod.ext (congrArg List.length kinds) (Prod.ext hp kinds)

theorem source_display_injective :
    Function.Injective (sourceDisplay : SourceWord d i j → Nat × List U) := by
  intro p q h
  exact source_positions_suffice p q (congrArg Prod.snd h)

def direction : Kind → Bool
  | .src => false
  | .trPlus => true
  | .trMinus => false

def transportKind (s : Bool) : Kind := if s then .trPlus else .trMinus

def directions (p : Path d i j) : List Bool := (decode p).kinds.map direction

theorem transport_kinds_recovered (p : Path d i j) (ht : TransportOnly p) :
    (directions p).map transportKind = (decode p).kinds := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    change transportKind (direction e.val) :: (directions p).map transportKind =
      e.val :: (decode p).kinds
    rw [ih ht.2]
    have atom : transportKind (direction e.val) = e.val := by
      cases h : e.val with
      | src => exact False.elim (ht.1 h)
      | trPlus => rfl
      | trMinus => rfl
    rw [atom]

theorem direction_length (p : Path d i j) : (directions p).length = length p := by
  simp only [directions,List.length_map]
  have h := native_length_preserved (decode p)
  rw [encode_decode] at h
  exact h.symm

def transportDisplay (p : TransportWord d i j) : Nat × List U × List Bool :=
  (length p.val,(decode p.val).positions,directions p.val)

theorem transport_display_injective :
    Function.Injective (transportDisplay : TransportWord d i j → Nat × List U × List Bool) := by
  intro p q h
  have pos := congrArg (fun x : Nat × List U × List Bool => x.2.1) h
  have signs := congrArg (fun x : Nat × List U × List Bool => x.2.2) h
  change directions p.val = directions q.val at signs
  have kinds := congrArg (List.map transportKind) signs
  rw [transport_kinds_recovered p.val p.property,transport_kinds_recovered q.val q.property] at kinds
  apply Subtype.ext
  apply native_display_injective
  exact Prod.ext (congrArg List.length kinds) (Prod.ext pos kinds)

theorem source_unique_display_preimage (p : SourceWord d i j) :
    ∃! q : SourceWord d i j, sourceDisplay q=sourceDisplay p :=
  ⟨p,rfl,fun _ h => source_display_injective h⟩

theorem transport_unique_display_preimage (p : TransportWord d i j) :
    ∃! q : TransportWord d i j, transportDisplay q=transportDisplay p :=
  ⟨p,rfl,fun _ h => transport_display_injective h⟩

theorem pure_display_shapes (p : SourceWord d i j) (q : TransportWord d i j) :
    (sourceDisplay p).2.length = (sourceDisplay p).1+1 ∧
    (transportDisplay q).2.1.length = (transportDisplay q).1+1 ∧
    (transportDisplay q).2.2.length = (transportDisplay q).1 :=
  ⟨native_position_length p.val,native_position_length q.val,direction_length q.val⟩

theorem source_direction_is_not_transport :
    transportKind (direction Kind.src) ≠ Kind.src := by
  change Kind.trMinus ≠ Kind.src
  intro h
  cases h

end LCTR.CorePureWordDisplays
