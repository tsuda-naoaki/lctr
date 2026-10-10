import CoreEngineeringDataInterfaces

namespace LCTR.CoreEngineeringInputBurden
set_option autoImplicit false
open Set LCTR.CoreAuditStateTransport

inductive Tag where
  | view | recordConfig | invasiveness | communication | countStep | stability
  | cellWidth | discernibility | coupling | trajectory | observable | lawTest | differentialTest
  deriving DecidableEq
def allTags : List Tag := [.view,.recordConfig,.invasiveness,.communication,.countStep,
  .stability,.cellWidth,.discernibility,.coupling,.trajectory,.observable,.lawTest,.differentialTest]
theorem tag_count : allTags.length = 13 := rfl
theorem tag_distinct : allTags.Nodup := by decide
theorem tag_complete (t : Tag) : t ∈ allTags := by cases t <;> simp [allTags]

structure BasicData where
  ViewContext : Type
  PairScaleContext : Type
  InvasionContext : Type
  DistributedContext : Type
  ViewValue : Type
  ConfigValue : Type
  InvasionValue : Type
  CommValue : Type
  view : ViewContext → ViewValue
  config : PairScaleContext → ConfigValue
  invasion : InvasionContext → InvasionValue
  comm : DistributedContext → CommValue

def Value (b : BasicData) (other : Tag → Type) : Tag → Type
  | .view => {v : b.ViewValue // v ∈ Set.range b.view}
  | .recordConfig => {v : b.ConfigValue // v ∈ Set.range b.config}
  | .invasiveness => {v : b.InvasionValue // v ∈ Set.range b.invasion}
  | .communication => {v : b.CommValue // v ∈ Set.range b.comm}
  | t => other t
structure Input (b : BasicData) (other : Tag → Type) (Ref Cert : Type) where
  tag : Ref → Tag
  measure : (r : Ref) → Value b other (tag r)
  certificate : Cert

theorem view_origin (b : BasicData) (other : Tag → Type) (v : Value b other .view) :
    ∃ x, b.view x = v.val := v.property
theorem config_origin (b : BasicData) (other : Tag → Type) (v : Value b other .recordConfig) :
    ∃ x, b.config x = v.val := v.property
theorem invasion_origin (b : BasicData) (other : Tag → Type) (v : Value b other .invasiveness) :
    ∃ x, b.invasion x = v.val := v.property
theorem communication_origin (b : BasicData) (other : Tag → Type) (v : Value b other .communication) :
    ∃ x, b.comm x = v.val := v.property
theorem all_references_typed (b : BasicData) (other : Tag → Type) {Ref Cert : Type}
    (d : Input b other Ref Cert) (r : Ref) :
    ∃ v : Value b other (d.tag r), d.measure r = v := ⟨d.measure r,rfl⟩
theorem range_not_ambient {A B : Type} (f : A → B) (y : B) (h : y ∉ Set.range f) :
    ¬ ∃ v : {v // v ∈ Set.range f}, v.val = y := by
  rintro ⟨v,rfl⟩
  exact h v.property

def bulkTags : Set Tag := {.view,.recordConfig,.invasiveness,.countStep,.stability,.cellWidth,.discernibility}
def followingTags : Set Tag := bulkTags ∪ {.communication,.coupling}
theorem bulk_tags_exact (t : Tag) : t ∈ bulkTags ↔
    t = .view ∨ t = .recordConfig ∨ t = .invasiveness ∨ t = .countStep ∨
    t = .stability ∨ t = .cellWidth ∨ t = .discernibility := by simp [bulkTags]
theorem following_tags_exact (t : Tag) : t ∈ followingTags ↔
    t ∈ bulkTags ∨ t = .communication ∨ t = .coupling := by
  simp only [followingTags,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff]
theorem four_other_tags_excluded :
    Tag.trajectory ∉ followingTags ∧ Tag.observable ∉ followingTags ∧
    Tag.lawTest ∉ followingTags ∧ Tag.differentialTest ∉ followingTags := by
  simp [followingTags,bulkTags]

structure Configuration (Ref Ev Tok : Type) where
  verified : Fin 2 → Set Ev
  refs : Ev → Set Ref
  tag : Ref → Tag
  state : Fin 2 → Ev → AuditStatus
  target : Ev → Tok
variable {Ref Ev Tok : Type}
def hasRef (d : Configuration Ref Ev Tok) (allowed : Set Tag) (e : Ev) : Prop :=
  ∃ r ∈ d.refs e, d.tag r ∈ allowed
def evidence (d : Configuration Ref Ev Tok) (allowed : Set Tag) (k : Fin 2) : Set Ev :=
  {e | e ∈ d.verified k ∧ hasRef d allowed e}
def indexed (d : Configuration Ref Ev Tok) (allowed : Set Tag) : Set (Fin 2 × Ev) :=
  {p | p.2 ∈ evidence d allowed p.1}
def failed (d : Configuration Ref Ev Tok) (allowed : Set Tag) (k : Fin 2) : Set Ev :=
  {e | e ∈ evidence d allowed k ∧ d.state k e = .fail}
def failingUnion (d : Configuration Ref Ev Tok) (allowed : Set Tag) : Set Ev :=
  {e | ∃ k, e ∈ failed d allowed k}
def tokens (d : Configuration Ref Ev Tok) (allowed : Set Tag) : Set Tok :=
  d.target '' failingUnion d allowed
def burden {S : Type} (kernel : Set Tok → Set S) (d : Configuration Ref Ev Tok) (allowed : Set Tag) : Set S :=
  kernel (tokens d allowed)

theorem evidence_exact (d : Configuration Ref Ev Tok) (allowed : Set Tag) (k : Fin 2) (e : Ev) :
    e ∈ evidence d allowed k ↔ e ∈ d.verified k ∧ ∃ r ∈ d.refs e, d.tag r ∈ allowed := Iff.rfl
theorem indexed_exact (d : Configuration Ref Ev Tok) (allowed : Set Tag) (k : Fin 2) (e : Ev) :
    (k,e) ∈ indexed d allowed ↔ e ∈ evidence d allowed k := Iff.rfl
theorem indexed_separates (e : Ev) : ((0 : Fin 2),e) ≠ (1,e) := by simp
theorem failed_exact (d : Configuration Ref Ev Tok) (allowed : Set Tag) (k : Fin 2) (e : Ev) :
    e ∈ failed d allowed k ↔ e ∈ d.verified k ∧ hasRef d allowed e ∧ d.state k e = .fail := by
  constructor
  · rintro ⟨⟨hv,hr⟩,hs⟩
    exact ⟨hv,hr,hs⟩
  · rintro ⟨hv,hr,hs⟩
    exact ⟨⟨hv,hr⟩,hs⟩
theorem union_exact (d : Configuration Ref Ev Tok) (allowed : Set Tag) (e : Ev) :
    e ∈ failingUnion d allowed ↔ ∃ k, e ∈ failed d allowed k := Iff.rfl
theorem tokens_exact (d : Configuration Ref Ev Tok) (allowed : Set Tag) (t : Tok) :
    t ∈ tokens d allowed ↔ ∃ k e, e ∈ d.verified k ∧
      hasRef d allowed e ∧ d.state k e = .fail ∧ d.target e = t := by
  simp only [tokens,Set.mem_image,failingUnion,Set.mem_ofPred_eq,failed,evidence]
  constructor
  · rintro ⟨e,⟨k,⟨hv,hr⟩,hs⟩,ht⟩
    exact ⟨k,e,hv,hr,hs,ht⟩
  · rintro ⟨k,e,hv,hr,hs,ht⟩
    exact ⟨e,⟨k,⟨hv,hr⟩,hs⟩,ht⟩
theorem nonfail_excluded (d : Configuration Ref Ev Tok) (allowed : Set Tag) (k : Fin 2) (e : Ev)
    (h : d.state k e ≠ .fail) : e ∉ failed d allowed k := by
  intro he; exact h he.2
theorem outside_tags_excluded (d : Configuration Ref Ev Tok) (allowed : Set Tag) (k : Fin 2) (e : Ev)
    (h : ∀ r ∈ d.refs e, d.tag r ∉ allowed) : e ∉ evidence d allowed k := by
  rintro ⟨_,r,hr,ha⟩
  exact h r hr ha
theorem burden_exact {S : Type} (kernel : Set Tok → Set S) (d : Configuration Ref Ev Tok)
    (allowed : Set Tag) : burden kernel d allowed = kernel (tokens d allowed) := rfl

def delta {S : Type} (a b : Set S) : Set S := {s | (s ∈ a ∧ s ∉ b) ∨ (s ∈ b ∧ s ∉ a)}
theorem configuration_delta {R0 E0 R1 E1 S : Type}
    (d0 : Configuration R0 E0 Tok) (d1 : Configuration R1 E1 Tok)
    (kernel : Set Tok → Set S) (s : S) :
    s ∈ delta (burden kernel d0 bulkTags) (burden kernel d1 followingTags) ↔
      (s ∈ kernel (tokens d0 bulkTags) ∧ s ∉ kernel (tokens d1 followingTags)) ∨
      (s ∈ kernel (tokens d1 followingTags) ∧ s ∉ kernel (tokens d0 bulkTags)) := Iff.rfl

end LCTR.CoreEngineeringInputBurden
