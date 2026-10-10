import CoreConfigurationComparison
import CoreExactInputAssembly

namespace LCTR.CoreConfigurationOrder
set_option autoImplicit false
open Set LCTR.CoreOperationalConfiguration LCTR.CoreSourceMatch
open LCTR.CoreConfigurationComparison LCTR.CorePreorderQuotient
open LCTR.CoreExactInputAssembly LCTR.CoreExactStructure

def sourceOrder (x : Configuration) (r : Fin 2) : OrderData (Source x r) := by
  by_cases h : r=0
  · subst r
    exact sourceClockOrder x.2.schema
  · have h' : r=1 := by omega
    subst r
    exact sourceDetectorOrder x.2.schema

theorem clock_order_exact (x : Configuration) (a b : Source x 0) :
    (sourceOrder x 0).le a b ↔ a.1=b.1 ∧ a.2≤b.2 := Iff.rfl

theorem record_order_exact (x : Configuration) (a b : Source x 1) :
    (sourceOrder x 1).le a b ↔ a=b ∨ x.2.schema.sequence a<x.2.schema.sequence b :=
  detector_order_exact x.2.schema a b

theorem distinct_clock_sources_incomparable (x : Configuration) (a b : Source x 0)
    (hd : a.1≠b.1) : ¬ (sourceOrder x 0).le a b ∧ ¬ (sourceOrder x 0).le b a := by
  rw [clock_order_exact,clock_order_exact]
  exact ⟨fun h => hd h.1,fun h => hd h.1.symm⟩

variable (x : Configuration) (d : PairDatum x) (h1 : CoreConfigurationComparison.L1 x)
variable (h2 : CoreConfigurationComparison.L2 x d)
variable (specs : (r : Fin 2) → Set (CoreLocalLoopRealization.Spec (data x d h1 h2 r)))

def NativeDescent : Prop := ∀ r,
  OrdDesc (CoreTypedWords.orbitSetoid (CoreSourceLoops.system (data x d h1 h2 r)))
    (Pullback (recover (arrival x r) (h1 r)) (sourceOrder x r).le)

variable (desc : NativeDescent x d h1 h2)
def orders (r : Fin 2) : RoleOrder (input x d h1 h2 specs) r where
  relation := (sourceOrder x r).le
  refl := (sourceOrder x r).reflexive
  trans := fun _ _ _ => (sourceOrder x r).transitive _ _ _
  anti := fun _ _ => (sourceOrder x r).antisymmetric _ _
  descent := desc r

noncomputable abbrev native (r : Fin 2) := assembled (input x d h1 h2 specs) r (orders x d h1 h2 specs desc r)

theorem quotient_preserved (r : Fin 2) :
    Canonical (native x d h1 h2 specs desc r) =
      CoreComparisonStage.RoleQuotient (input x d h1 h2 specs) r := rfl

theorem projection_preserved (r : Fin 2) (i : Node x) (a : ImageAt (arrival x r) i) :
    canonicalProjection (native x d h1 h2 specs desc r) ⟨i,a⟩ =
      CoreComparisonStage.roleProjection (input x d h1 h2 specs) r i a := rfl

theorem original_source_order (r : Fin 2) (a b : Tagged (arrival x r)) :
    canonicalOrder (native x d h1 h2 specs desc r)
      (canonicalProjection (native x d h1 h2 specs desc r) a)
      (canonicalProjection (native x d h1 h2 specs desc r) b) ↔
      (sourceOrder x r).le (recover (arrival x r) (h1 r) a)
        (recover (arrival x r) (h1 r) b) := Iff.rfl

theorem native_partial_order (r : Fin 2) :
    ReflRel (canonicalOrder (native x d h1 h2 specs desc r)) ∧
    TransRel (canonicalOrder (native x d h1 h2 specs desc r)) ∧
    AntiRel (canonicalOrder (native x d h1 h2 specs desc r)) := canonical_partial_order _

variable (g : ∀ r, GlobalInc (native x d h1 h2 specs desc r))

theorem native_ordered_output_unique (h : RemainingConditions x d h1 h2 specs) :
    ∃! p : CoreComparisonStage.Output (input x d h1 h2 specs) ×
      OrderedFamily (input x d h1 h2 specs) (orders x d h1 h2 specs desc) g,
      CoreComparisonStage.Valid (input x d h1 h2 specs) p.1 ∧
      FamilyValid (input x d h1 h2 specs) (orders x d h1 h2 specs desc) g p.2 :=
  comparison_and_order_same_input _ _ ((remaining_iff_operative x d h1 h2 specs).mp h) g

theorem native_local_global_compatible (r : Fin 2) (i : Node x)
    (a : ImageAt (arrival x r) i) :
    localGlobal (native x d h1 h2 specs desc r) i
      (global_implies_local_inc _ (g r) i) (g r)
      (chart (native x d h1 h2 specs desc r) i (global_implies_local_inc _ (g r) i) a) =
      globalProjection (native x d h1 h2 specs desc r) (g r)
        (CoreComparisonStage.roleProjection (input x d h1 h2 specs) r i a) := rfl

theorem native_representation_order (r : Fin 2) {Y : Type}
    (f : GlobalQ (native x d h1 h2 specs desc r) (g r) → Y) (lt : Y → Y → Prop)
    (hf : ∀ a b, lt (f a) (f b) ↔ globalOrder (native x d h1 h2 specs desc r) (g r) a b)
    (a b : Canonical (native x d h1 h2 specs desc r)) :
    lt (represented (native x d h1 h2 specs desc r) (g r) f a)
      (represented (native x d h1 h2 specs desc r) (g r) f b) ↔
      (sourceOrder x r).le
        (recover (arrival x r) (h1 r) (Quotient.out a))
        (recover (arrival x r) (h1 r) (Quotient.out b)) ∧ a≠b := by
  rw [represented_order_pullback _ _ f lt hf]
  change canonicalOrder (native x d h1 h2 specs desc r) a b ∧ a≠b ↔ _
  have recover_order := original_source_order x d h1 h2 specs desc r (Quotient.out a) (Quotient.out b)
  have ho : canonicalOrder (native x d h1 h2 specs desc r) a b ↔
      (sourceOrder x r).le (recover (arrival x r) (h1 r) (Quotient.out a))
        (recover (arrival x r) (h1 r) (Quotient.out b)) := by
    have ha : canonicalProjection (native x d h1 h2 specs desc r) (Quotient.out a) = a :=
      Quotient.out_eq a
    have hb : canonicalProjection (native x d h1 h2 specs desc r) (Quotient.out b) = b :=
      Quotient.out_eq b
    exact (congrArg₂ (canonicalOrder (native x d h1 h2 specs desc r)) ha hb).symm.to_iff.trans recover_order
  exact and_congr ho Iff.rfl

theorem native_representation_kernel (r : Fin 2) {Y : Type}
    (f : GlobalQ (native x d h1 h2 specs desc r) (g r) → Y)
    (hf : Function.Injective f) (a b : Canonical (native x d h1 h2 specs desc r)) :
    represented (native x d h1 h2 specs desc r) (g r) f a =
      represented (native x d h1 h2 specs desc r) (g r) f b ↔
      LCTR.TransitiveIncomparabilityQuotientCore.Inc (strictData (native x d h1 h2 specs desc r)).lt a b :=
  represented_kernel _ _ f hf a b

end LCTR.CoreConfigurationOrder
