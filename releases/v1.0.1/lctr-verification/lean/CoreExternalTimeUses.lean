import CoreFiniteAudit

namespace LCTR.CoreExternalTimeUses
set_option autoImplicit false
open Set LCTR.CoreTokenGraph LCTR.CoreFiniteAudit

inductive Use where
  | logIndex | calibration | provenance | generatedPremise
  deriving DecidableEq
inductive InputPart where
  | formation | evaluation | condition
  deriving DecidableEq
abbrev Site := InputPart × Token

structure Audit (Ref : Type) where
  external : Set Ref
  usage : external → Use
  sites : external → Set Site
  faithful : ∀ r, (sites r).Nonempty ↔ usage r = .generatedPremise

def violations {Ref : Type} (a : Audit Ref) : Set a.external :=
  {r | a.usage r = .generatedPremise}

theorem violation_iff_actual_site {Ref : Type} (a : Audit Ref) (r : a.external) :
    r ∈ violations a ↔ (a.sites r).Nonempty := (a.faithful r).symm

theorem empty_iff_no_actual_sites {Ref : Type} (a : Audit Ref) :
    violations a = ∅ ↔ ∀ r, a.sites r = ∅ := by
  constructor
  · intro he r
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro site hs
    have hv : r ∈ violations a := (a.faithful r).mp ⟨site,hs⟩
    rw [he] at hv
    exact hv
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro r hr
    obtain ⟨site,hs⟩ := (violation_iff_actual_site a r).mp hr
    rw [h r] at hs
    exact hs

theorem empty_allows_only_metadata_uses {Ref : Type} (a : Audit Ref)
    (h : violations a = ∅) (r : a.external) :
    a.usage r = .logIndex ∨ a.usage r = .calibration ∨ a.usage r = .provenance := by
  have no : a.usage r ≠ .generatedPremise := by
    intro hu
    have hv : r ∈ violations a := hu
    rw [h] at hv
    exact hv
  cases hu : a.usage r <;> simp_all

theorem actual_site_identifies_target {Ref : Type} (a : Audit Ref) (r : a.external)
    (h : r ∈ violations a) :
    ∃ part : InputPart, ∃ t : Token, (part,t) ∈ a.sites r := by
  obtain ⟨⟨part,t⟩,hs⟩ := (violation_iff_actual_site a r).mp h
  exact ⟨part,t,hs⟩

theorem every_actual_site_is_flagged {Ref : Type} (a : Audit Ref) (r : a.external)
    (site : Site) (h : site ∈ a.sites r) : r ∈ violations a :=
  (a.faithful r).mp ⟨site,h⟩

theorem metadata_use_has_no_premise_site {Ref : Type} (a : Audit Ref) (r : a.external)
    (h : a.usage r = .logIndex ∨ a.usage r = .calibration ∨ a.usage r = .provenance) :
    a.sites r = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro site hs
  have hu := (a.faithful r).mp ⟨site,hs⟩
  rcases h with h | h | h <;> simp_all

theorem native_states_depend_on_typed_inputs
    (f e c g h k : Token → Bool) (hf : f = g) (he : e = h) (hc : c = k) :
    run f e c 40 = run g h k 40 := by rw [hf,he,hc]

theorem metadata_tag_alone_does_not_certify :
    let misleadingUsage : Unit → Use := fun _ => .logIndex
    let actualSites : Unit → Set Site := fun _ => {(.formation,(⟨0,⟨0,by decide⟩⟩ : Token))}
    {r | misleadingUsage r = .generatedPremise} = ∅ ∧
    (actualSites ()).Nonempty ∧
    ¬ (∀ r, (actualSites r).Nonempty ↔ misleadingUsage r = .generatedPremise) := by
  dsimp
  refine ⟨by simp,⟨(.formation,⟨0,⟨0,by decide⟩⟩),rfl⟩,?_⟩
  intro hf
  have bad := (hf ()).mp ⟨(.formation,⟨0,⟨0,by decide⟩⟩),rfl⟩
  cases bad

end LCTR.CoreExternalTimeUses
