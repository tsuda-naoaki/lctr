import CoreFailureMultiplicity
import CoreSeriesValidity
import CoreStructuralBurden

namespace LCTR.CoreLocalizationBundle
set_option autoImplicit false
open Set LCTR.CoreTokenGraph LCTR.CoreEvaluation LCTR.CoreFiniteAudit
open LCTR.SelectedInputEvaluation LCTR.CoreContinuumBoundary LCTR.CoreFirstFailureReport
open LCTR.CoreFailureMultiplicity LCTR.CoreSeriesValidity LCTR.CoreStructuralBurden
open scoped ENNReal
variable {L : Type} [LinearOrder L]

def strictDomain (q : L → Token → State) : Set L := {l | Strict (q l)}
def approxDomain (q : L → Token → State) : Set L := {l | Approximation (q l)}
def fullDomain (q : L → Token → State) : Set L := {l | Full (q l)}

omit [LinearOrder L] in
theorem domain_intersection (q : L → Token → State) :
    fullDomain q = strictDomain q ∩ approxDomain q := by
  ext l
  exact completion_split (q l)

def boundaryTokens (V : Set L) (b : L → ApproxSignature) : Set Token :=
  {t | ∃ i ∈ support V b, t = (⟨3,i⟩ : Token)}

theorem boundary_tokens_only_approx (V : Set L) (b : L → ApproxSignature)
    (t : Token) (h : t ∈ boundaryTokens V b) : t.1 = 3 := by
  obtain ⟨i,_,rfl⟩ := h
  rfl

theorem boundary_tokens_at_least (V : Set L) (b : L → ApproxSignature) (l : L)
    (hl : IsLeast Vᶜ l) :
    boundaryTokens V b = {t | ∃ i : Fin 9, b l i = true ∧ t = (⟨3,i⟩ : Token)} := by
  ext t
  simp [boundaryTokens,support_at_boundary V b l hl,signatureSupport]

theorem no_boundary_no_tokens (V : Set L) (b : L → ApproxSignature)
    (h : boundaryData V b = ∅) : boundaryTokens V b = ∅ := by
  have hn := (boundary_empty_iff V b).mp h
  ext t
  simp [boundaryTokens,no_boundary_no_support V b hn]

theorem no_boundary_no_burden (V : Set L) (b : L → ApproxSignature)
    (h : boundaryData V b = ∅) : nativeBurden (boundaryTokens V b) = ∅ := by
  rw [no_boundary_no_tokens V b h]
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro s ⟨t,ht,_⟩
  exact ht

structure Data (L : Type) where
  strictValidity : Set L
  approxValidity : Set L
  fullValidity : Set L
  maxInterval : Set L
  firstFailure : LCTR.CoreFirstFailureReport.Report L
  multiplicity : FailureCase × BoundaryCase
  structuralBurden : Set StructTok × Set StructTok
  sixSignature : SixSignature

noncomputable def assemble (q : L → Token → State) (b : L → ApproxSignature) (l : L) : Data L where
  strictValidity := strictDomain q
  approxValidity := approxDomain q
  fullValidity := fullDomain q
  maxInterval := MaximalInitial (approxDomain q)
  firstFailure := LCTR.CoreFirstFailureReport.report (q l) (approxDomain q) b
  multiplicity := multiplicityReport (q l) (approxDomain q) b
  structuralBurden := (nativeBurden (failedSet (q l)),nativeBurden (boundaryTokens (approxDomain q) b))
  sixSignature := signature (q l)

theorem assembled_domain_intersection (q : L → Token → State) (b : L → ApproxSignature) (l : L) :
    (assemble q b l).fullValidity =
      (assemble q b l).strictValidity ∩ (assemble q b l).approxValidity := domain_intersection q

theorem interval_within_approx (q : L → Token → State) (b : L → ApproxSignature) (l : L) :
    (assemble q b l).maxInterval ⊆ (assemble q b l).approxValidity :=
  (maximal_initial_greatest _).1.1

theorem interval_equals_initial_approx (q : L → Token → State) (b : L → ApproxSignature) (l : L)
    (h : Initial (approxDomain q)) :
    (assemble q b l).maxInterval = (assemble q b l).approxValidity := maximal_initial_eq _ h

theorem quantitative_interval (q : L → Token → State) (b : L → ApproxSignature) (l : L)
    (d : L → Fin 9 → ℝ≥0∞) (eps : Fin 9 → ℝ≥0∞)
    (bridge : ∀ x, Approximation (q x) ↔ Valid (d x) eps)
    (hd : ∀ i, Monotone (fun x => d x i)) :
    (assemble q b l).maxInterval = (assemble q b l).approxValidity := by
  apply interval_equals_initial_approx
  have eq : approxDomain q = {x | Valid (d x) eps} := Set.ext bridge
  rw [eq]
  exact monotone_defects_initial d eps hd

theorem assembled_signature_is_minimal (f e c : L → Token → Bool)
    (q : L → Token → State) (rec : ∀ l, Recurs Edge (f l) (e l) (c l) (q l))
    (b : L → ApproxSignature) (l : L) :
    (assemble q b l).sixSignature = setSignature (minimalSet (q l)) :=
  minimal_signature_exact (f l) (e l) (c l) (q l) (rec l)

omit [LinearOrder L] in
theorem native_solution_family_unique (f e c : L → Token → Bool)
    (q : L → Token → State) (rec : ∀ l, Recurs Edge (f l) (e l) (c l) (q l)) :
    q = fun l => run (f l) (e l) (c l) 40 := by
  funext l
  exact finite_run_unique (f l) (e l) (c l) (q l) (rec l)

theorem assembled_independent_of_solution (f e c : L → Token → Bool)
    (q r : L → Token → State)
    (hq : ∀ l, Recurs Edge (f l) (e l) (c l) (q l))
    (hr : ∀ l, Recurs Edge (f l) (e l) (c l) (r l))
    (b : L → ApproxSignature) (l : L) : assemble q b l = assemble r b l := by
  rw [native_solution_family_unique f e c q hq,native_solution_family_unique f e c r hr]

def Generated (f e c : L → Token → Bool) (b : L → ApproxSignature) (l : L) (a : Data L) : Prop :=
  ∃ q : L → Token → State, (∀ x, Recurs Edge (f x) (e x) (c x) (q x)) ∧ a = assemble q b l

theorem localization_data_unique (f e c : L → Token → Bool) (b : L → ApproxSignature) (l : L) :
    ∃! a : Data L, Generated f e c b l a := by
  let q := fun x => run (f x) (e x) (c x) 40
  have hq : ∀ x, Recurs Edge (f x) (e x) (c x) (q x) :=
    fun x => finite_run_solves (f x) (e x) (c x)
  refine ⟨assemble q b l,⟨q,hq,rfl⟩,?_⟩
  rintro a ⟨r,hr,ha⟩
  exact ha.trans (assembled_independent_of_solution f e c r q hr hq b l)

end LCTR.CoreLocalizationBundle
