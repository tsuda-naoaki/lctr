import CoreLawComponentCharts
import CoreDifferentialCovariance

namespace LCTR.CoreNativeLawJets
set_option autoImplicit false
open Set Filter LCTR.CoreLocalCharts LCTR.CoreLawComponentCharts
open LCTR.CoreNativeLawComponents LCTR.CoreValueJetChanges LCTR.CoreDifferentialCovariance
open scoped Topology
variable {C D B I TI : Type} {Val : I → Type} {VI : Fin 2 → Type}
variable (c : Context C D B I Val) (l : ComponentInput c)
variable (a : NativeAtlas c l TI VI) (i : Index TI VI) (s : Fin 2) (k : ℕ)

abbrev ValueSpace := Fin (a.val.dim s) → ℝ
abbrev ValueDomain := (a.val.valChart s (i.2 s)).target

structure SmoothRealization where
  extension : ℝ → ValueSpace c l a s
  agrees : ∀ t : NumericDomain a.val i,
    extension t.val = (curve a.val i t s).val
  smooth : ∀ t : NumericDomain a.val i, ContDiffAt ℝ k extension t.val

variable (d : SmoothRealization c l a i s k)

theorem realization_value_in_chart (t : NumericDomain a.val i) :
    d.extension t.val ∈ ValueDomain c l a i s := by
  rw [d.agrees t]
  exact (curve a.val i t s).property

noncomputable def nativeJet (t : NumericDomain a.val i) : Domain k (ValueDomain c l a i s) :=
  jetAt k t.val d.extension (ValueDomain c l a i s)
    (realization_value_in_chart c l a i s k d t)

theorem zeroth_is_generated_curve (t : NumericDomain a.val i) :
    (nativeJet c l a i s k d t).val 0 = (curve a.val i t s).val := by
  simpa only [nativeJet,jetAt,LCTR.CoreFiniteJets.jet,Fin.val_zero,iteratedDeriv_zero]
    using d.agrees t

theorem zeroth_is_native_law_value (x : JointDomain a.val i) :
    ∃ hs : nativeValues c l s x.val ∈ (a.val.valChart s (i.2 s)).source,
      (nativeJet c l a i s k d (timeCoord a.val i x)).val 0 =
        ((a.val.valChart s (i.2 s)).coordinates ⟨nativeValues c l s x.val,hs⟩).val := by
  obtain ⟨hs,h⟩ := native_side_curve c l a i x s
  exact ⟨hs,(zeroth_is_generated_curve c l a i s k d _).trans (congrArg Subtype.val h)⟩

theorem smooth_realizations_agree_nearby
    (e : SmoothRealization c l a i s k) (openDomain : IsOpen (NumericDomain a.val i))
    (t : NumericDomain a.val i) : d.extension =ᶠ[𝓝 t.val] e.extension := by
  filter_upwards [openDomain.mem_nhds t.property] with z hz
  exact (d.agrees ⟨z,hz⟩).trans (e.agrees ⟨z,hz⟩).symm

theorem native_jet_independent_of_extension
    (e : SmoothRealization c l a i s k) (openDomain : IsOpen (NumericDomain a.val i))
    (t : NumericDomain a.val i) :
    nativeJet c l a i s k d t = nativeJet c l a i s k e t :=
  jetAt_eventual_eq k t.val _ d.extension e.extension _ _
    (smooth_realizations_agree_nearby c l a i s k d e openDomain t)

noncomputable def nativePair (t : NumericDomain a.val i) := (t,nativeJet c l a i s k d t)

theorem generated_jet_relation_membership
    (relation : Set (NumericDomain a.val i × Domain k (ValueDomain c l a i s)))
    (condition : ∀ t, nativePair c l a i s k d t ∈ relation) :
    Set.range (nativePair c l a i s k d) ⊆ relation := by
  rintro _ ⟨t,rfl⟩
  exact condition t

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {W : Set F}

theorem value_change_acts_on_native_jet
    (change : ValueChange k (NumericDomain a.val i) (ValueDomain c l a i s) W)
    (t : NumericDomain a.val i) :
    change.lift t.val (nativeJet c l a i s k d t) =
      jetAt k t.val (change.forward ∘ d.extension) W
        (change.forward_maps (realization_value_in_chart c l a i s k d t)) :=
  change.lift_action t.val t.property d.extension (d.smooth t) _

theorem value_covariance_preserves_native_membership
    (change : ValueChange k (NumericDomain a.val i) (ValueDomain c l a i s) W)
    (source : Set (NumericDomain a.val i × Domain k (ValueDomain c l a i s)))
    (target : Set (NumericDomain a.val i × Domain k W))
    (cov : ∀ p, p ∈ source ↔ change.map p ∈ target)
    (member : ∀ t, nativePair c l a i s k d t ∈ source) :
    change.map '' source = target ∧
      ∀ t, change.map (nativePair c l a i s k d t) ∈ target :=
  ⟨change.relation_image source target cov,fun t => (cov _).mp (member t)⟩

theorem time_change_preserves_native_zeroth
    {Wtime : Set ℝ}
    (change : TimeChange k (ValueDomain c l a i s) (NumericDomain a.val i) Wtime)
    (t : NumericDomain a.val i) :
    (change.map (nativePair c l a i s k d t)).2.val 0 = (curve a.val i t s).val :=
  (change.preserves_zeroth_value _).trans (zeroth_is_generated_curve c l a i s k d t)

theorem time_covariance_preserves_native_membership
    {Wtime : Set ℝ}
    (change : TimeChange k (ValueDomain c l a i s) (NumericDomain a.val i) Wtime)
    (source : Set (NumericDomain a.val i × Domain k (ValueDomain c l a i s)))
    (target : Set (Wtime × Domain k (ValueDomain c l a i s)))
    (cov : ∀ p, p ∈ source ↔ change.map p ∈ target)
    (member : ∀ t, nativePair c l a i s k d t ∈ source) :
    change.map '' source = target ∧
      ∀ t, change.map (nativePair c l a i s k d t) ∈ target :=
  ⟨change.relation_image source target cov,fun t => (cov _).mp (member t)⟩

end LCTR.CoreNativeLawJets
