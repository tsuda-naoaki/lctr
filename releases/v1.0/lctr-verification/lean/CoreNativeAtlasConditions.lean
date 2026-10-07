import CoreNativeChartOverlaps
import CoreNativeDifferentialPredicates

namespace LCTR.CoreNativeAtlasConditions
set_option autoImplicit false
open Set Filter LCTR.CoreLocalCharts LCTR.CoreValueJetChanges
open LCTR.CoreNativeJointJets LCTR.CoreNativeChartOverlaps
open scoped Topology
variable {T TI : Type} {Val VI : Fin 2 → Type}
variable (a : Atlas T TI Val VI) (k : ℕ)
abbrev Beta := (s : Fin 2) → VI s
abbrev VDomain (b c : Beta (VI:=VI)) := OverlapImage (productChart a b) (productChart a c)
abbrev VSpace (alpha : TI) (b c : Beta (VI:=VI)) :=
  (a.time alpha).target × Domain k (VDomain a b c)
abbrev TDomain (alpha delta : TI) := OverlapImage (a.time alpha) (a.time delta)
abbrev TSpace (alpha delta : TI) (b : Beta (VI:=VI)) :=
  TDomain a alpha delta × Domain k (productChart a b).target

def valueAmbient (alpha : TI) (b c : Beta (VI:=VI)) (p : VSpace a k alpha b c) :
    JetSpace a (alpha,b) k :=
  (p.1,⟨p.2.val,overlap_image_in_target (productChart a b) (productChart a c) p.2.property⟩)

def timeAmbient (alpha delta : TI) (b : Beta (VI:=VI)) (p : TSpace a k alpha delta b) :
    JetSpace a (alpha,b) k :=
  (⟨p.1.val,overlap_image_in_target (a.time alpha) (a.time delta) p.1.property⟩,p.2)

structure Regular where
  valChange : ∀ alpha b c, BoundValueChange (productChart a b) (productChart a c) k (a.time alpha).target
  timeChange : ∀ alpha delta b, BoundTimeChange (a.time alpha) (a.time delta) k (productChart a b).target

def Diff1 : Prop := Nonempty (Regular a k)
abbrev Relations := (i : Index TI VI) → Set (JetSpace a i k)
def ValueCov (r : Regular a k) (R : Relations a k) : Prop :=
  ∀ alpha b c p, valueAmbient a k alpha b c p ∈ R (alpha,b) ↔
    valueAmbient a k alpha c b ((r.valChange alpha b c).change.map p) ∈ R (alpha,c)
def Diff4 (R : Relations a k) : Prop := ∃ r : Regular a k, ValueCov a k r R

theorem diff1_has_actual_changes (h : Diff1 a k) :
    ∀ alpha b c, Nonempty (BoundValueChange (productChart a b) (productChart a c) k (a.time alpha).target) := by
  obtain ⟨r⟩ := h
  exact fun alpha b c => ⟨r.valChange alpha b c⟩

theorem regular_value_domains_open (r : Regular a k) (alpha : TI) (b c : Beta (VI:=VI)) :
    IsOpen (VDomain a b c) ∧ IsOpen (VDomain a c b) :=
  ⟨(r.valChange alpha b c).change.source_open,(r.valChange alpha b c).change.target_open⟩

theorem regular_time_domains_open (r : Regular a k) (alpha delta : TI) (b : Beta (VI:=VI)) :
    IsOpen (TDomain a alpha delta) ∧ IsOpen (TDomain a delta alpha) :=
  ⟨(r.timeChange alpha delta b).change.source_open,(r.timeChange alpha delta b).change.target_open⟩

theorem value_ambient_preserves_coordinates (alpha : TI) (b c : Beta (VI:=VI))
    (p : VSpace a k alpha b c) :
    (valueAmbient a k alpha b c p).1=p.1 ∧ (valueAmbient a k alpha b c p).2.val=p.2.val := ⟨rfl,rfl⟩

theorem time_ambient_preserves_coordinates (alpha delta : TI) (b : Beta (VI:=VI))
    (p : TSpace a k alpha delta b) :
    (timeAmbient a k alpha delta b p).1.val=p.1.val ∧ (timeAmbient a k alpha delta b p).2=p.2 := ⟨rfl,rfl⟩

theorem regular_value_maps_unique (r q : Regular a k) (alpha : TI) (b c : Beta (VI:=VI)) :
    (r.valChange alpha b c).change.map = (q.valChange alpha b c).change.map := by
  funext p
  apply Prod.ext
  · rfl
  · obtain ⟨gamma,hg,hv,he⟩ := domain_realization k p.1.val (VDomain a b c) p.2
    change (r.valChange alpha b c).change.lift p.1.val p.2 =
      (q.valChange alpha b c).change.lift p.1.val p.2
    rw [← he,(r.valChange alpha b c).change.lift_action p.1.val p.1.property,
      (q.valChange alpha b c).change.lift_action p.1.val p.1.property]
    · apply jetAt_eventual_eq
      have near : ∀ᶠ x in 𝓝 p.1.val, gamma x ∈ VDomain a b c :=
        hg.continuous.continuousAt ((r.valChange alpha b c).change.source_open.mem_nhds hv)
      filter_upwards [near] with x hx
      exact ((r.valChange alpha b c).forward_exact ⟨gamma x,hx⟩).trans
        ((q.valChange alpha b c).forward_exact ⟨gamma x,hx⟩).symm
    all_goals exact (hg.of_le le_top).contDiffAt

theorem value_cov_independent_of_certificate (r q : Regular a k) (R : Relations a k) :
    ValueCov a k r R ↔ ValueCov a k q R := by
  unfold ValueCov
  simp only [regular_value_maps_unique a k r q]

theorem diff4_requires_diff1 (R : Relations a k) : Diff4 a k R → Diff1 a k := by
  rintro ⟨r,_⟩
  exact ⟨r⟩

theorem diff4_restricts (R : Relations a k) (r : Regular a k) :
    Diff4 a k R ↔ ValueCov a k r R := by
  constructor
  · rintro ⟨q,hq⟩
    exact (value_cov_independent_of_certificate a k q r R).mp hq
  · exact fun hr => ⟨r,hr⟩

theorem diff4_false_outside (R : Relations a k) (h : ¬ Diff1 a k) : ¬ Diff4 a k R :=
  fun h4 => h (diff4_requires_diff1 a k R h4)

theorem value_relation_restriction_image (R : Relations a k) (r : Regular a k)
    (cov : ValueCov a k r R) (alpha : TI) (b c : Beta (VI:=VI)) :
    (r.valChange alpha b c).change.map ''
      {p | valueAmbient a k alpha b c p ∈ R (alpha,b)} =
      {p | valueAmbient a k alpha c b p ∈ R (alpha,c)} :=
  bound_value_relation_image (productChart a b) (productChart a c)
    (r.valChange alpha b c) _ _ (cov alpha b c)

end LCTR.CoreNativeAtlasConditions
