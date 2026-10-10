import CoreNativeAtlasConditions

namespace LCTR.CoreNativeTimeConditions
set_option autoImplicit false
open Set Filter LCTR.CoreLocalCharts LCTR.CoreNativeChartOverlaps
open LCTR.CoreValueJetChanges LCTR.CoreTransportedLawCharts
open scoped Topology
variable {X E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (ct dt : Chart X ℝ) (k : ℕ) (region : Set E)

theorem bound_time_maps_unique
    (b q : BoundTimeChange ct dt k region) : b.change.map = q.change.map := by
  funext p
  have sameForward : b.change.forward p.1.val = q.change.forward p.1.val :=
    (b.forward_exact p.1).trans (q.forward_exact p.1).symm
  apply Prod.ext
  · exact Subtype.ext sameForward
  · obtain ⟨gamma,hg,hv,he⟩ := domain_realization k p.1.val region p.2
    change b.change.lift p.1.val p.2 = q.change.lift p.1.val p.2
    rw [← he,b.change.lift_action p.1.val p.1.property,
      q.change.lift_action p.1.val p.1.property]
    · apply Subtype.ext
      funext n
      change iteratedDeriv n.val (gamma ∘ b.change.backward) (b.change.forward p.1.val) =
        iteratedDeriv n.val (gamma ∘ q.change.backward) (q.change.forward p.1.val)
      rw [sameForward]
      have near : ∀ᶠ x in 𝓝 (q.change.forward p.1.val), x ∈ OverlapImage dt ct :=
        q.change.target_open.mem_nhds (q.change.forward_maps p.1.property)
      have germs : (gamma ∘ b.change.backward) =ᶠ[𝓝 (q.change.forward p.1.val)]
          (gamma ∘ q.change.backward) := by
        filter_upwards [near] with x hx
        exact congrArg gamma ((b.backward_exact ⟨x,hx⟩).trans (q.backward_exact ⟨x,hx⟩).symm)
      exact germs.iteratedDeriv_eq n.val
    all_goals exact (hg.of_le le_top).contDiffAt

variable {T U : Type} (e : T ≃ U) (c : Chart T ℝ) (d : Chart U ℝ)
abbrev pulledTarget := pushChart e.symm d
abbrev RepDomain := OverlapImage c (pulledTarget e d)
abbrev ReverseDomain := OverlapImage (pulledTarget e d) c
abbrev RepChange := BoundTimeChange c (pulledTarget e d) k region
abbrev SourceSpace := RepDomain e c d × Domain k region
abbrev TargetSpace := ReverseDomain e c d × Domain k region

theorem rep_domain_formula : RepDomain e c d =
    {theta | ∃ x : c.source, e x.val ∈ d.source ∧ (c.coordinates x).val=theta} :=
  overlap_image_formula c (pulledTarget e d)

theorem rep_change_from_actual_time_map (b : RepChange k region e c d)
    (x : Overlap c (pulledTarget e d)) :
    b.change.forward ((c.coordinates ⟨x.val,x.property.1⟩).val) =
      (d.coordinates ⟨e x.val,x.property.2⟩).val :=
  time_change_from_actual_charts c (pulledTarget e d) b x

def sourceAmbient (p : SourceSpace k region e c d) : c.target × Domain k region :=
  (⟨p.1.val,overlap_image_in_target c (pulledTarget e d) p.1.property⟩,p.2)
def targetAmbient (p : TargetSpace k region e c d) : d.target × Domain k region :=
  (⟨p.1.val,overlap_image_in_target (pulledTarget e d) c p.1.property⟩,p.2)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem rep_ambient_coordinates (p : SourceSpace k region e c d) :
    (sourceAmbient k region e c d p).1.val=p.1.val ∧
      (sourceAmbient k region e c d p).2=p.2 := ⟨rfl,rfl⟩

def RepCov (b : RepChange k region e c d)
    (R : Set (c.target × Domain k region)) (S : Set (d.target × Domain k region)) : Prop :=
  ∀ p, sourceAmbient k region e c d p ∈ R ↔
    targetAmbient k region e c d (b.change.map p) ∈ S

theorem rep_cov_independent_of_certificate
    (b q : RepChange k region e c d)
    (R : Set (c.target × Domain k region)) (S : Set (d.target × Domain k region)) :
    RepCov k region e c d b R S ↔ RepCov k region e c d q R S := by
  unfold RepCov
  simp only [bound_time_maps_unique c (pulledTarget e d) k region b q]

theorem rep_relation_restriction_image (b : RepChange k region e c d)
    (R : Set (c.target × Domain k region)) (S : Set (d.target × Domain k region))
    (cov : RepCov k region e c d b R S) :
    b.change.map '' {p | sourceAmbient k region e c d p ∈ R} =
      {p | targetAmbient k region e c d p ∈ S} :=
  bound_time_relation_image c (pulledTarget e d) b _ _ cov

theorem rep_time_change_preserves_value (b : RepChange k region e c d)
    (p : SourceSpace k region e c d) :
    (targetAmbient k region e c d (b.change.map p)).2.val 0 =
      (sourceAmbient k region e c d p).2.val 0 := b.change.preserves_zeroth_value p

end LCTR.CoreNativeTimeConditions
