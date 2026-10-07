import CoreNativeJointJets

namespace LCTR.CoreNativeChartOverlaps
set_option autoImplicit false
open Set LCTR.CoreLocalCharts LCTR.CoreRepresentationImages
open LCTR.CoreValueJetChanges LCTR.CoreDifferentialCovariance
variable {X E F : Type}
variable (c : Chart X E) (d : Chart X F)

abbrev Overlap := c.source ∩ d.source
def overlapValue (x : Overlap c d) : E := (c.coordinates ⟨x.val,x.property.1⟩).val
abbrev OverlapImage := Set.range (overlapValue c d)

theorem overlap_value_injective : Function.Injective (overlapValue c d) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : c.source => z.val) (c.coordinates.injective (Subtype.ext h))

noncomputable def overlapCoordinates : Overlap c d ≃ OverlapImage c d :=
  Equiv.ofBijective (imageProjection (overlapValue c d))
    ⟨fun _ _ h => overlap_value_injective c d
      (congrArg (fun z : OverlapImage c d => z.val) h),imageProjection_surjective _⟩

def swapOverlap : Overlap c d ≃ Overlap d c where
  toFun x := ⟨x.val,x.property.2,x.property.1⟩
  invFun x := ⟨x.val,x.property.2,x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def chartChange : OverlapImage c d ≃ OverlapImage d c :=
  ((overlapCoordinates c d).symm.trans (swapOverlap c d)).trans (overlapCoordinates d c)

theorem overlap_image_formula : OverlapImage c d =
    {v | ∃ x : c.source, x.val ∈ d.source ∧ (c.coordinates x).val=v} := by
  ext v
  constructor
  · rintro ⟨x,h⟩
    exact ⟨⟨x.val,x.property.1⟩,x.property.2,h⟩
  · rintro ⟨x,hx,hv⟩
    exact ⟨⟨x.val,x.property,hx⟩,hv⟩

theorem overlap_image_in_target : OverlapImage c d ⊆ c.target := by
  rintro _ ⟨x,rfl⟩
  exact (c.coordinates ⟨x.val,x.property.1⟩).property

theorem chart_change_formula (x : Overlap c d) :
    (chartChange c d (overlapCoordinates c d x)).val =
      (d.coordinates ⟨x.val,x.property.2⟩).val := by
  unfold chartChange
  simp only [Equiv.trans_apply,Equiv.symm_apply_apply]
  rfl

theorem chart_change_bijective : Function.Bijective (chartChange c d) := (chartChange c d).bijective

theorem chart_change_inverse (v : OverlapImage c d) : chartChange d c (chartChange c d v) = v := by
  obtain ⟨x,rfl⟩ := (overlapCoordinates c d).surjective v
  unfold chartChange
  simp only [Equiv.trans_apply,Equiv.symm_apply_apply]
  rfl

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

structure BoundValueChange (k : ℕ) (U : Set ℝ) where
  change : ValueChange k U (OverlapImage c d) (OverlapImage d c)
  forward_exact : ∀ v : OverlapImage c d, change.forward v.val = (chartChange c d v).val
  backward_exact : ∀ v : OverlapImage d c, change.backward v.val = (chartChange d c v).val

theorem value_change_from_actual_charts {k : ℕ} {U : Set ℝ}
    (b : BoundValueChange c d k U) (x : Overlap c d) :
    b.change.forward ((c.coordinates ⟨x.val,x.property.1⟩).val) =
      (d.coordinates ⟨x.val,x.property.2⟩).val :=
  (b.forward_exact (overlapCoordinates c d x)).trans (chart_change_formula c d x)

theorem bound_value_relation_image {k : ℕ} {U : Set ℝ}
    (b : BoundValueChange c d k U)
    (R : Set (U × Domain k (OverlapImage c d)))
    (S : Set (U × Domain k (OverlapImage d c)))
    (cov : ∀ p, p ∈ R ↔ b.change.map p ∈ S) :
    b.change.map '' R = S := b.change.relation_image R S cov

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (ct dt : Chart X ℝ)
structure BoundTimeChange (k : ℕ) (region : Set V) where
  change : TimeChange k region (OverlapImage ct dt) (OverlapImage dt ct)
  forward_exact : ∀ v : OverlapImage ct dt, change.forward v.val = (chartChange ct dt v).val
  backward_exact : ∀ v : OverlapImage dt ct, change.backward v.val = (chartChange dt ct v).val

theorem time_change_from_actual_charts {k : ℕ} {region : Set V}
    (b : BoundTimeChange ct dt k region) (x : Overlap ct dt) :
    b.change.forward ((ct.coordinates ⟨x.val,x.property.1⟩).val) =
      (dt.coordinates ⟨x.val,x.property.2⟩).val :=
  (b.forward_exact (overlapCoordinates ct dt x)).trans (chart_change_formula ct dt x)

theorem bound_time_relation_image {k : ℕ} {region : Set V}
    (b : BoundTimeChange ct dt k region)
    (R : Set (OverlapImage ct dt × Domain k region))
    (S : Set (OverlapImage dt ct × Domain k region))
    (cov : ∀ p, p ∈ R ↔ b.change.map p ∈ S) :
    b.change.map '' R = S := b.change.relation_image R S cov

variable {T TI : Type} {Val VI : Fin 2 → Type}
variable (a : Atlas T TI Val VI) (beta : (s : Fin 2) → VI s)

def productChart : Chart ((s : Fin 2) → Val s) (LCTR.CoreNativeJointJets.JointValue a) where
  source := {v | ∀ s, v s ∈ (a.valChart s (beta s)).source}
  target := {v | ∀ s, v s ∈ (a.valChart s (beta s)).target}
  coordinates := {
    toFun := fun v => ⟨fun s => ((a.valChart s (beta s)).coordinates ⟨v.val s,v.property s⟩).val,
      fun s => ((a.valChart s (beta s)).coordinates ⟨v.val s,v.property s⟩).property⟩
    invFun := fun v => ⟨fun s => ((a.valChart s (beta s)).coordinates.symm ⟨v.val s,v.property s⟩).val,
      fun s => ((a.valChart s (beta s)).coordinates.symm ⟨v.val s,v.property s⟩).property⟩
    left_inv := by
      intro v
      apply Subtype.ext
      funext s
      exact congrArg Subtype.val ((a.valChart s (beta s)).coordinates.symm_apply_apply ⟨v.val s,v.property s⟩)
    right_inv := by
      intro v
      apply Subtype.ext
      funext s
      exact congrArg Subtype.val ((a.valChart s (beta s)).coordinates.apply_symm_apply ⟨v.val s,v.property s⟩) }

theorem product_chart_region (alpha : TI) :
    (productChart a beta).target = LCTR.CoreNativeJointJets.jointRegion a (alpha,beta) := rfl

theorem product_chart_at_generated_values (alpha : TI) (x : JointDomain a (alpha,beta)) :
    ((productChart a beta).coordinates ⟨fun s => a.value s x.val,x.property.2⟩).val =
      fun s => (curve a (alpha,beta) (timeCoord a (alpha,beta) x) s).val := by
  funext s
  exact (congrArg Subtype.val (side_curve_generated a (alpha,beta) x s)).symm

end LCTR.CoreNativeChartOverlaps
