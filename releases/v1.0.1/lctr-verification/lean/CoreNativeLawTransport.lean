import CoreNativeCurves
import LCTR.LawFamilyTransport

namespace LCTR.CoreNativeLawTransport
set_option autoImplicit false
open LCTR.CoreObserverTime LCTR.CoreNativeCurves
open LCTR.LawTimeTransport LCTR.LawFamilyTransport
universe u v w
variable {C : Type u} {D : Type v} {B : Type w}

abbrev Part (d : Input C D B) (h : IncTrans d) (rho0 : RealEmbedding d h) (L : Set ℝ) :=
  {q : OrderDomain d h // realValue d h rho0 q ∈ L}
def baseValue (d : Input C D B) (h : IncTrans d) (rho0 : RealEmbedding d h) (L : Set ℝ) :
    Part d h rho0 L → L := fun q => ⟨realValue d h rho0 q.val, q.property⟩
def newValue (d : Input C D B) (h : IncTrans d) (rho0 rho : RealEmbedding d h) (L : Set ℝ) :
    Part d h rho0 L → ℝ := fun q => realValue d h rho q.val
abbrev NewTime (d : Input C D B) (h : IncTrans d) (rho0 rho : RealEmbedding d h) (L : Set ℝ) :=
  Set.range (newValue d h rho0 rho L)

theorem base_value_bijective (d : Input C D B) (h : IncTrans d) (rho0 : RealEmbedding d h)
    (L : Set ℝ) (within : L ⊆ Set.range (realValue d h rho0)) :
    Function.Bijective (baseValue d h rho0 L) := by
  constructor
  · intro x y same
    apply Subtype.ext
    apply Subtype.ext
    exact embedding_injective d h rho0 (congrArg Subtype.val same)
  · intro t
    obtain ⟨q, hq⟩ := within t.property
    exact ⟨⟨q, by rw [hq]; exact t.property⟩, Subtype.ext hq⟩

theorem new_value_injective (d : Input C D B) (h : IncTrans d) (rho0 rho : RealEmbedding d h)
    (L : Set ℝ) : Function.Injective (newValue d h rho0 rho L) := by
  intro x y same
  exact Subtype.ext (Subtype.ext (embedding_injective d h rho same))

noncomputable def changeEquiv (d : Input C D B) (h : IncTrans d) (rho0 rho : RealEmbedding d h)
    (L : Set ℝ) (within : L ⊆ Set.range (realValue d h rho0)) : L ≃ NewTime d h rho0 rho L :=
  (Equiv.ofBijective (baseValue d h rho0 L) (base_value_bijective d h rho0 L within)).symm.trans
    (Equiv.ofInjective (newValue d h rho0 rho L) (new_value_injective d h rho0 rho L))

theorem change_commutes (d : Input C D B) (h : IncTrans d) (rho0 rho : RealEmbedding d h)
    (L : Set ℝ) (within : L ⊆ Set.range (realValue d h rho0)) (q : Part d h rho0 L) :
    changeEquiv d h rho0 rho L within (baseValue d h rho0 L q) =
      ⟨newValue d h rho0 rho L q, ⟨q,rfl⟩⟩ := by
  let e0 := Equiv.ofBijective (baseValue d h rho0 L) (base_value_bijective d h rho0 L within)
  let e1 := Equiv.ofInjective (newValue d h rho0 rho L) (new_value_injective d h rho0 rho L)
  change e1 (e0.symm (e0 q)) = e1 q
  rw [e0.symm_apply_apply]

theorem change_identity_values (d : Input C D B) (h : IncTrans d) (rho0 : RealEmbedding d h)
    (L : Set ℝ) (within : L ⊆ Set.range (realValue d h rho0)) (t : L) :
    (changeEquiv d h rho0 rho0 L within t).val = t.val := by
  obtain ⟨q, rfl⟩ := (base_value_bijective d h rho0 L within).2 t
  rw [change_commutes]
  rfl

theorem changed_domain_contained (d : Input C D B) (h : IncTrans d) (rho0 rho : RealEmbedding d h)
    (L : Set ℝ) : Set.range (newValue d h rho0 rho L) ⊆ Set.range (realValue d h rho) := by
  rintro t ⟨q,rfl⟩
  exact ⟨q.val,rfl⟩

noncomputable def reindex (d : Input C D B) (h : IncTrans d) (rho0 rho : RealEmbedding d h)
    (L : Set ℝ) (within : L ⊆ Set.range (realValue d h rho0)) :
    Reindex L (NewTime d h rho0 rho L) where
  forward := changeEquiv d h rho0 rho L within
  inverse := (changeEquiv d h rho0 rho L within).symm
  left := (changeEquiv d h rho0 rho L within).symm_apply_apply
  right := (changeEquiv d h rho0 rho L within).apply_symm_apply

theorem native_five_conditions (d : Input C D B) (h : IncTrans d) (rho0 rho : RealEmbedding d h)
    (L : Set ℝ) (within : L ⊆ Set.range (realValue d h rho0))
    {A : Type} {X Y : A → Type} (f : Family L A X Y) :
    (K1 (transportFamily (reindex d h rho0 rho L within) f) ↔ K1 f) ∧
    (K2 (transportFamily (reindex d h rho0 rho L within) f) ↔ K2 f) ∧
    (K3 (transportFamily (reindex d h rho0 rho L within) f) ↔ K3 f) ∧
    (K4 (transportFamily (reindex d h rho0 rho L within) f) ↔ K4 f) ∧
    (K5 (transportFamily (reindex d h rho0 rho L within) f) ↔ K5 f) :=
  ⟨condition1_preserved _ _, condition2_preserved _ _, condition3_preserved _ _,
    condition4_preserved _ _, condition5_preserved _ _⟩

theorem native_common_domain_image (d : Input C D B) (h : IncTrans d) (rho0 rho : RealEmbedding d h)
    (L : Set ℝ) (within : L ⊆ Set.range (realValue d h rho0))
    {A : Type} {X Y : A → Type} (f : Family L A X Y) :
    common (transportFamily (reindex d h rho0 rho L within) f) =
      image (reindex d h rho0 rho L within) (common f) := common_is_image _ _

theorem native_admissible_family_image (d : Input C D B) (h : IncTrans d) (rho0 rho : RealEmbedding d h)
    (L : Set ℝ) (within : L ⊆ Set.range (realValue d h rho0))
    {A : Type} {X Y : A → Type} (f : Family L A X Y)
    (Q : NewTime d h rho0 rho L → Prop) :
    (transportFamily (reindex d h rho0 rho L within) f).admissibleCommon Q ↔
      ∃ P, f.admissibleCommon P ∧ Q = image (reindex d h rho0 rho L within) P :=
  admissible_family_is_image _ _ _

theorem native_evaluation_tuple (d : Input C D B) (h : IncTrans d) (rho0 rho : RealEmbedding d h)
    (L : Set ℝ) (within : L ⊆ Set.range (realValue d h rho0))
    {X Y : Type} (c : Component L X Y) (t : {t // c.evalTime t}) :
    evalTuple (transport (reindex d h rho0 rho L within) c)
        (liftTime (reindex d h rho0 rho L within) c t) =
      (tupleReindex (reindex d h rho0 rho L within)).forward (evalTuple c t) :=
  evaluation_tuple_transport _ _ _

def reverseReindex {T : Type} (e : Reindex T T) : Reindex T T where
  forward := e.inverse
  inverse := e.forward
  left := e.right
  right := e.left

theorem inverse_image_invariance {T : Type} (P : T → Prop) (e : Reindex T T)
    (inv : ImageInvariant P e) :
    ImageInvariant P (reverseReindex e) ∧ (∀ z, P z ↔ P (e.inverse z)) := by
  have pointwise : ∀ z, P z ↔ P (e.inverse z) := by
    intro z
    have hz := (image_invariance_iff P e).mp inv (e.inverse z)
    simpa [e.right] using hz
  exact ⟨(image_invariance_iff P (reverseReindex e)).mpr (fun z => (pointwise z).symm), pointwise⟩

theorem faithful_candidate_inverse {T A : Type} {X Y : A → Type} (f : Family T A X Y)
    (k4 : K4 f) (phi : (a : A) → Reindex (Tuple T (X a) (Y a)) (Tuple T (X a) (Y a)))
    (allowed : f.faithful phi) (a : A) :
    ImageInvariant (tupleRelation (f.component a)) (reverseReindex (phi a)) ∧
    (∀ z, tupleRelation (f.component a) z ↔ tupleRelation (f.component a) ((phi a).inverse z)) :=
  inverse_image_invariance _ _ (k4 phi allowed a)

end LCTR.CoreNativeLawTransport
