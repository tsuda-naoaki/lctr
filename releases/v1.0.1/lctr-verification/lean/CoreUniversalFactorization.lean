import CoreRepresentationImages
import CoreJointDescent
import OrderEmbeddingBridge
import LCTR.QuotientFactorization

namespace LCTR.CoreUniversalFactorization
open Set LCTR.CoreRepresentationImages
open LCTR.OrderEmbeddingBridgeV1 LCTR.TransitiveIncomparabilityQuotientCore
universe u v w z

theorem surjective_factor_exists_unique {S : Type u} {Q : Type v} {T : Type w}
    (p : S → Q) (f : S → T) (onto : Function.Surjective p)
    (kernel : ∀ x y, p x = p y → f x = f y) :
    ∃! F : Q → T, f = F ∘ p := by
  obtain ⟨F, hF, unique⟩ :=
    LCTR.Trajectory.surjective_fiber_invariant_map_factors_uniquely p f onto kernel
  refine ⟨F, funext hF, ?_⟩
  intro G hG
  exact unique G (fun x => congrFun hG x)

theorem precomposition_cancellation {S : Type u} {Q : Type v} {T : Type w}
    (p : S → Q) (onto : Function.Surjective p) (f g : Q → T)
    (same : f ∘ p = g ∘ p) : f = g := by
  funext q
  obtain ⟨x, rfl⟩ := onto q
  exact congrFun same x

def comparisonFactor {S : Type u} {T : Type v} (s : Setoid S) (f : S → T)
    (respects : ∀ x y, s.r x y → f x = f y) : Quotient s → T :=
  Quotient.lift f respects

theorem comparison_factor_unique {S : Type u} {T : Type v} (s : Setoid S) (f : S → T)
    (respects : ∀ x y, s.r x y → f x = f y) :
    ∃! F : Quotient s → T, ∀ x, F (Quotient.mk s x) = f x := by
  refine ⟨comparisonFactor s f respects, fun _ => rfl, ?_⟩
  intro F hF
  funext q
  induction q using Quotient.inductionOn with
  | _ x => exact hF x

theorem comparison_relation_factorization
    {S : Fin 2 → Type u} {T : Fin 2 → Type v}
    (s : (i : Fin 2) → Setoid (S i)) (f : (i : Fin 2) → S i → T i)
    (respects : ∀ i x y, (s i).r x y → f i x = f i y)
    (paired relation : Set ((i : Fin 2) → S i)) (typed : relation ⊆ paired)
    (saturated : ∀ x ∈ paired, ∀ y ∈ paired,
      (∀ i, (s i).r (x i) (y i)) → (x ∈ relation ↔ y ∈ relation))
    (target : Set ((i : Fin 2) → T i))
    (compatibility : ∀ x ∈ paired, (fun i => f i (x i)) ∈ target ↔ x ∈ relation)
    (x : (i : Fin 2) → S i) (hx : x ∈ paired) :
    (fun i => comparisonFactor (s i) (f i) (respects i) (Quotient.mk (s i) (x i))) ∈ target ↔
      LCTR.CoreJointDescent.prodPrj s x ∈ LCTR.CoreJointDescent.prodPrj s '' relation := by
  change (fun i => f i (x i)) ∈ target ↔ _
  rw [compatibility x hx]
  constructor
  · exact fun h => ⟨x,h,rfl⟩
  · rintro ⟨y,hy,hq⟩
    exact (saturated y (typed hy) x hx
      ((LCTR.CoreJointDescent.prodPrj_kernel s y x).mpr hq)).mp hy

noncomputable def quotientImageEquiv {S : Type u} {Y : Type v}
    (r : S → S → Prop) (irr : ∀ x, ¬ r x x)
    (inc : ∀ {x y z}, Inc r x y → Inc r y z → Inc r x z)
    (f : S → Y) (kernel : ∀ x y, f x = f y ↔ Inc r x y) :
    IncQuotient r irr inc ≃ range f where
  toFun := Quotient.lift (imageProjection f) (fun x y h => Subtype.ext ((kernel x y).mpr h))
  invFun := fun a => proj r irr inc a.property.choose
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ x =>
      apply Quotient.sound
      exact (kernel _ x).mp (imageProjection f x).property.choose_spec
  right_inv := by
    intro a
    apply Subtype.ext
    exact a.property.choose_spec

theorem quotient_factor_commutes {S : Type u} {Y : Type v}
    (r : S → S → Prop) (irr : ∀ x, ¬ r x x)
    (inc : ∀ {x y z}, Inc r x y → Inc r y z → Inc r x z)
    (f : S → Y) (kernel : ∀ x y, f x = f y ↔ Inc r x y) (x : S) :
    quotientImageEquiv r irr inc f kernel (proj r irr inc x) = imageProjection f x := rfl

theorem quotient_factor_strict_order {S : Type u} {Y : Type v}
    (r : S → S → Prop) (irr : ∀ x, ¬ r x x)
    (trans : ∀ {x y z}, r x y → r y z → r x z)
    (inc : ∀ {x y z}, Inc r x y → Inc r y z → Inc r x z)
    (f : S → Y) (kernel : ∀ x y, f x = f y ↔ Inc r x y)
    (lt : Y → Y → Prop) (ord : ∀ x y, lt (f x) (f y) ↔ r x y)
    (a b : IncQuotient r irr inc) :
    lt (quotientImageEquiv r irr inc f kernel a).val
      (quotientImageEquiv r irr inc f kernel b).val ↔ quotientLt r irr inc a b := by
  induction a using Quotient.inductionOn with
  | _ x =>
    induction b using Quotient.inductionOn with
    | _ y =>
      change lt (f x) (f y) ↔ quotientLt r irr inc (proj r irr inc x) (proj r irr inc y)
      exact (ord x y).trans (quotientLt_proj_iff r irr trans inc x y).symm

theorem quotient_factor_exists_unique {S : Type u} {Y : Type v}
    (r : S → S → Prop) (irr : ∀ x, ¬ r x x)
    (trans : ∀ {x y z}, r x y → r y z → r x z)
    (inc : ∀ {x y z}, Inc r x y → Inc r y z → Inc r x z)
    (f : S → Y) (kernel : ∀ x y, f x = f y ↔ Inc r x y)
    (lt : Y → Y → Prop) (ord : ∀ x y, lt (f x) (f y) ↔ r x y) :
    ∃! F : IncQuotient r irr inc ≃ range f,
      (∀ x, F (proj r irr inc x) = imageProjection f x) ∧
      (∀ a b, lt (F a).val (F b).val ↔ quotientLt r irr inc a b) := by
  refine ⟨quotientImageEquiv r irr inc f kernel,
    ⟨quotient_factor_commutes r irr inc f kernel,
      quotient_factor_strict_order r irr trans inc f kernel lt ord⟩, ?_⟩
  intro F hF
  apply Equiv.ext
  intro q
  obtain ⟨x,rfl⟩ := proj_surjective r irr inc q
  exact hF.1 x

def restrictToImage {A : Type u} {Q : Type v} {Y : Type w}
    (p : A → Q) (f : Q → Y) (q : range p) : range (f ∘ p) :=
  ⟨f q.val, by obtain ⟨x,hx⟩ := q.property; exact ⟨x, congrArg f hx⟩⟩

theorem overlap_factor_naturality {A : Type u} {Q Q' : Type v} {Y Y' : Type w}
    (p : A → Q) (q : A → Q') (f : Q → Y) (g : Q' → Y')
    (canonicalChange : range p → range q) (targetChange : range (f ∘ p) → range (g ∘ q))
    (native : ∀ x, canonicalChange (imageProjection p x) = imageProjection q x)
    (target : ∀ x, targetChange (imageProjection (f ∘ p) x) = imageProjection (g ∘ q) x) :
    restrictToImage q g ∘ canonicalChange = targetChange ∘ restrictToImage p f := by
  funext a
  obtain ⟨x,rfl⟩ := imageProjection_surjective p a
  change restrictToImage q g (canonicalChange (imageProjection p x)) =
    targetChange (imageProjection (f ∘ p) x)
  rw [native x, target x]
  rfl

theorem reparametrization_unique {S : Type u} {Y : Type v} {Z : Type w}
    [LinearOrder Y] [LinearOrder Z] (same strict : S → S → Prop)
    (f : S → Y) (g : S → Z)
    (eqf : ∀ x y, f x = f y ↔ same x y) (eqg : ∀ x y, g x = g y ↔ same x y)
    (ordf : ∀ x y, f x < f y ↔ strict x y) (ordg : ∀ x y, g x < g y ↔ strict x y) :
    ∃! F : range f ≃o range g, ∀ x, F (imageProjection f x) = imageProjection g x :=
  source_representation_image_uniqueness same strict f g eqf eqg ordf ordg

end LCTR.CoreUniversalFactorization
