import Mathlib.Order.Hom.Basic
import LCTR.RepresentationImageOrderIsomorphismCore

namespace LCTR.CoreRepresentationImages
set_option autoImplicit false
open Set
universe u v w
variable {S : Type u} {Y : Type v} {Z : Type w}

def imageProjection (f : S → Y) (x : S) : range f := ⟨f x,⟨x,rfl⟩⟩

theorem imageProjection_surjective (f : S → Y) : Function.Surjective (imageProjection f) := by
  rintro ⟨y,x,hx⟩
  exact ⟨x,Subtype.ext hx⟩

noncomputable def imageMap (f : S → Y) (g : S → Z) : range f → range g :=
  fun y => ⟨g y.property.choose,⟨y.property.choose,rfl⟩⟩

theorem imageMap_commutes (f : S → Y) (g : S → Z)
    (kernel : ∀ x y, f x = f y → g x = g y) (x : S) :
    imageMap f g (imageProjection f x) = imageProjection g x := by
  apply Subtype.ext
  exact kernel _ x (imageProjection f x).property.choose_spec

theorem imageMap_unique (f : S → Y) (g : S → Z)
    (kernel : ∀ x y, f x = f y → g x = g y)
    (F : range f → range g) (commutes : ∀ x, F (imageProjection f x) = imageProjection g x) :
    F = imageMap f g := by
  funext y
  obtain ⟨x,rfl⟩ := imageProjection_surjective f y
  exact (commutes x).trans (imageMap_commutes f g kernel x).symm

noncomputable def imageEquiv (f : S → Y) (g : S → Z)
    (kernel : ∀ x y, f x = f y ↔ g x = g y) : range f ≃ range g where
  toFun := imageMap f g
  invFun := imageMap g f
  left_inv := by
    intro y
    obtain ⟨x,rfl⟩ := imageProjection_surjective f y
    rw [imageMap_commutes f g (fun x y => (kernel x y).mp),
      imageMap_commutes g f (fun x y => (kernel x y).mpr)]
  right_inv := by
    intro y
    obtain ⟨x,rfl⟩ := imageProjection_surjective g y
    rw [imageMap_commutes g f (fun x y => (kernel x y).mpr),
      imageMap_commutes f g (fun x y => (kernel x y).mp)]

theorem imageMap_strict_order [LinearOrder Y] [LinearOrder Z]
    (f : S → Y) (g : S → Z) (kernel : ∀ x y, f x = f y ↔ g x = g y)
    (ord : ∀ x y, f x < f y ↔ g x < g y) (a b : range f) :
    imageMap f g a < imageMap f g b ↔ a < b := by
  obtain ⟨x,rfl⟩ := imageProjection_surjective f a
  obtain ⟨y,rfl⟩ := imageProjection_surjective f b
  rw [imageMap_commutes f g (fun x y => (kernel x y).mp),
    imageMap_commutes f g (fun x y => (kernel x y).mp)]
  exact (ord x y).symm

noncomputable def imageOrderIso [LinearOrder Y] [LinearOrder Z]
    (f : S → Y) (g : S → Z) (kernel : ∀ x y, f x = f y ↔ g x = g y)
    (ord : ∀ x y, f x < f y ↔ g x < g y) : range f ≃o range g where
  toEquiv := imageEquiv f g kernel
  map_rel_iff' := by
    intro a b
    change imageMap f g a ≤ imageMap f g b ↔ a ≤ b
    rw [← not_lt,← not_lt,imageMap_strict_order f g kernel ord b a]

theorem image_order_iso_exists_unique [LinearOrder Y] [LinearOrder Z]
    (f : S → Y) (g : S → Z) (kernel : ∀ x y, f x = f y ↔ g x = g y)
    (ord : ∀ x y, f x < f y ↔ g x < g y) :
    ∃! F : range f ≃o range g, ∀ x, F (imageProjection f x) = imageProjection g x := by
  refine ⟨imageOrderIso f g kernel ord,?_,?_⟩
  · exact imageMap_commutes f g (fun x y => (kernel x y).mp)
  · intro F hF
    apply DFunLike.ext
    intro y
    exact congrFun (imageMap_unique f g (fun x y => (kernel x y).mp) F hF) y

theorem source_representation_image_uniqueness [LinearOrder Y] [LinearOrder Z]
    (same strict : S → S → Prop) (f : S → Y) (g : S → Z)
    (eq0 : ∀ x y, f x = f y ↔ same x y) (eq1 : ∀ x y, g x = g y ↔ same x y)
    (ord0 : ∀ x y, f x < f y ↔ strict x y) (ord1 : ∀ x y, g x < g y ↔ strict x y) :
    ∃! F : range f ≃o range g, ∀ x, F (imageProjection f x) = imageProjection g x := by
  have pair := LCTR.RepresentationImageOrderIsomorphismCore.equality_and_order_criteria_transfer
    same strict (· < ·) (· < ·) f g eq0 eq1 ord0 ord1
  exact image_order_iso_exists_unique f g pair.1 pair.2

theorem empty_source_image (f : Empty → Y) : IsEmpty (range f) := by
  constructor
  rintro ⟨y,x,_⟩
  exact Empty.elim x

theorem missing_kernel_control : ¬ ∃ F : Unit → Bool, ∀ x : Bool, F () = x := by
  rintro ⟨F,h⟩
  have bad : (true : Bool) = false := (h true).symm.trans (h false)
  cases bad

end LCTR.CoreRepresentationImages
