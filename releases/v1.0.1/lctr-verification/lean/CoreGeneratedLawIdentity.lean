import CoreLawTransportIdentity

namespace LCTR.CoreGeneratedLawIdentity
set_option autoImplicit false
open LCTR.LawTimeTransport LCTR.LawFamilyTransport LCTR.CoreLawTransportIdentity
variable {Q T U A : Type} {X Y : A → Type}

def coordinateChange (base : Reindex Q T) (newer : Reindex Q U) : Reindex T U where
  forward t := newer.forward (base.inverse t)
  inverse u := base.forward (newer.inverse u)
  left t := by rw [newer.left, base.right]
  right u := by rw [base.left, newer.right]

theorem coordinate_change_bijection (base : Reindex Q T) (newer : Reindex Q U) :
    (∀ t, (coordinateChange base newer).inverse
      ((coordinateChange base newer).forward t) = t) ∧
    (∀ u, (coordinateChange base newer).forward
      ((coordinateChange base newer).inverse u) = u) :=
  ⟨(coordinateChange base newer).left, (coordinateChange base newer).right⟩

theorem coordinate_change_on_source (base : Reindex Q T) (newer : Reindex Q U) (q : Q) :
    (coordinateChange base newer).forward (base.forward q) = newer.forward q := by
  simp only [coordinateChange, base.left]

theorem coordinate_change_unique (base : Reindex Q T) (newer : Reindex Q U)
    (f : T → U) (commutes : ∀ q, f (base.forward q) = newer.forward q) :
    f = (coordinateChange base newer).forward := by
  funext t
  have h := commutes (base.inverse t)
  rw [base.right] at h
  exact h

theorem base_coordinate_identity (base : Reindex Q T) :
    coordinateChange base base = identityReindex T := by
  apply identity_reindex_unique
  exact base.right

theorem base_family_identity (base : Reindex Q T) (d : Family T A X Y) :
    transportFamily (coordinateChange base base) d = d := by
  rw [base_coordinate_identity, family_identity_transport]

end LCTR.CoreGeneratedLawIdentity
