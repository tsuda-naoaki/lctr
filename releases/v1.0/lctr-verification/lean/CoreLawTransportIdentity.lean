import LCTR.LawFamilyTransport

namespace LCTR.CoreLawTransportIdentity
set_option autoImplicit false
open LCTR.LawTimeTransport LCTR.LawFamilyTransport
variable {T A X Y : Type} {IX OY : A → Type}

theorem identity_reindex_unique (e : Reindex T T)
    (same : ∀ t, e.forward t = t) : e = identityReindex T := by
  have inv : ∀ t, e.inverse t = t := by
    intro t
    simpa only [same t] using e.left t
  cases e with
  | mk forward inverse left right =>
    have hf : forward = id := funext same
    have hi : inverse = id := funext inv
    subst forward
    subst inverse
    rfl

theorem component_identity_transport (c : Component T X Y) :
    transport (identityReindex T) c = c := by
  cases c
  rfl

theorem tuple_identity_reindex :
    tupleReindex (X := X) (Y := Y) (identityReindex T) =
      identityReindex (Tuple T X Y) := by
  rfl

theorem conjugate_identity_transport (phi : Reindex T T) :
    conjugate (identityReindex T) phi = phi := by
  cases phi
  rfl

theorem faithful_identity_transport (d : Family T A IX OY) :
    (transportFamily (identityReindex T) d).faithful = d.faithful := by
  funext psi
  apply propext
  change (∃ phi, d.faithful phi ∧
    psi = fun a => conjugate (tupleReindex (identityReindex T)) (phi a)) ↔ _
  simp only [tuple_identity_reindex, conjugate_identity_transport]
  exact ⟨fun ⟨phi, h, eq⟩ => eq ▸ h, fun h => ⟨psi, h, rfl⟩⟩

theorem family_identity_transport (d : Family T A IX OY) :
    transportFamily (identityReindex T) d = d := by
  have hf := faithful_identity_transport d
  cases d
  simp only [transportFamily] at hf ⊢
  rw [hf]
  simp only [component_identity_transport]
  rfl

theorem family_identity_from_values (d : Family T A IX OY) (e : Reindex T T)
    (same : ∀ t, e.forward t = t) : transportFamily e d = d := by
  rw [identity_reindex_unique e same, family_identity_transport]

end LCTR.CoreLawTransportIdentity
