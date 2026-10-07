namespace LCTR.RepresentationImageOrderIsomorphismCore

universe u v w

theorem equality_and_order_criteria_transfer
    {S : Type u}
    {Y0 : Type v}
    {Y1 : Type w}
    (same strict : S → S → Prop)
    (lt0 : Y0 → Y0 → Prop)
    (lt1 : Y1 → Y1 → Prop)
    (f0 : S → Y0)
    (f1 : S → Y1)
    (eq0 : ∀ x y, f0 x = f0 y ↔ same x y)
    (eq1 : ∀ x y, f1 x = f1 y ↔ same x y)
    (ord0 : ∀ x y, lt0 (f0 x) (f0 y) ↔ strict x y)
    (ord1 : ∀ x y, lt1 (f1 x) (f1 y) ↔ strict x y) :
    (∀ x y, f0 x = f0 y ↔ f1 x = f1 y) ∧
      (∀ x y, lt0 (f0 x) (f0 y) ↔ lt1 (f1 x) (f1 y)) := by
  constructor
  · intro x y
    exact (eq0 x y).trans (eq1 x y).symm
  · intro x y
    exact (ord0 x y).trans (ord1 x y).symm

theorem commuting_factor_map_is_unique
    {S : Type u}
    {Y0 : Type v}
    {Y1 : Type w}
    (f0 : S → Y0)
    (f1 : S → Y1)
    (surjective0 : Function.Surjective f0)
    (iso0 iso1 : Y0 → Y1)
    (commutes0 : ∀ x, iso0 (f0 x) = f1 x)
    (commutes1 : ∀ x, iso1 (f0 x) = f1 x) :
    iso0 = iso1 := by
  funext y
  obtain ⟨x, rfl⟩ := surjective0 y
  exact (commutes0 x).trans (commutes1 x).symm

theorem commuting_factor_map_is_bijective
    {S : Type u}
    {Y0 : Type v}
    {Y1 : Type w}
    (same : S → S → Prop)
    (f0 : S → Y0)
    (f1 : S → Y1)
    (eq0 : ∀ x y, f0 x = f0 y ↔ same x y)
    (eq1 : ∀ x y, f1 x = f1 y ↔ same x y)
    (surjective0 : Function.Surjective f0)
    (surjective1 : Function.Surjective f1)
    (iso : Y0 → Y1)
    (commutes : ∀ x, iso (f0 x) = f1 x) :
    Function.Injective iso ∧ Function.Surjective iso := by
  constructor
  · intro y0 y1 h
    obtain ⟨x0, rfl⟩ := surjective0 y0
    obtain ⟨x1, rfl⟩ := surjective0 y1
    apply (eq0 x0 x1).mpr
    apply (eq1 x0 x1).mp
    exact (commutes x0).symm.trans (h.trans (commutes x1))
  · intro y
    obtain ⟨x, rfl⟩ := surjective1 y
    exact ⟨f0 x, commutes x⟩

#print axioms equality_and_order_criteria_transfer
#print axioms commuting_factor_map_is_unique
#print axioms commuting_factor_map_is_bijective

end LCTR.RepresentationImageOrderIsomorphismCore
