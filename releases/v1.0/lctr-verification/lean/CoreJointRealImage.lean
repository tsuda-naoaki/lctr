import CoreJointLawEvaluation

namespace LCTR.CoreJointRealImage
set_option autoImplicit false
open LCTR.CoreJointLawEvaluation LCTR.CoreJointTime LCTR.CoreNativeJointRelation
variable {C D B I R : Type} (c : Context C D B I R)

theorem domain_image :
    RealTime c = c.rho.value '' {q | ∀ i, individualDomain c.objects c.base i q} := by
  ext t
  constructor
  · rintro ⟨q,hq⟩
    exact ⟨q.val,q.property,hq⟩
  · rintro ⟨q,hq,ht⟩
    exact ⟨⟨q,hq⟩,ht⟩

theorem projection_inverse (t : RealTime c) :
    realProjection c (orderInverse c t) = t := by
  apply Subtype.ext
  exact LCTR.ImageInverseConstruction.inverse_right (realValue c) t

theorem relation_image (r : R) :
    realRelation c r =
      (fun p : CommonDomain c.objects c.base × c.relValue r => (realProjection c p.1,p.2)) ''
        jointRelation c.objects c.base (c.sourceRelation r) := by
  ext p
  constructor
  · intro h
    exact ⟨(orderInverse c p.1,p.2),h,Prod.ext (projection_inverse c p.1) rfl⟩
  · rintro ⟨⟨q,v⟩,h,rfl⟩
    change (orderInverse c (realProjection c q),v) ∈ jointRelation c.objects c.base (c.sourceRelation r)
    rw [inverse_on_projection]
    exact h

theorem ambient_relation_image (r : R) (t : RealTime c) (v : c.relValue r) :
    (t,v) ∈ realRelation c r ↔
      (t.val,v) ∈ (fun p : CommonDomain c.objects c.base × c.relValue r => (realValue c p.1,p.2)) ''
        jointRelation c.objects c.base (c.sourceRelation r) := by
  rw [relation_image]
  constructor
  · rintro ⟨p,h,hp⟩
    exact ⟨p,h,congrArg (fun z : RealTime c × c.relValue r => (z.1.val,z.2)) hp⟩
  · rintro ⟨p,h,hp⟩
    have ht : realValue c p.1 = t.val := congrArg (fun z : ℝ × c.relValue r => z.1) hp
    have hv : p.2 = v := congrArg (fun z : ℝ × c.relValue r => z.2) hp
    exact ⟨p,h,Prod.ext (Subtype.ext ht) hv⟩

end LCTR.CoreJointRealImage
