import CoreLawComponentCharts

namespace LCTR.CoreTransportedLawCharts
set_option autoImplicit false
open Set LCTR.CoreLocalCharts LCTR.LawTimeTransport
variable {T U X Y TI : Type} {Val VI : Fin 2 → Type}

def pushChart (e : T ≃ U) (c : Chart T X) : Chart U X where
  source := {u | e.symm u ∈ c.source}
  target := c.target
  coordinates := {
    toFun := fun u => c.coordinates ⟨e.symm u.val,u.property⟩
    invFun := fun x => ⟨e (c.coordinates.symm x).val,by simp⟩
    left_inv := by
      intro u
      apply Subtype.ext
      change e (c.coordinates.symm (c.coordinates ⟨e.symm u.val,u.property⟩)).val=u.val
      rw [c.coordinates.symm_apply_apply,e.apply_symm_apply]
    right_inv := by
      intro x
      have h : (⟨e.symm (e (c.coordinates.symm x).val),by simp⟩ : c.source) =
        c.coordinates.symm x := Subtype.ext (e.symm_apply_apply _)
      change c.coordinates _ = x
      rw [h,c.coordinates.apply_symm_apply] }

def pushAtlas (e : T ≃ U) (a : Atlas T TI Val VI) : Atlas U TI Val VI where
  dim := a.dim
  value s u := a.value s (e.symm u)
  time j := pushChart e (a.time j)
  valChart := a.valChart
  timeIndexNonempty := a.timeIndexNonempty
  valueIndexNonempty := a.valueIndexNonempty
  timeOpen := a.timeOpen
  valueOpen := a.valueOpen
  cover := by
    intro u
    exact a.cover (e.symm u)

variable (e : T ≃ U) (a : Atlas T TI Val VI) (i : Index TI VI)

def liftJoint (x : JointDomain a i) : JointDomain (pushAtlas e a) i :=
  ⟨e x.val,by simpa [pushAtlas,pushChart] using x.property⟩

def unliftJoint (x : JointDomain (pushAtlas e a) i) : JointDomain a i :=
  ⟨e.symm x.val,x.property⟩

theorem joint_lift_inverse (x : JointDomain a i) :
    unliftJoint e a i (liftJoint e a i x) = x := Subtype.ext (e.symm_apply_apply _)

theorem joint_unlift_inverse (x : JointDomain (pushAtlas e a) i) :
    liftJoint e a i (unliftJoint e a i x) = x := Subtype.ext (e.apply_symm_apply _)

theorem numeric_time_preserved (x : JointDomain a i) :
    timeValue (pushAtlas e a) i (liftJoint e a i x) = timeValue a i x := by
  unfold timeValue pushAtlas pushChart liftJoint
  simp

theorem numeric_domain_preserved : NumericDomain (pushAtlas e a) i = NumericDomain a i := by
  ext theta
  constructor
  · rintro ⟨x,rfl⟩
    refine ⟨unliftJoint e a i x,?_⟩
    rw [← numeric_time_preserved e a i, joint_unlift_inverse]
  · rintro ⟨x,rfl⟩
    exact ⟨liftJoint e a i x,numeric_time_preserved e a i x⟩

theorem native_curve_preserved (x : JointDomain a i) (s : Fin 2) :
    curve (pushAtlas e a) i
      (timeCoord (pushAtlas e a) i (liftJoint e a i x)) s =
      curve a i (timeCoord a i x) s := by
  rw [side_curve_generated,side_curve_generated]
  apply congrArg (a.valChart s (i.2 s)).coordinates
  apply Subtype.ext
  change a.value s (e.symm (e x.val)) = a.value s x.val
  rw [e.symm_apply_apply]

def evaluationEquiv (r : Reindex T U) (c : Component T X Y) :
    {t // c.evalTime t} ≃ {u // (transport r c).evalTime u} where
  toFun := liftTime r c
  invFun := unliftTime r c
  left_inv := unlift_lift r c
  right_inv := lift_unlift r c

theorem same_transported_input (r : Reindex T U) (c : Component T X Y)
    (u : {u // (transport r c).evalTime u}) :
    (transport r c).input u = c.input ((evaluationEquiv r c).symm u) := rfl

theorem same_transported_output (r : Reindex T U) (c : Component T X Y)
    (u : {u // (transport r c).evalTime u}) :
    (transport r c).output u = c.output ((evaluationEquiv r c).symm u) := rfl

open LCTR.CoreNativeLawComponents LCTR.CoreLawComponentCharts
variable {C D B I : Type} {Values : I → Type}
variable (context : Context C D B I Values) (component : ComponentInput context)
variable (atlas : NativeAtlas context component TI VI)
variable (reindex : Reindex (NativeTime context) U)

noncomputable def transportedNativeAtlas :=
  pushAtlas (evaluationEquiv reindex (generated context component)) atlas.val

theorem transported_atlas_input_is_law_input
    (u : {u // (transport reindex (generated context component)).evalTime u}) :
    (transportedNativeAtlas context component atlas reindex).value 0 u =
      (transport reindex (generated context component)).input u :=
  same_law_values context component atlas 0 _

theorem transported_atlas_output_is_law_output
    (u : {u // (transport reindex (generated context component)).evalTime u}) :
    (transportedNativeAtlas context component atlas reindex).value 1 u =
      (transport reindex (generated context component)).output u :=
  same_law_values context component atlas 1 _

theorem transported_native_curve_agrees (j : Index TI VI) (x : JointDomain atlas.val j)
    (s : Fin 2) :
    curve (transportedNativeAtlas context component atlas reindex) j
      (timeCoord (transportedNativeAtlas context component atlas reindex) j
        (liftJoint (evaluationEquiv reindex (generated context component)) atlas.val j x)) s =
      curve atlas.val j (timeCoord atlas.val j x) s :=
  native_curve_preserved _ _ _ _ _

end LCTR.CoreTransportedLawCharts
