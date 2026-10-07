import Std




namespace LCTR.JointTimeReadiness
set_option autoImplicit false
universe u v w z

def CommonDomain {I : Type u} {Q : Type v} (D : I → Q → Prop) :=
  {q : Q // ∀ i, D i q}

def Joint {I : Type u} {Q : Type v} {B : I → Type w}
    (D : I → Q → Prop) (curve : (i : I) → {q : Q // D i q} → B i)
    (q : CommonDomain D) : (i : I) → B i :=
  fun i => curve i ⟨q.val,q.property i⟩

theorem common_domain_projects {I : Type u} {Q : Type v}
    (D : I → Q → Prop) (q : CommonDomain D) (i : I) : D i q.val :=
  q.property i

theorem joint_component {I : Type u} {Q : Type v} {B : I → Type w}
    (D : I → Q → Prop) (curve : (i : I) → {q : Q // D i q} → B i)
    (q : CommonDomain D) (i : I) :
    Joint D curve q i = curve i ⟨q.val,q.property i⟩ := rfl

theorem joint_unique {I : Type u} {Q : Type v} {B : I → Type w}
    (D : I → Q → Prop) (curve : (i : I) → {q : Q // D i q} → B i)
    (f : CommonDomain D → (i : I) → B i)
    (component : ∀ q i, f q i = curve i ⟨q.val,q.property i⟩) :
    f = Joint D curve := by
  funext q i
  exact component q i

def Pullback {I : Type u} {Q : Type v} {B : I → Type w} {V : Type z}
    (D : I → Q → Prop) (curve : (i : I) → {q : Q // D i q} → B i)
    (r : ((i : I) → B i) → V → Prop) : CommonDomain D → V → Prop :=
  fun q v => r (Joint D curve q) v

theorem joint_relation_membership {I : Type u} {Q : Type v}
    {B : I → Type w} {V : Type z}
    (D : I → Q → Prop) (curve : (i : I) → {q : Q // D i q} → B i)
    (r : ((i : I) → B i) → V → Prop) (q : CommonDomain D) (v : V) :
    Pullback D curve r q v ↔ r (Joint D curve q) v := Iff.rfl

theorem real_time_unambiguous {I : Type u} {Q : Type v} {B : I → Type w}
    {T : Type z} (D : I → Q → Prop)
    (curve : (i : I) → {q : Q // D i q} → B i)
    (rho : Q → T) (inj : ∀ a b, rho a = rho b → a = b)
    (q₁ q₂ : CommonDomain D) (same : rho q₁.val = rho q₂.val) :
    Joint D curve q₁ = Joint D curve q₂ := by
  have h : q₁ = q₂ := Subtype.ext (inj _ _ same)
  exact congrArg (Joint D curve) h

theorem individual_domains_can_be_nonempty :
    ∀ i : Bool, ∃ q : Bool, q = i := fun i => ⟨i,rfl⟩

theorem common_domain_can_be_empty :
    ¬ ∃ q : Bool, ∀ i : Bool, q = i := by
  intro ⟨q,h⟩
  have bad : false = true := (h false).symm.trans (h true)
  cases bad

def Descends {S : Type u} {V : Type v} (e : S → S → Prop) (f : S → V) :=
  ∀ x y, e x y → f x = f y

theorem state_trajectory_does_not_force_observable_descent :
    (∃ curve : Unit → Unit, ∀ t, curve t = ()) ∧
    ¬ Descends (fun (_ _ : Bool) => True) (fun b => b) := by
  constructor
  · exact ⟨fun _ => (), fun _ => rfl⟩
  · intro h
    have bad : false = true := h false true True.intro
    cases bad

theorem relation_value_curves_need_selection :
    ∃ f g : Unit → Bool,
      (∀ t, (fun (_ : Unit) (_ : Bool) => True) t (f t)) ∧
      (∀ t, (fun (_ : Unit) (_ : Bool) => True) t (g t)) ∧ f ≠ g := by
  refine ⟨fun _ => false, fun _ => true, fun _ => True.intro,
    fun _ => True.intro, ?_⟩
  intro h
  have bad : false = true := congrFun h ()
  cases bad

theorem different_generated_equivalences_are_possible :
    ∃ e₁ e₂ : Bool → Bool → Prop,
      (∀ x, e₁ x x) ∧ (∀ x, e₂ x x) ∧
      (∀ x y, e₁ x y → e₁ y x) ∧ (∀ x y, e₂ x y → e₂ y x) ∧
      (∀ x y z, e₁ x y → e₁ y z → e₁ x z) ∧
      (∀ x y z, e₂ x y → e₂ y z → e₂ x z) ∧ e₁ ≠ e₂ := by
  refine ⟨Eq, fun _ _ => True, fun _ => rfl, fun _ => True.intro,
    fun _ _ h => h.symm, fun _ _ _ => True.intro,
    fun _ _ _ h k => h.trans k, fun _ _ _ _ _ => True.intro, ?_⟩
  intro h
  have truth : (false = true) = True := congrFun (congrFun h false) true
  have bad : false = true := truth.mpr True.intro
  cases bad

#print axioms common_domain_projects
#print axioms joint_component
#print axioms joint_unique
#print axioms joint_relation_membership
#print axioms real_time_unambiguous
#print axioms individual_domains_can_be_nonempty
#print axioms common_domain_can_be_empty
#print axioms state_trajectory_does_not_force_observable_descent
#print axioms relation_value_curves_need_selection
#print axioms different_generated_equivalences_are_possible
end LCTR.JointTimeReadiness
