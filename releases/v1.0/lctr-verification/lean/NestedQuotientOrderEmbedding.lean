import Std

namespace LCTR.NestedQuotientOrderEmbedding

noncomputable def lift {A Q R : Type} (p : A → Q) (b : A → R)
    (surj : ∀ q, ∃ a, p a = q) : Q → R :=
  fun q => b (Classical.choose (surj q))

theorem lift_commutes {A Q R : Type} (p : A → Q) (b : A → R)
    (surj : ∀ q, ∃ a, p a = q)
    (kernel : ∀ a a', p a = p a' ↔ b a = b a') (a : A) :
    lift p b surj (p a) = b a := by
  exact (kernel (Classical.choose (surj (p a))) a).mp
    (Classical.choose_spec (surj (p a)))

theorem lift_injective {A Q R : Type} (p : A → Q) (b : A → R)
    (surj : ∀ q, ∃ a, p a = q)
    (kernel : ∀ a a', p a = p a' ↔ b a = b a')
    (q q' : Q) (h : lift p b surj q = lift p b surj q') : q = q' := by
  have eq := (kernel (Classical.choose (surj q)) (Classical.choose (surj q'))).mpr h
  simpa [Classical.choose_spec (surj q), Classical.choose_spec (surj q')] using eq

theorem lift_order {A Q R : Type} (p : A → Q) (b : A → R)
    (surj : ∀ q, ∃ a, p a = q) (ltQ : Q → Q → Prop) (ltR : R → R → Prop)
    (order : ∀ a a', ltQ (p a) (p a') ↔ ltR (b a) (b a')) (q q' : Q) :
    ltQ q q' ↔ ltR (lift p b surj q) (lift p b surj q') := by
  have h := order (Classical.choose (surj q)) (Classical.choose (surj q'))
  simpa [lift, Classical.choose_spec (surj q), Classical.choose_spec (surj q')] using h

theorem factor_unique {A Q R : Type} (p : A → Q) (b : A → R)
    (surj : ∀ q, ∃ a, p a = q)
    (kernel : ∀ a a', p a = p a' ↔ b a = b a')
    (f : Q → R) (commutes : ∀ a, f (p a) = b a) : f = lift p b surj := by
  funext q
  obtain ⟨a, rfl⟩ := surj q
  exact (commutes a).trans (lift_commutes p b surj kernel a).symm

theorem universal_hypotheses_give_factor {A Q R : Type} (p : A → Q) (b : A → R)
    (surj : ∀ q, ∃ a, p a = q) (ltQ : Q → Q → Prop) (ltR : R → R → Prop)
    (kernel : ∀ a a', p a = p a' ↔ b a = b a')
    (order : ∀ a a', ltQ (p a) (p a') ↔ ltR (b a) (b a')) :
    ∃ f : Q → R,
      (∀ a, f (p a) = b a) ∧
      (∀ q q', f q = f q' → q = q') ∧
      (∀ q q', ltQ q q' ↔ ltR (f q) (f q')) ∧
      (∀ g : Q → R, (∀ a, g (p a) = b a) → g = f) := by
  exact ⟨lift p b surj, lift_commutes p b surj kernel,
    lift_injective p b surj kernel, lift_order p b surj ltQ ltR order,
    fun g hg => factor_unique p b surj kernel g hg⟩

structure StrictOrder (X : Type) where
  lt : X → X → Prop
  irrefl : ∀ x, ¬ lt x x
  trans : ∀ x y z, lt x y → lt y z → lt x z

 
 
theorem nested_quotient_order_embedding {S QA QS : Type}
    (A : S → Prop) (orderA : StrictOrder QA) (orderS : StrictOrder QS)
    (piA : {x : S // A x} → QA) (piS : S → QS)
    (surjA : ∀ q, ∃ x, piA x = q) (_surjS : ∀ q, ∃ x, piS x = q)
    (kernel : ∀ x y, piA x = piA y ↔ piS x.val = piS y.val)
    (order : ∀ x y, orderA.lt (piA x) (piA y) ↔ orderS.lt (piS x.val) (piS y.val)) :
    ∃ iota : QA → QS,
      (∀ q q', iota q = iota q' → q = q') ∧
      (∀ x, iota (piA x) = piS x.val) ∧
      (∀ q q', orderA.lt q q' ↔ orderS.lt (iota q) (iota q')) := by
  obtain ⟨f, hc, hi, ho, _hu⟩ := universal_hypotheses_give_factor
    piA (fun x => piS x.val) surjA orderA.lt orderS.lt kernel order
  exact ⟨f, hi, hc, ho⟩

#print axioms universal_hypotheses_give_factor
#print axioms nested_quotient_order_embedding
end LCTR.NestedQuotientOrderEmbedding
