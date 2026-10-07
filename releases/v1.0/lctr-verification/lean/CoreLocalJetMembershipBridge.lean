import CoreNativeDifferentialPredicates

namespace LCTR.CoreLocalJetMembershipBridge
set_option autoImplicit false
open Set LCTR.CoreLocalCharts LCTR.CoreNativeJointJets
open LCTR.CoreNativeDifferentialPredicates

theorem generated_image_member {T TI X : Type} {Val VI : Fin 2 → Type}
    (a : Atlas T TI Val VI) (i : Index TI VI) (k : ℕ)
    (relation : Set (JetSpace a i k)) (h2 : Diff2 a i k)
    (h3 : Diff3 a i k relation) (theta : NumericDomain a i)
    (F : JetSpace a i k → X) :
    F (canonicalPair a i k h2 theta) ∈ F '' relation := by
  exact ⟨canonicalPair a i k h2 theta,
    (diff3_restricts a i k relation h2).mp h3 theta, rfl⟩

#print axioms generated_image_member
end LCTR.CoreLocalJetMembershipBridge
