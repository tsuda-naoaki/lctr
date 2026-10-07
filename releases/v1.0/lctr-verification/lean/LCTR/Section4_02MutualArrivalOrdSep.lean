import Init

namespace LCTR.Section402MutualArrivalOrdSep

universe u v

def Pullback
    {Arrival : Type u} {Source : Type v}
    (recover : Arrival → Source)
    (sourceLE : Source → Source → Prop) :
    Arrival → Arrival → Prop :=
  fun left right => sourceLE (recover left) (recover right)

def OrdSep
    {Arrival : Type u}
    (comparisonEquiv arrivalLE : Arrival → Arrival → Prop) : Prop :=
  ∀ left right,
    arrivalLE left right →
    arrivalLE right left →
    comparisonEquiv left right

theorem ordSep_of_recovery_antisymmetry
    {Arrival : Type u} {Source : Type v}
    (recover : Arrival → Source)
    (sourceLE : Source → Source → Prop)
    (comparisonEquiv : Arrival → Arrival → Prop)
    (hAntisymmetric :
      ∀ {left right},
        sourceLE left right → sourceLE right left → left = right)
    (hEqualRecoveryImpliesComparison :
      ∀ {left right},
        recover left = recover right → comparisonEquiv left right) :
    OrdSep comparisonEquiv (Pullback recover sourceLE) := by
  intro left right hLeftRight hRightLeft
  apply hEqualRecoveryImpliesComparison
  exact hAntisymmetric hLeftRight hRightLeft

#print axioms ordSep_of_recovery_antisymmetry

end LCTR.Section402MutualArrivalOrdSep
