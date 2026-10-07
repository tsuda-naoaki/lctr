import CoreOperationalConfiguration

namespace LCTR.CoreReceptionInput
set_option autoImplicit false
open Set LCTR.Chapter02 LCTR.CoreCarrierPatterns LCTR.CoreOperationalConfiguration
universe u

def sourceToBase : SourceRole → Role
  | .clock => .clock | .detector => .detector | .body => .body
def comparisonRoles : Set SourceRole := {.clock,.detector}

theorem source_role_exact (b : Role) : b ∈ Set.range sourceToBase ↔ b ≠ .observer := by
  constructor
  · rintro ⟨r,rfl⟩; cases r <;> decide
  · intro h
    cases b with
    | clock => exact ⟨.clock,rfl⟩
    | detector => exact ⟨.detector,rfl⟩
    | body => exact ⟨.body,rfl⟩
    | observer => exact False.elim (h rfl)

theorem source_role_injective : Function.Injective sourceToBase := by
  intro a b h
  cases a <;> cases b <;> simp_all [sourceToBase]

theorem comparison_role_exact (r : SourceRole) :
    r ∈ comparisonRoles ↔ r = .clock ∨ r = .detector := by
  simp [comparisonRoles]

variable {a : Input} {p : Physical a} (rcv : Reception.{u} a p)

def restrictedOrder (v : rcv.Node) (r : SourceRole) : OrderData (rcv.receive v r) where
  le x y := (rcv.order v).le ⟨r,x⟩ ⟨r,y⟩
  reflexive x := (rcv.order v).reflexive ⟨r,x⟩
  transitive x y z := (rcv.order v).transitive ⟨r,x⟩ ⟨r,y⟩ ⟨r,z⟩
  antisymmetric x y hxy hyx := by
    have h := (rcv.order v).antisymmetric ⟨r,x⟩ ⟨r,y⟩ hxy hyx
    simpa using h

theorem restriction_exact (v : rcv.Node) (r : SourceRole) (x y : rcv.receive v r) :
    (restrictedOrder rcv v r).le x y ↔ (rcv.order v).le ⟨r,x⟩ ⟨r,y⟩ := Iff.rfl

theorem restriction_partial_order (v : rcv.Node) (r : SourceRole) :
    (∀ x, (restrictedOrder rcv v r).le x x) ∧
    (∀ x y z, (restrictedOrder rcv v r).le x y → (restrictedOrder rcv v r).le y z → (restrictedOrder rcv v r).le x z) ∧
    (∀ x y, (restrictedOrder rcv v r).le x y → (restrictedOrder rcv v r).le y x → x=y) :=
  ⟨(restrictedOrder rcv v r).reflexive,(restrictedOrder rcv v r).transitive,(restrictedOrder rcv v r).antisymmetric⟩

abbrev TotalReception (r : SourceRole) := (v : rcv.Node) × rcv.receive v r

theorem total_reception_decomposition (r : SourceRole) (z : TotalReception rcv r) :
    (⟨z.1,z.2⟩ : TotalReception rcv r) = z := rfl

theorem total_reception_distinct_nodes (r : SourceRole) (x y : TotalReception rcv r)
    (h : x.1 ≠ y.1) : x ≠ y := fun e => h (congrArg Sigma.fst e)

end LCTR.CoreReceptionInput
