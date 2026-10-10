import CoreLocalCharts
import CoreNativeLawGeneration

namespace LCTR.CoreLawComponentCharts
set_option autoImplicit false
open LCTR.CoreLocalCharts LCTR.CoreNativeLawComponents
open LCTR.LawTimeTransport LCTR.LawFamilyTransport
variable {C D B I TI : Type} {Val : I → Type} {VI : Fin 2 → Type}
variable (c : Context C D B I Val) (l : ComponentInput c)
abbrev EvalTime := {t : NativeTime c // t ∈ l.evalTimes}
abbrev SideValue : Fin 2 → Type :=
  Fin.cases (Values (Val := Val) l.inIndices) (fun _ => Values (Val := Val) l.outIndices)
noncomputable def nativeValues : (s : Fin 2) → EvalTime c l → SideValue c l s :=
  Fin.cases (generated c l).input (fun _ => (generated c l).output)

abbrev NativeAtlas (TI : Type) (VI : Fin 2 → Type) :=
  {a : Atlas (EvalTime c l) TI (SideValue c l) VI // a.value = nativeValues c l}

variable (a : NativeAtlas c l TI VI)

theorem same_law_values (s : Fin 2) (t : EvalTime c l) :
    a.val.value s t = nativeValues c l s t := congrFun (congrFun a.property s) t

theorem native_coordinate_bijective (i : Index TI VI) :
    Function.Bijective (timeCoord a.val i) := time_coordinate_bijective a.val i

theorem native_side_curve (i : Index TI VI) (x : JointDomain a.val i) (s : Fin 2) :
    ∃ hs : nativeValues c l s x.val ∈ (a.val.valChart s (i.2 s)).source,
      curve a.val i (timeCoord a.val i x) s =
        (a.val.valChart s (i.2 s)).coordinates ⟨nativeValues c l s x.val,hs⟩ := by
  have h := same_law_values c l a s x.val
  have hs : nativeValues c l s x.val ∈ (a.val.valChart s (i.2 s)).source := h ▸ x.property.2 s
  refine ⟨hs,?_⟩
  rw [side_curve_generated]
  apply congrArg (a.val.valChart s (i.2 s)).coordinates
  exact Subtype.ext h

theorem native_input_curve (i : Index TI VI) (x : JointDomain a.val i) :
    ∃ hs : (generated c l).input x.val ∈ (a.val.valChart 0 (i.2 0)).source,
      curve a.val i (timeCoord a.val i x) 0 =
        (a.val.valChart 0 (i.2 0)).coordinates ⟨(generated c l).input x.val,hs⟩ :=
  native_side_curve c l a i x 0

theorem native_output_curve (i : Index TI VI) (x : JointDomain a.val i) :
    ∃ hs : (generated c l).output x.val ∈ (a.val.valChart 1 (i.2 1)).source,
      curve a.val i (timeCoord a.val i x) 1 =
        (a.val.valChart 1 (i.2 1)).coordinates ⟨(generated c l).output x.val,hs⟩ :=
  native_side_curve c l a i x 1

theorem every_law_evaluation_covered (t : EvalTime c l) :
    ∃ i : Index TI VI, ∃ x : JointDomain a.val i, x.val = t ∧
      ∀ s, ∃ hs : nativeValues c l s x.val ∈ (a.val.valChart s (i.2 s)).source,
        curve a.val i (timeCoord a.val i x) s =
          (a.val.valChart s (i.2 s)).coordinates ⟨nativeValues c l s x.val,hs⟩ := by
  obtain ⟨i,x,hx⟩ := joint_domain_coverage a.val t
  exact ⟨i,x,hx,native_side_curve c l a i x⟩

end LCTR.CoreLawComponentCharts
