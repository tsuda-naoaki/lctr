import CoreDynamicsBundle

namespace LCTR.CoreDynamicMaster
set_option autoImplicit false
open LCTR.CoreObserverTime LCTR.CoreNativeCurves LCTR.CoreRecordCodes
open LCTR.CoreNativeObservables LCTR.CoreLawInputBundle LCTR.CoreDynamicsBundle
universe u v w
variable {C : Type u} {D : Type v} {B : Type w}
variable {U L J V W P N : Type} {Arr : U → Type}

theorem dynamic_master (d : Input C D B) (inc : IncTrans d) (single : Single d)
    (fiber : FiberCondition d inc single) (embeddings : Nonempty (RealEmbedding d inc))
    (a : LocalDatum B U L J V Arr) (h : Descent d a) (code : Code D W P N) :
    Nonempty (RealEmbedding d inc) ∧ ∀ rho : RealEmbedding d inc,
      (∃! x : Description d inc rho J V W P N, DescriptionSpec d inc single rho a h code x) ∧
      (∃! x : LawInput d J V W P N × Description d inc rho J V W P N,
        WitnessSpec d inc single rho a h code x) :=
  ⟨embeddings,fun rho => ⟨description_exists_unique d inc single fiber rho a h code,
    witness_exists_unique d inc single fiber rho a h code⟩⟩

theorem same_pre_real_input (d : Input C D B) (inc : IncTrans d) (single : Single d)
    (fiber : FiberCondition d inc single) (rho sigma : RealEmbedding d inc)
    (a : LocalDatum B U L J V Arr) (h : Descent d a) (code : Code D W P N) :
    (description d inc single fiber rho a h code).law =
      (description d inc single fiber sigma a h code).law := rfl

end LCTR.CoreDynamicMaster
