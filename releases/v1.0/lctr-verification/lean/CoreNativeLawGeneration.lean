import CoreNativeLawComponents

namespace LCTR.CoreNativeLawGeneration
set_option autoImplicit false
open LCTR.CoreObserverTime LCTR.CoreNativeCurves LCTR.CoreNativeLawComponents
open LCTR.LawTimeTransport LCTR.LawFamilyTransport
universe u v w
variable {C : Type u} {D : Type v} {B : Type w} {I A : Type} {Val : I → Type}

structure LawInput (c : Context C D B I Val) (A : Type) where
  nonempty : Nonempty A
  component : A → ComponentInput c
  allowed : (NativeTime c → Prop) → Prop
  faithful : ((j : A) → Reindex
    (Tuple (NativeTime c) (Values (Val := Val) (component j).inIndices)
      (Values (Val := Val) (component j).outIndices))
    (Tuple (NativeTime c) (Values (Val := Val) (component j).inIndices)
      (Values (Val := Val) (component j).outIndices))) → Prop

noncomputable def family (c : Context C D B I Val) (a : LawInput c A) :=
  nativeFamily c a.nonempty a.component a.allowed a.faithful

theorem common_generated_representability (c : Context C D B I Val) (a : LawInput c A)
    (conditions : AllConditions (family c a)) :
    (∃ t, common (family c a) t) ∧
    a.allowed (common (family c a)) ∧
    ∀ t, common (family c a) t →
      t.val ∈ Set.range (realValue c.data c.inc c.rho) ∧
      ∀ j, ∃ ht : t ∈ (a.component j).evalTimes,
        evalTuple (generated c (a.component j)) ⟨t,ht⟩ ∈ (a.component j).candidate := by
  have h := native_common_valid_contract c a.nonempty a.component a.allowed a.faithful
    conditions.2.2.2.2
  exact ⟨h.1, h.2.1, fun t valid => ⟨t.property, h.2.2 t valid⟩⟩

theorem generated_preimage_unique (c : Context C D B I Val) (t : NativeTime c) :
    ∃! q : OrderDomain c.data c.inc, realValue c.data c.inc c.rho q = t.val := by
  obtain ⟨q,hq⟩ := t.property
  refine ⟨q,hq,?_⟩
  intro r hr
  apply Subtype.ext
  exact embedding_injective c.data c.inc c.rho (hr.trans hq.symm)

theorem actual_trajectory_representative (c : Context C D B I Val) (t : NativeTime c) :
    ∃ x : Domain c.data,
      realEmbedding c.data c.inc c.rho (restrictedProjection c.data c.inc x) = t := by
  have member : t.val ∈ Set.range (fun x : Domain c.data => timeRep c.data c.inc c.rho x.val) := by
    rw [← real_domain_composition]
    exact t.property
  obtain ⟨x,hx⟩ := member
  exact ⟨x, Subtype.ext hx⟩

theorem common_evaluation_source_values (c : Context C D B I Val) (a : LawInput c A)
    (t : NativeTime c) (valid : common (family c a) t) :
    ∃ x : Domain c.data,
      realEmbedding c.data c.inc c.rho (restrictedProjection c.data c.inc x) = t ∧
      ∀ j, ∃ ht : t ∈ (a.component j).evalTimes,
        evalTuple (generated c (a.component j)) ⟨t,ht⟩ =
          ((t, fun i : (a.component j).inIndices =>
            c.observable i.val (canonicalTrajectory c.data c.single x)),
           fun i : (a.component j).outIndices =>
            c.observable i.val (canonicalTrajectory c.data c.single x)) ∧
        evalTuple (generated c (a.component j)) ⟨t,ht⟩ ∈ (a.component j).candidate := by
  obtain ⟨x,hx⟩ := actual_trajectory_representative c t
  have values : ∀ i : I, curve c i t = c.observable i (canonicalTrajectory c.data c.single x) := by
    intro i
    have fact := (observable_factorization c.data c.inc c.single c.fiber c.rho (c.observable i)).1 x
    exact (congrArg (curve c i) hx).symm.trans (fact.1.trans fact.2).symm
  refine ⟨x,hx,?_⟩
  intro j
  obtain ⟨ht,mem⟩ := valid j
  refine ⟨ht,?_,mem⟩
  rw [evaluation_tuple_components]
  simp only [values]

noncomputable def timeChange (c : Context C D B I Val) (rho : RealEmbedding c.data c.inc) :=
  CoreNativeLawTransport.reindex c.data c.inc c.rho rho
    (Set.range (realValue c.data c.inc c.rho)) (fun _ h => h)

theorem transported_law_generation (c : Context C D B I Val) (a : LawInput c A)
    (rho : RealEmbedding c.data c.inc) (conditions : AllConditions (family c a)) :
    AllConditions (transportFamily (timeChange c rho) (family c a)) ∧
    (∃ t, common (transportFamily (timeChange c rho) (family c a)) t) ∧
    ∀ t, common (transportFamily (timeChange c rho) (family c a)) t →
      t.val ∈ Set.range (realValue c.data c.inc rho) ∧
      ∀ j, ∃ ht : (transportFamily (timeChange c rho) (family c a)).component j |>.evalTime t,
        tupleRelation ((transportFamily (timeChange c rho) (family c a)).component j)
          (evalTuple ((transportFamily (timeChange c rho) (family c a)).component j) ⟨t,ht⟩) := by
  have h := (five_conditions_preserved (timeChange c rho) (family c a)).mpr conditions
  refine ⟨h,h.2.2.2.2.2.1,?_⟩
  intro t valid
  exact ⟨CoreNativeLawTransport.changed_domain_contained c.data c.inc c.rho rho
    (Set.range (realValue c.data c.inc c.rho)) t.property, valid⟩

theorem empty_trajectory_rejects_law_conditions (c : Context C D B I Val) (a : LawInput c A)
    (empty : IsEmpty (Domain c.data)) : ¬ AllConditions (family c a) := by
  intro conditions
  obtain ⟨t,_⟩ := (common_generated_representability c a conditions).1
  obtain ⟨x,_⟩ := actual_trajectory_representative c t
  exact empty.false x

end LCTR.CoreNativeLawGeneration
