import CoreRefinementForest
import CoreFinitePartitions

namespace LCTR.CoreRepresentationFailure
set_option autoImplicit false
open Set LCTR.CoreTokenGraph LCTR.CoreEvaluation LCTR.CoreFiniteAudit LCTR.SelectedInputEvaluation
open LCTR.CoreComparisonFailure (cmpToken)

def reprToken (i : Fin 3) : Token := ⟨1,i⟩

theorem representation_incoming_exact : ∀ i : Fin 3, ∀ t : Token,
    Edge t (reprToken i) ↔
      (∃ j : Fin 8, t = cmpToken j) ∨
      (∃ j : Fin 3, t = reprToken j ∧ j.val + 1 = i.val) := by decide

def Prefix (c : Token → Bool) (i : Fin 3) : Prop :=
  ∀ j : Fin 3, j < i → c (reprToken j) = true
def First (c : Token → Bool) (i : Fin 3) : Prop :=
  Prefix c i ∧ c (reprToken i) = false
def Generated (c : Token → Bool) (n : Nat) : Prop :=
  ∀ j : Fin 3, j.val < n → c (reprToken j) = true

theorem incoming_prefix (c : Token → Bool) (s : Token → State) (i : Fin 3)
    (external : ∀ j : Fin 8, s (cmpToken j) = .sat)
    (prior : ∀ j : Fin 3, j < i →
      (s (reprToken j) = .sat ↔ ∀ k : Fin 3, k ≤ j → c (reprToken k) = true)) :
    (∀ y : {y : Token // Edge y (reprToken i)}, s y.val = .sat) ↔ Prefix c i := by
  constructor
  · intro hs j hji
    let p : Fin 3 := ⟨i.val-1,by omega⟩
    have pi : p < i := by change i.val-1 < i.val; omega
    have ep : Edge (reprToken p) (reprToken i) :=
      (representation_incoming_exact i _).mpr (Or.inr ⟨p,rfl,by dsimp [p]; omega⟩)
    exact ((prior p pi).mp (hs ⟨reprToken p,ep⟩)) j (by change j.val ≤ i.val-1; omega)
  · rintro hp ⟨t,ht⟩
    rcases (representation_incoming_exact i t).mp ht with hc | hr
    · obtain ⟨j,rfl⟩ := hc
      exact external j
    · obtain ⟨j,rfl,hj⟩ := hr
      apply (prior j (by omega)).mpr
      intro k hk
      exact hp k (by omega)

theorem representation_sat_prefix (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s)
    (external : ∀ j : Fin 8, s (cmpToken j) = .sat)
    (ready : ∀ i : Fin 3, f (reprToken i) = true ∧ e (reprToken i) = true) (i : Fin 3) :
    s (reprToken i) = .sat ↔ ∀ j : Fin 3, j ≤ i → c (reprToken j) = true := by
  classical
  induction i using Fin.strong_induction_on with
  | h i ih =>
    have prior := incoming_prefix c s i external ih
    rw [rec (reprToken i)]
    simp only [update,state_sat_iff,(ready i).1,(ready i).2,true_and,decide_eq_true_eq,prior]
    constructor
    · rintro ⟨hp,hc⟩ j hj
      rcases lt_or_eq_of_le hj with lt | rfl
      · exact hp j lt
      · exact hc
    · intro h
      exact ⟨fun j hj => h j hj.le,h i le_rfl⟩

theorem representation_failed_prefix (f e c : Token → Bool) (s : Token → State)
    (rec : Recurs Edge f e c s)
    (external : ∀ j : Fin 8, s (cmpToken j) = .sat)
    (ready : ∀ i : Fin 3, f (reprToken i) = true ∧ e (reprToken i) = true) (i : Fin 3) :
    s (reprToken i) = .failed ↔ First c i := by
  have prior := incoming_prefix c s i external
    (fun j _ => representation_sat_prefix f e c s rec external ready j)
  rw [rec (reprToken i),update_failed_iff]
  simp only [(ready i).1,(ready i).2,true_and,prior,First]

theorem generation_boundary (c : Token → Bool) (i : Fin 3) :
    First c i ↔ Generated c i.val ∧ ¬ Generated c (i.val+1) := by
  constructor
  · rintro ⟨hp,hc⟩
    refine ⟨hp,?_⟩
    intro hg
    have bad := (hg i (by omega)).symm.trans hc
    cases bad
  · rintro ⟨hp,hn⟩
    refine ⟨hp,Bool.eq_false_iff.mpr ?_⟩
    intro hc
    apply hn
    intro j hj
    rcases lt_or_eq_of_le (show j ≤ i by omega) with lt | rfl
    · exact hp j lt
    · exact hc

theorem first_index_unique (c : Token → Bool) {i j : Fin 3}
    (hi : First c i) (hj : First c j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have bad := (hj.1 i h).symm.trans hi.2; cases bad
  · exact h
  · have bad := (hi.1 j h).symm.trans hj.2; cases bad

theorem first_failure_partition (c : Token → Bool) :
    (¬ ∀ i : Fin 3, c (reprToken i) = true) ↔ ∃! i : Fin 3, First c i := by
  constructor
  · intro hf
    let K : Nat → Prop := fun n => ∀ j : Fin 3, j.val+1 = n → c (reprToken j) = true
    have fails : ¬ ∀ n, 1 ≤ n → n ≤ 3 → K n := by
      intro all
      exact hf (fun j => all (j.val+1) (by omega) (by omega) j rfl)
    obtain ⟨n,hn,_⟩ := LCTR.CoreFinitePartitions.first_failure_unique 3 K fails
    let i : Fin 3 := ⟨n-1,by have := hn.1; have := hn.2.1; omega⟩
    have iv : i.val+1 = n := by dsimp [i]; have := hn.1; omega
    have first : First c i := by
      constructor
      · intro j hj
        exact hn.2.2.2 (j.val+1) (by omega) (by omega) j rfl
      · apply Bool.eq_false_iff.mpr
        intro hc
        apply hn.2.2.1
        intro j hj
        have ji : j = i := Fin.ext (by omega)
        simpa only [ji] using hc
    exact ⟨i,first,fun j hj => first_index_unique c hj first⟩
  · rintro ⟨i,hi,_⟩ all
    have bad := (all i).symm.trans hi.2
    cases bad

theorem comparison_success (f e c : Token → Bool)
    (ready : ∀ j : Fin 8, f (cmpToken j) = true ∧ e (cmpToken j) = true)
    (pass : ∀ j : Fin 8, c (cmpToken j) = true) :
    ∀ j : Fin 8, run f e c 40 (cmpToken j) = .sat := by
  intro j
  exact (LCTR.CoreComparisonFailure.comparison_sat_prefix f e c _
    (finite_run_solves f e c) ready j).mpr (fun k _ => pass k)

structure Config (E : Type) where
  op : E → Prop
  formed : E → Token → Bool
  evaluated : E → Token → Bool
  condition : E → Token → Bool
  comparison_ready : ∀ x, op x → ∀ j : Fin 8,
    formed x (cmpToken j) = true ∧ evaluated x (cmpToken j) = true
  comparison_pass : ∀ x, op x → ∀ j : Fin 8, condition x (cmpToken j) = true
  representation_ready : ∀ x, op x → ∀ i : Fin 3,
    formed x (reprToken i) = true ∧ evaluated x (reprToken i) = true
  outside_unformed : ∀ x, ¬ op x → ∀ i : Fin 3, formed x (reprToken i) = false

variable {E : Type}
noncomputable def states (a : Config E) (x : E) : Token → State :=
  run (a.formed x) (a.evaluated x) (a.condition x) 40
def region (a : Config E) (i : Fin 3) : Set E :=
  {x | a.op x ∧ states a x (reprToken i) = .failed}
def failureDomain (a : Config E) : Set E :=
  {x | a.op x ∧ ¬ ∀ i : Fin 3, a.condition x (reprToken i) = true}

theorem native_failed_prefix (a : Config E) (x : E) (hop : a.op x) (i : Fin 3) :
    states a x (reprToken i) = .failed ↔ First (a.condition x) i :=
  representation_failed_prefix _ _ _ _ (finite_run_solves _ _ _)
    (comparison_success _ _ _ (a.comparison_ready x hop) (a.comparison_pass x hop))
    (a.representation_ready x hop) i

theorem native_generation_boundary (a : Config E) (x : E) (hop : a.op x) (i : Fin 3) :
    x ∈ region a i ↔ Generated (a.condition x) i.val ∧
      ¬ Generated (a.condition x) (i.val+1) := by
  simp only [region,Set.mem_ofPred_eq,hop,true_and,native_failed_prefix a x hop i,
    generation_boundary]

theorem native_localization (a : Config E) (x : E) :
    x ∈ failureDomain a ↔ ∃! i : Fin 3, x ∈ region a i := by
  constructor
  · rintro ⟨hop,hf⟩
    obtain ⟨i,hi,hu⟩ := (first_failure_partition (a.condition x)).mp hf
    refine ⟨i,⟨hop,(native_failed_prefix a x hop i).mpr hi⟩,?_⟩
    rintro j ⟨_,hj⟩
    exact hu j ((native_failed_prefix a x hop j).mp hj)
  · rintro ⟨i,⟨hop,hi⟩,_⟩
    refine ⟨hop,?_⟩
    intro all
    have ff := (native_failed_prefix a x hop i).mp hi
    have bad := (all i).symm.trans ff.2
    cases bad

theorem native_region_union (a : Config E) : failureDomain a = ⋃ i : Fin 3, region a i := by
  ext x
  constructor
  · intro h
    exact Set.mem_iUnion.mpr ((native_localization a x).mp h).exists
  · intro h
    obtain ⟨i,hop,hi⟩ := Set.mem_iUnion.mp h
    refine ⟨hop,?_⟩
    intro all
    have ff := (native_failed_prefix a x hop i).mp hi
    have bad := (all i).symm.trans ff.2
    cases bad

theorem native_regions_disjoint (a : Config E) (i j : Fin 3) (ne : i ≠ j) :
    Disjoint (region a i) (region a j) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨hop,hi⟩ ⟨_,hj⟩
  exact ne (first_index_unique (a.condition x)
    ((native_failed_prefix a x hop i).mp hi) ((native_failed_prefix a x hop j).mp hj))

theorem outside_has_no_failed_representation (a : Config E) (x : E) (hop : ¬ a.op x)
    (i : Fin 3) : states a x (reprToken i) ≠ .failed := by
  intro hf
  rw [states,finite_run_solves _ _ _ (reprToken i),update_failed_iff] at hf
  rw [a.outside_unformed x hop i] at hf
  cases hf.1

theorem token_region_correspondence (a : Config E) (x : E) (i : Fin 3) :
    states a x (reprToken i) = .failed ↔ x ∈ region a i := by
  constructor
  · intro hf
    have hop : a.op x := by
      by_contra hn
      exact outside_has_no_failed_representation a x hn i hf
    exact ⟨hop,hf⟩
  · exact fun h => h.2

theorem domain_separation (a : Config E) :
    Disjoint {x | ¬ a.op x} (failureDomain a) ∧ failureDomain a ⊆ {x | a.op x} := by
  exact ⟨Set.disjoint_left.mpr (fun _ hn hf => hn hf.1),fun _ h => h.1⟩

noncomputable def signature (a : Config E) (x : E) (i : Fin 3) : Nat := by
  classical
  exact if x ∈ region a i then 1 else 0
def basis (i j : Fin 3) : Nat := if j = i then 1 else 0

theorem signature_token_correspondence (a : Config E) (x : E) (i : Fin 3) :
    (signature a x i = 1 ↔ x ∈ region a i) ∧
    (x ∈ region a i ↔ states a x (reprToken i) = .failed) := by
  classical
  exact ⟨by simp [signature],(token_region_correspondence a x i).symm⟩

theorem signature_at_failure (a : Config E) (x : E) (i : Fin 3) (hi : x ∈ region a i) :
    signature a x = basis i := by
  classical
  funext j
  have iff : x ∈ region a j ↔ j = i := by
    constructor
    · intro hj
      exact first_index_unique (a.condition x)
        ((native_failed_prefix a x hi.1 j).mp hj.2)
        ((native_failed_prefix a x hi.1 i).mp hi.2)
    · rintro rfl; exact hi
  simp only [signature,basis,iff]

theorem signature_one_hot (a : Config E) (x : E) (hf : x ∈ failureDomain a) :
    (∃! i : Fin 3, signature a x = basis i) ∧ (∑ i : Fin 3, signature a x i) = 1 := by
  obtain ⟨i,hi,_⟩ := (native_localization a x).mp hf
  have sig := signature_at_failure a x i hi
  constructor
  · refine ⟨i,sig,?_⟩
    intro j hj
    have hji : basis j i = 1 := by rw [← hj,sig]; simp [basis]
    have : i = j := by simpa [basis] using hji
    exact this.symm
  · rw [sig,Finset.sum_eq_single i]
    · simp [basis]
    · intro j _ hji; simp [basis,hji]
    · intro h; exact False.elim (h (Finset.mem_univ i))

theorem comparison_failure_blocks_representation (f e c : Token → Bool)
    (j : Fin 8) (i : Fin 3) (hj : run f e c 40 (cmpToken j) = .failed) :
    run f e c 40 (reprToken i) = .unformed := by
  apply direct_nonsat_unformed Edge f e c _ (finite_run_solves f e c)
    ((representation_incoming_exact i _).mpr (Or.inl ⟨j,rfl⟩))
  rw [hj]
  decide

theorem all_conditions_pass_no_failure (a : Config E) (x : E)
    (hp : ∀ i : Fin 3, a.condition x (reprToken i) = true) :
    ∀ i : Fin 3, signature a x i = 0 := by
  classical
  intro i
  have hn : x ∉ region a i := by
    rintro ⟨hop,hi⟩
    have ff := (native_failed_prefix a x hop i).mp hi
    have bad := (hp i).symm.trans ff.2
    cases bad
  simp [signature,hn]

open LCTR.CoreRefinementForest

def representationRegions {J : Fin 3 → Type} {K : (i : Fin 3) → J i → Type}
    (a : Config E) (first : (i : Fin 3) → J i → Set E)
    (second : (i : Fin 3) → (j : J i) → K i j → Set E)
    (first_sub : ∀ i j, first i j ⊆ region a i)
    (second_sub : ∀ i j k, second i j k ⊆ first i j) : Regions E (Fin 3) J K :=
  ⟨region a,first,second,first_sub,second_sub⟩

theorem native_refinement_coverage {J : Fin 3 → Type} {K : (i : Fin 3) → J i → Type}
    (a : Config E) (first : (i : Fin 3) → J i → Set E)
    (second : (i : Fin 3) → (j : J i) → K i j → Set E)
    (first_sub : ∀ i j, first i j ⊆ region a i)
    (second_sub : ∀ i j k, second i j k ⊆ first i j) :
    let F := asForest (representationRegions a first second first_sub second_sub)
    (∀ n, F.region n = covered F n ∪ unrefined F n ∧ Disjoint (covered F n) (unrefined F n)) ∧
    (∀ n m, Relation.ReflTransGen (ChildEdge F) n m → F.region m ⊆ F.region n) := by
  exact ⟨fun n => node_decomposition _ n,fun _ _ h => ancestor_inclusion _ h⟩

theorem native_refinement_monotonicity {J K : Type} (a : Config E) (i : Fin 3)
    (r : J → Set E) (s : K → Set E) (embed : J → K)
    (same : ∀ j, r j = s (embed j)) :
    (⋃ j, r j) ⊆ (⋃ k, s k) ∧ region a i \ (⋃ k, s k) ⊆ region a i \ (⋃ j, r j) :=
  snapshot_monotonicity (region a i) r s embed same

theorem native_conditional_child_partition {J : Fin 3 → Type} {K : (i : Fin 3) → J i → Type}
    (a : Config E) (first : (i : Fin 3) → J i → Set E)
    (second : (i : Fin 3) → (j : J i) → K i j → Set E)
    (first_sub : ∀ i j, first i j ⊆ region a i)
    (second_sub : ∀ i j k, second i j k ⊆ first i j)
    (n : Node (Fin 3) J K)
    (pairwise : ∀ i j : children n, i ≠ j →
      Disjoint ((asForest (representationRegions a first second first_sub second_sub)).region (descend n i))
        ((asForest (representationRegions a first second first_sub second_sub)).region (descend n j))) :
    let F := asForest (representationRegions a first second first_sub second_sub)
    (∀ i j : F.Child n, i ≠ j → Disjoint (F.region (F.descend n i)) (F.region (F.descend n j))) ∧
    (∀ i : F.Child n, Disjoint (F.region (F.descend n i)) (unrefined F n)) :=
  child_family_with_remainder _ n pairwise

end LCTR.CoreRepresentationFailure
