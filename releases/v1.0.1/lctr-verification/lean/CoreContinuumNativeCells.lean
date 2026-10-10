import CoreObserverRecordImages
import CoreRecordCells
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.FinCases

namespace LCTR.CoreContinuumNativeCells
set_option autoImplicit false
open Set LCTR.CoreObserverTime LCTR.CoreObserverRecordImages LCTR.CoreContinuumDatum
open scoped ENNReal
noncomputable section
variable {U C D B P N : Type} {V : U → Type}

structure RealMap where
  Codomain : Type
  topology : TopologicalSpace Codomain
  interval : Set ℝ
  samples : Finset interval
  sampleValue : {x : interval // x ∈ samples} → Codomain
  candidate : interval → Codomain
  deviation : Codomain → Codomain → ℝ≥0∞
  tolerance : ℝ≥0∞

def RealMap.toMap (m : RealMap) : MapDatum where
  Domain := ℝ
  Codomain := m.Codomain
  domainTopology := inferInstance
  codomainTopology := m.topology
  interval := m.interval
  samples := m.samples
  sampleValue := m.sampleValue
  candidate := m.candidate
  deviation := m.deviation
  tolerance := m.tolerance

def maps (cmp obs : RealMap) (other : Fin 3 → MapDatum) : Fin 5 → MapDatum :=
  ![other 0,cmp.toMap,obs.toMap,other 1,other 2]

structure NativeSource (U C D B P N : Type) (V : U → Type) where
  comparison : LCTR.CoreExactStructure.Input U D V
  representation : LCTR.CoreRecordCells.Representation comparison ℝ
  dynamics : Input C D B
  incomparableTransitive : IncTrans dynamics
  realEmbedding : RealEmbedding dynamics incomparableTransitive
  code : WindowCode D P N

def comparisonImage (s : NativeSource U C D B P N V) (x : U × D) : Set ℝ :=
  LCTR.CoreRecordCells.cellImage s.comparison s.representation s.code.window x.1 x.2
def observerImage (s : NativeSource U C D B P N V) (r : D) : Set ℝ :=
  realImage s.dynamics s.incomparableTransitive s.realEmbedding s.code (s.code.window r)

def mapped (m : RealMap) (S : Set ℝ) : Set m.Codomain :=
  m.candidate '' {x : m.interval | x.val ∈ S}

def cells (s : NativeSource U C D B P N V) (cmp obs : RealMap)
    (other : Fin 3 → MapDatum) : CellDatum (maps cmp obs other) where
  Index := ![U × D,D]
  cell := Fin.cases (fun x => {z | z.val ∈ comparisonImage s x})
    (Fin.cases (fun x => {z | z.val ∈ observerImage s x}) (fun i => Fin.elim0 i))

def Contained (s : NativeSource U C D B P N V) (cmp obs : RealMap) : Prop :=
  (∀ x, comparisonImage s x ⊆ cmp.interval) ∧ (∀ r, observerImage s r ⊆ obs.interval)

theorem mapped_full_image (m : RealMap) (S : Set ℝ) (inside : S ⊆ m.interval) :
    mapped m S = (fun x : S => m.candidate ⟨x.val,inside x.property⟩) '' Set.univ := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨x.val,hx⟩,Set.mem_univ _,rfl⟩
  · rintro ⟨x,_,rfl⟩
    exact ⟨⟨x.val,inside x.property⟩,x.property,rfl⟩

theorem comparison_cell_exact (s : NativeSource U C D B P N V)
    (cmp obs : RealMap) (other : Fin 3 → MapDatum) (x : U × D) :
    cellImage (maps cmp obs other) (cells s cmp obs other) 0 x =
      mapped cmp (comparisonImage s x) := rfl

theorem observer_cell_exact (s : NativeSource U C D B P N V)
    (cmp obs : RealMap) (other : Fin 3 → MapDatum) (r : D) :
    cellImage (maps cmp obs other) (cells s cmp obs other) 1 r =
      mapped obs (observerImage s r) := rfl

theorem comparison_native_witness (s : NativeSource U C D B P N V)
    (cmp : RealMap) (x : U × D) (y : cmp.Codomain) :
    y ∈ mapped cmp (comparisonImage s x) ↔ ∃ z : cmp.interval,
      (∃ r : (s.comparison.arrival x.1).dom, r.val ∈ s.code.window x.2 ∧
        LCTR.CoreRecordCells.recordValue s.comparison s.representation x.1 r = z.val) ∧
      cmp.candidate z = y := Iff.rfl

theorem observer_native_witness (s : NativeSource U C D B P N V)
    (obs : RealMap) (r : D) (y : obs.Codomain) :
    y ∈ mapped obs (observerImage s r) ↔ ∃ z : obs.interval,
      (∃ w ∈ s.code.window r, ∃ x : LCTR.CoreContinuumNativeRecords.Raw s.dynamics,
        s.code.value x.val.2.1 = s.code.value w ∧
        timeRep s.dynamics s.incomparableTransitive s.realEmbedding
          (timeProjection s.dynamics x.val.1) = z.val) ∧ obs.candidate z = y := by
  unfold mapped observerImage
  apply exists_congr
  intro z
  exact and_congr_left (fun _ => real_image_membership _ _ _ _ _ _)

theorem both_families_width_bound (s : NativeSource U C D B P N V)
    (cmp obs : RealMap) (other : Fin 3 → MapDatum) (eps : ℝ≥0∞) :
    cellWidth (maps cmp obs other) (cells s cmp obs other) ≤ eps ↔
      (∀ x, diameter cmp.deviation (mapped cmp (comparisonImage s x)) ≤ eps) ∧
      (∀ r, diameter obs.deviation (mapped obs (observerImage s r)) ≤ eps) := by
  simp only [cellWidth,iSup_le_iff]
  constructor
  · intro h
    exact ⟨h 0,h 1⟩
  · rintro ⟨hc,ho⟩ i
    fin_cases i
    · exact hc
    · exact ho

theorem both_families_width_excess (s : NativeSource U C D B P N V)
    (cmp obs : RealMap) (other : Fin 3 → MapDatum) (eps : ℝ≥0∞) :
    eps < cellWidth (maps cmp obs other) (cells s cmp obs other) ↔
      (∃ x, ∃ a ∈ mapped cmp (comparisonImage s x),
        ∃ b ∈ mapped cmp (comparisonImage s x), eps < cmp.deviation a b) ∨
      (∃ r, ∃ a ∈ mapped obs (observerImage s r),
        ∃ b ∈ mapped obs (observerImage s r), eps < obs.deviation a b) := by
  classical
  rw [← not_le,both_families_width_bound]
  simp only [not_and_or,not_forall,not_le,diameter_excess]

theorem native_width_source_supremum (s : NativeSource U C D B P N V)
    (cmp obs : RealMap) (other : Fin 3 → MapDatum) :
    cellWidth (maps cmp obs other) (cells s cmp obs other) =
      sSup ({0} ∪ {v | ∃ x, v = diameter cmp.deviation (mapped cmp (comparisonImage s x))} ∪
        {v | ∃ r, v = diameter obs.deviation (mapped obs (observerImage s r))}) := by
  apply le_antisymm
  · apply (both_families_width_bound s cmp obs other _).mpr
    exact ⟨fun x => le_sSup (Or.inl (Or.inr ⟨x,rfl⟩)),
      fun r => le_sSup (Or.inr ⟨r,rfl⟩)⟩
  · apply sSup_le
    intro v hv
    have bounds := (both_families_width_bound s cmp obs other _).mp le_rfl
    rcases hv with (hz | ⟨x,rfl⟩) | ⟨r,rfl⟩
    · exact hz ▸ bot_le
    · exact bounds.1 x
    · exact bounds.2 r

theorem full_cell_images_preserved (s : NativeSource U C D B P N V)
    (cmp obs : RealMap) (other : Fin 3 → MapDatum) (inside : Contained s cmp obs) :
    (∀ x, cellImage (maps cmp obs other) (cells s cmp obs other) 0 x =
      (fun z : comparisonImage s x => cmp.candidate ⟨z.val,inside.1 x z.property⟩) '' Set.univ) ∧
    (∀ r, cellImage (maps cmp obs other) (cells s cmp obs other) 1 r =
      (fun z : observerImage s r => obs.candidate ⟨z.val,inside.2 r z.property⟩) '' Set.univ) :=
  ⟨fun x => mapped_full_image cmp _ (inside.1 x),fun r => mapped_full_image obs _ (inside.2 r)⟩

end
end LCTR.CoreContinuumNativeCells
