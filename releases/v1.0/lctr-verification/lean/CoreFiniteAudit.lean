import CoreTokenGraph
import CoreAuditStateTransport
import Init.Data.Vector.OfFn

namespace LCTR.CoreFiniteAudit
set_option autoImplicit false
open LCTR.CoreTokenGraph LCTR.CoreEvaluation LCTR.SelectedInputEvaluation LCTR.CoreAuditStateTransport

def predecessorPass (s : Token → State) (x : Token) : Bool :=
  decide (∀ y : Token, Edge y x → s y=.sat)

def step (formed evaluated condition : Token → Bool) (s : Token → State) (x : Token) : State :=
  state (formed x) (evaluated x) (predecessorPass s x) (condition x)

theorem count_le_nine : ∀ i : Fin 6, count i ≤ 9 := by decide

abbrev Table := Vector (Vector State 9) 6

def tabulate (s : Token → State) : Table := Vector.ofFn (fun i =>
    Vector.ofFn (fun j => if h : j.val < count i then s ⟨i,⟨j.val,h⟩⟩ else .unformed))

def lookup (table : Table) (t : Token) : State :=
  table[t.1.val][t.2.val]'(lt_of_lt_of_le t.2.isLt (count_le_nine t.1))

def memoize (s : Token → State) : Token → State := lookup (tabulate s)

theorem memoize_eq (s : Token → State) : memoize s = s := by
  funext t
  simp only [memoize,lookup,tabulate,Vector.getElem_ofFn,dif_pos t.2.isLt]

def runTable (formed evaluated condition : Token → Bool) : ℕ → Table
  | 0 => tabulate (fun _ => .unformed)
  | n+1 =>
      let previous := runTable formed evaluated condition n
      tabulate (step formed evaluated condition (lookup previous))

def run (formed evaluated condition : Token → Bool) (n : ℕ) : Token → State :=
  lookup (runTable formed evaluated condition n)

theorem predecessor_iff (s : Token → State) (x : Token) :
    (∀ y : Token, Edge y x → s y=.sat) ↔ (∀ y : {y : Token // Edge y x}, s y.val=.sat) := by
  exact ⟨fun h y => h y.val y.property,fun h y hy => h ⟨y,hy⟩⟩

theorem step_eq_native (formed evaluated condition : Token → Bool) (s : Token → State) (x : Token) :
    step formed evaluated condition s x = update Edge formed evaluated condition x (fun y => s y.val) := by
  classical
  unfold step predecessorPass update
  exact congrArg (fun b => state (formed x) (evaluated x) b (condition x))
    (decide_eq_decide.mpr (predecessor_iff s x))

theorem rank_bound : ∀ t : Token, scalarRank t < 40 := by decide

theorem run_matches_solution (f e c : Token → Bool) (s : Token → State)
    (hs : Recurs Edge f e c s) (n : ℕ) :
    ∀ x, scalarRank x < n → run f e c n x = s x := by
  induction n with
  | zero => intro x hx; omega
  | succ n ih =>
    intro x hx
    have incoming : ∀ y, Edge y x → run f e c n y = s y := by
      intro y hy
      exact ih y (lt_of_lt_of_le (edge_rank_increasing hy) (Nat.lt_succ_iff.mp hx))
    have hp : (∀ y : Token, Edge y x → run f e c n y=.sat) ↔
        (∀ y : Token, Edge y x → s y=.sat) := by
      constructor
      · intro h y hy
        rw [← incoming y hy]
        exact h y hy
      · intro h y hy
        rw [incoming y hy]
        exact h y hy
    change memoize (step f e c (run f e c n)) x = s x
    rw [memoize_eq]
    rw [hs x,← step_eq_native]
    simp only [step,predecessorPass,propext hp]

theorem finite_run_solves (f e c : Token → Bool) : Recurs Edge f e c (run f e c 40) := by
  obtain ⟨s,hs,_⟩ := unique_state_recursion Edge
    (LCTR.CoreDagRecursion.finite_acyclic_wellFounded Edge acyclic) f e c
  have he : run f e c 40=s := funext (fun x => run_matches_solution f e c s hs 40 x (rank_bound x))
  rw [he]
  exact hs

theorem finite_run_unique (f e c : Token → Bool) (s : Token → State)
    (hs : Recurs Edge f e c s) : s = run f e c 40 :=
  (funext (fun x => run_matches_solution f e c s hs 40 x (rank_bound x))).symm

def auditOutput (f e c : Token → Bool) (x : Token) : AuditStatus :=
  lift (predecessorPass (run f e c 40) x) (run f e c 40 x)

theorem audit_output_eq_native (f e c : Token → Bool) (x : Token) :
    auditOutput f e c x = auditAt Edge (run f e c 40) x := by
  classical
  unfold auditOutput auditAt predecessorPass
  exact congrArg (fun b => lift b (run f e c 40 x))
    (decide_eq_decide.mpr (predecessor_iff (run f e c 40) x))

theorem finite_audit_output_unique (f e c : Token → Bool) (s : Token → State)
    (hs : Recurs Edge f e c s) : ∀ x, auditOutput f e c x = auditAt Edge s x := by
  intro x
  rw [audit_output_eq_native,← finite_run_unique f e c s hs]

end LCTR.CoreFiniteAudit
