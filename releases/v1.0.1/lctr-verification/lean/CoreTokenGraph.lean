import CoreEvaluation
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma

namespace LCTR.CoreTokenGraph
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
universe u v w

 
def count (s : Fin 6) : Nat := [8, 3, 8, 9, 5, 5][s.val]!
abbrev Token := (s : Fin 6) × Fin (count s)
def series (t : Token) : Nat := t.1.val
def index (t : Token) : Nat := t.2.val + 1

theorem token_card : Fintype.card Token = 38 := by decide
theorem series_card : ∀ s : Fin 6, Fintype.card (Fin (count s)) = count s :=
  fun _ => Fintype.card_fin _
theorem strict_approx_card :
    (Finset.univ.filter (fun t : Token => series t ≠ 3)).card = 29 ∧
    (Finset.univ.filter (fun t : Token => series t = 3)).card = 9 := by decide

theorem series_partition :
    (∀ t : Token, ∃! s : Fin 6, t.1 = s) ∧
    (∀ s : Fin 6, ∃ t : Token, t.1 = s) := by
  constructor
  · intro t
    exact ⟨t.1, rfl, fun _ h => h.symm⟩
  · decide

theorem strict_approx_partition : ∀ t : Token,
    (series t ≠ 3 ∨ series t = 3) ∧ ¬ (series t ≠ 3 ∧ series t = 3) := by decide

 
 
def conditionEquiv (P : Token → Type v) (K : (t : Token) → P t) :
    Token ≃ {p : (t : Token) × P t // p.2 = K p.1} where
  toFun t := ⟨⟨t, K t⟩, rfl⟩
  invFun p := p.val.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨t, p⟩, h⟩
    apply Subtype.ext
    change Sigma.mk t (K t) = Sigma.mk t p
    congr 1
    exact h.symm

theorem condition_classification_bijective (P : Token → Type v) (K : (t : Token) → P t) :
    Function.Bijective (conditionEquiv P K) := (conditionEquiv P K).bijective

def within (s i j : Nat) : Prop :=
  match s with
  | 0 => 1 ≤ i ∧ i < 8 ∧ j = i + 1
  | 1 => (i,j) ∈ [(1,2),(2,3)]
  | 2 => (i,j) ∈ [(1,6),(6,7),(2,3),(3,8),(6,8)]
  | 3 => (1 ≤ i ∧ i ≤ 6 ∧ j = 7) ∨ (i,j) ∈ [(7,8),(7,9)]
  | 4 => (i,j) ∈ [(1,3),(1,5),(3,5)]
  | 5 => (i,j) ∈ [(1,2),(2,3),(1,4),(1,5)]
  | _ => False
instance (s i j : Nat) : Decidable (within s i j) := by
  unfold within
  split <;> infer_instance

def between (s t : Nat) : Prop := (s,t) ∈ [(0,1),(1,2),(2,3),(2,4),(4,5)]
instance (s t : Nat) : Decidable (between s t) := inferInstanceAs (Decidable (_ ∈ _))
def Edge (a b : Token) : Prop :=
  (series a = series b ∧ within (series a) (index a) (index b)) ∨
  between (series a) (series b)
instance (a b : Token) : Decidable (Edge a b) := by unfold Edge; infer_instance

theorem edge_count : (Finset.univ.filter (fun p : Token × Token => Edge p.1 p.2)).card = 214 := by
  decide

def layer (s : Nat) : Nat := [0,1,2,3,3,4][s]!
def withinRank (t : Token) : Nat :=
  let ranks := [[0,1,2,3,4,5,6,7], [0,1,2], [0,0,1,0,0,1,2,2],
    [0,0,0,0,0,0,1,2,2], [0,0,1,0,2], [0,1,2,1,1]]
  ranks[series t]![t.2.val]!
def rank (t : Token) : Nat × Nat := (layer (series t), withinRank t)
def scalarRank (t : Token) : Nat := 8 * (rank t).1 + (rank t).2
def LexLess (a b : Nat × Nat) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)
instance (a b : Nat × Nat) : Decidable (LexLess a b) := by unfold LexLess; infer_instance

theorem source_rank_bridge : ∀ a b : Token,
    LexLess (rank a) (rank b) ↔ scalarRank a < scalarRank b := by decide
theorem edge_lex_increasing : ∀ a b : Token, Edge a b → LexLess (rank a) (rank b) := by decide
theorem edge_rank_increasing {a b : Token} (h : Edge a b) : scalarRank a < scalarRank b :=
  (source_rank_bridge a b).mp (edge_lex_increasing a b h)

 
theorem path_increases {V : Type u} {R : Type v} (E : V → V → Prop)
    (lt : R → R → Prop) [IsStrictOrder R lt] (r : V → R)
    (step : ∀ a b, E a b → lt (r a) (r b)) {a b : V}
    (p : Relation.TransGen E a b) : lt (r a) (r b) := by
  induction p with
  | single h => exact step _ _ h
  | tail _ h ih => exact _root_.trans ih (step _ _ h)

theorem rank_reachability_antisymm {V : Type u} {R : Type v} (E : V → V → Prop)
    (lt : R → R → Prop) [IsStrictOrder R lt] (r : V → R)
    (step : ∀ a b, E a b → lt (r a) (r b)) {a b : V}
    (ab : Relation.ReflTransGen E a b) (ba : Relation.ReflTransGen E b a) : a = b := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp ab with h | hp
  · exact h.symm
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp ba with h | hq
  · exact h
  exact False.elim (irrefl (r a) (_root_.trans (path_increases E lt r step hp)
    (path_increases E lt r step hq)))

theorem acyclic (a : Token) : ¬ Relation.TransGen Edge a a := by
  intro h
  have bad := path_increases Edge (· < ·) scalarRank (fun _ _ => edge_rank_increasing) h
  exact Nat.lt_irrefl _ bad

@[instance_reducible] def reachPartialOrder : PartialOrder Token where
  le := Relation.ReflTransGen Edge
  le_refl _ := .refl
  le_trans _ _ _ := Relation.ReflTransGen.trans
  le_antisymm _ _ := rank_reachability_antisymm Edge (· < ·) scalarRank
    (fun _ _ => edge_rank_increasing)

 
def allowed (s t : Fin 6) : Prop :=
  s.val = 0 ∨ (s.val = 1 ∧ t.val ≠ 0) ∨
  (s.val = 2 ∧ t.val ∈ [2,3,4,5]) ∨ (s.val = 3 ∧ t.val = 3) ∨
  (s.val = 4 ∧ t.val ∈ [4,5]) ∨ (s.val = 5 ∧ t.val = 5)
instance (s t : Fin 6) : Decidable (allowed s t) := by unfold allowed; infer_instance
theorem allowed_refl : ∀ s, allowed s s := by decide
theorem allowed_trans : ∀ a b c, allowed a b → allowed b c → allowed a c := by decide
theorem edge_allowed : ∀ a b : Token, Edge a b → allowed a.1 b.1 := by decide
theorem path_allowed {a b : Token} (h : Relation.TransGen Edge a b) : allowed a.1 b.1 := by
  induction h with
  | single h => exact edge_allowed _ _ h
  | tail _ h ih => exact allowed_trans _ _ _ ih (edge_allowed _ _ h)

def designated (a b : Token) : Prop :=
  (series a = 3 ∧ series b ∈ [4,5]) ∨
  (series a = 2 ∧ series b = 2 ∧ index a = 4 ∧ index b = 5) ∨
  (series a = 3 ∧ series b = 3 ∧
    ((index a < index b ∧ index b ≤ 6) ∨ (index a = 8 ∧ index b = 9))) ∨
  (series a = 4 ∧ series b = 4 ∧ index a < index b ∧
    index a ∈ [1,2,4] ∧ index b ∈ [1,2,4]) ∨
  (series a = 5 ∧ series b = 5 ∧ index a = 4 ∧ index b = 5)
instance (a b : Token) : Decidable (designated a b) := by unfold designated; infer_instance
theorem designated_count :
    (Finset.univ.filter (fun p : Token × Token => designated p.1 p.2)).card = 111 := by decide
theorem designated_criterion : ∀ a b : Token, designated a b →
    a ≠ b ∧ (scalarRank a = scalarRank b ∨ (¬ allowed a.1 b.1 ∧ ¬ allowed b.1 a.1)) := by decide

theorem parallel_branches {a b : Token} (h : designated a b) :
    ¬ Relation.ReflTransGen Edge a b ∧ ¬ Relation.ReflTransGen Edge b a := by
  obtain ⟨ne, criterion⟩ := designated_criterion a b h
  have no_path : ¬ Relation.TransGen Edge a b ∧ ¬ Relation.TransGen Edge b a := by
    rcases criterion with same | ⟨ab, ba⟩
    · constructor
      · intro hp
        have bad := path_increases Edge (· < ·) scalarRank (fun _ _ => edge_rank_increasing) hp
        omega
      · intro hp
        have bad := path_increases Edge (· < ·) scalarRank (fun _ _ => edge_rank_increasing) hp
        omega
    · exact ⟨fun hp => ab (path_allowed hp), fun hp => ba (path_allowed hp)⟩
  constructor
  · intro hp
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hp with he | he
    · exact ne he.symm
    · exact no_path.1 he
  · intro hp
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hp with he | he
    · exact ne he
    · exact no_path.2 he

 
theorem concrete_argument_unique (Spec : Token → Type v)
    (res : (x y : Token) → Edge y x → Spec x → Spec y)
    (f e c : ((x : Token) × Spec x) → Bool) :
    ∃! s, LCTR.CoreEvaluation.Recurs (LCTR.CoreEvaluation.argEdge Edge Spec res) f e c s :=
  LCTR.CoreEvaluation.typed_argument_unique Edge acyclic Spec res f e c

#print axioms token_card
#print axioms series_partition
#print axioms strict_approx_partition
#print axioms condition_classification_bijective
#print axioms edge_count
#print axioms source_rank_bridge
#print axioms edge_lex_increasing
#print axioms rank_reachability_antisymm
#print axioms acyclic
#print axioms reachPartialOrder
#print axioms designated_count
#print axioms parallel_branches
#print axioms concrete_argument_unique
end LCTR.CoreTokenGraph
