import Std




namespace LCTR.DifferentialNativeDomains

structure Input (Ω : Type) where
  atlas : Ω → Prop
  jet : Ω → Prop
  member : (ρ : Ω) → jet ρ → Prop
  value : (ρ : Ω) → atlas ρ → Prop
  time : (ρ σ : Ω) → atlas ρ → atlas σ → Prop

def c1 {Ω} (d : Input Ω) : Prop := ∀ ρ, d.atlas ρ
def c2 {Ω} (d : Input Ω) : Prop := ∀ ρ, d.jet ρ
def c3 {Ω} (d : Input Ω) : Prop := ∀ ρ, ∃ h : d.jet ρ, d.member ρ h
def c4 {Ω} (d : Input Ω) : Prop := ∀ ρ, ∃ h : d.atlas ρ, d.value ρ h
def c5 {Ω} (d : Input Ω) : Prop :=
  ∀ ρ σ, ∃ h : d.atlas ρ, ∃ k : d.atlas σ, d.time ρ σ h k

theorem third_requires_second {Ω} (d : Input Ω) : c3 d → c2 d := by
  intro h ρ
  exact (h ρ).choose

theorem fourth_requires_first {Ω} (d : Input Ω) : c4 d → c1 d := by
  intro h ρ
  exact (h ρ).choose

theorem fifth_requires_first {Ω} (d : Input Ω) : c5 d → c1 d := by
  intro h ρ
  exact (h ρ ρ).choose

theorem third_restricts {Ω} (d : Input Ω) (h : c2 d) :
    c3 d ↔ ∀ ρ, d.member ρ (h ρ) := by
  constructor
  · intro hc ρ
    obtain ⟨_, hm⟩ := hc ρ
    exact hm
  · intro hm ρ
    exact ⟨h ρ, hm ρ⟩

theorem fourth_restricts {Ω} (d : Input Ω) (h : c1 d) :
    c4 d ↔ ∀ ρ, d.value ρ (h ρ) := by
  constructor
  · intro hc ρ
    obtain ⟨_, hv⟩ := hc ρ
    exact hv
  · intro hv ρ
    exact ⟨h ρ, hv ρ⟩

theorem fifth_restricts {Ω} (d : Input Ω) (h : c1 d) :
    c5 d ↔ ∀ ρ σ, d.time ρ σ (h ρ) (h σ) := by
  constructor
  · intro hc ρ σ
    obtain ⟨_, _, ht⟩ := hc ρ σ
    exact ht
  · intro ht ρ σ
    exact ⟨h ρ, h σ, ht ρ σ⟩

 
def independentJet : Input Unit where
  atlas _ := False
  jet _ := True
  member _ _ := True
  value _ h := False.elim h
  time _ _ h _ := False.elim h

theorem second_need_not_require_first :
    c2 independentJet ∧ ¬ c1 independentJet := by
  exact ⟨fun _ => True.intro, fun h => h ()⟩

def complete {Ω} (d : Input Ω) : Prop :=
  c1 d ∧ c2 d ∧ c3 d ∧ c4 d ∧ c5 d

 
def f1 {Ω} (d : Input Ω) := ¬ c1 d
def f2 {Ω} (d : Input Ω) := c1 d ∧ ¬ c2 d
def f3 {Ω} (d : Input Ω) := c1 d ∧ c2 d ∧ ¬ c3 d
def f4 {Ω} (d : Input Ω) := c1 d ∧ ¬ c4 d
def f5 {Ω} (d : Input Ω) := c1 d ∧ ¬ c5 d

theorem five_failure_cover {Ω} (d : Input Ω) :
    ¬ complete d ↔ f1 d ∨ f2 d ∨ f3 d ∨ f4 d ∨ f5 d := by
  classical
  constructor
  · intro hn
    by_cases h1 : c1 d
    · by_cases h2 : c2 d
      · by_cases h3 : c3 d
        · by_cases h4 : c4 d
          · by_cases h5 : c5 d
            · exact False.elim (hn ⟨h1,h2,h3,h4,h5⟩)
            · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h1,h5⟩)))
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1,h4⟩)))
        · exact Or.inr (Or.inr (Or.inl ⟨h1,h2,h3⟩))
      · exact Or.inr (Or.inl ⟨h1,h2⟩)
    · exact Or.inl h1
  · intro hf hc
    rcases hf with h | h | h | h | h
    · exact h hc.1
    · exact h.2 hc.2.1
    · exact h.2.2 hc.2.2.1
    · exact h.2 hc.2.2.2.1
    · exact h.2 hc.2.2.2.2

def extend {X : Type} (D : X → Prop) (P : (x : X) → D x → Prop) (x : X) :
    Prop := ∃ h : D x, P x h

theorem extension_restricts {X : Type} (D : X → Prop)
    (P : (x : X) → D x → Prop) (x : X) (h : D x) :
    extend D P x ↔ P x h := by
  constructor
  · rintro ⟨_, hp⟩
    exact hp
  · exact fun hp => ⟨h,hp⟩

theorem extension_false_outside {X : Type} (D : X → Prop)
    (P : (x : X) → D x → Prop) (x : X) (h : ¬ D x) :
    ¬ extend D P x := by
  rintro ⟨hd,_⟩
  exact h hd

#print axioms third_requires_second
#print axioms fourth_requires_first
#print axioms fifth_requires_first
#print axioms third_restricts
#print axioms fourth_restricts
#print axioms fifth_restricts
#print axioms second_need_not_require_first
#print axioms five_failure_cover
#print axioms extension_restricts
#print axioms extension_false_outside
end LCTR.DifferentialNativeDomains
