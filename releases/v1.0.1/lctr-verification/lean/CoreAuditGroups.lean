import CoreFiniteAudit
import CoreAuditTags

namespace LCTR.CoreAuditGroups
set_option autoImplicit false
open LCTR.CoreTokenGraph LCTR.CoreAuditStateTransport LCTR.CoreFiniteAudit LCTR.CoreEvaluation
open LCTR.SelectedInputEvaluation

def groupTokens (i : Fin 6) : Finset Token := Finset.univ.filter (fun t => t.1=i)

theorem group_nonempty (i : Fin 6) : (groupTokens i).Nonempty := by
  obtain ⟨t,ht⟩ := series_partition.2 i
  exact ⟨t,by simp only [groupTokens,Finset.mem_filter,Finset.mem_univ,true_and]; exact ht⟩

def decode : ℕ → AuditStatus
  | 0 => .pass
  | 1 => .indeterminate
  | 2 => .unformed
  | 3 => .blocked
  | _ => .fail

theorem decode_priority (s : AuditStatus) : decode (priority s)=s := by cases s <;> rfl

def groupPriority (s : Token → AuditStatus) (i : Fin 6) : Nat := (groupTokens i).sup (fun t => priority (s t))
def groupStatus (s : Token → AuditStatus) (i : Fin 6) : AuditStatus := decode (groupPriority s i)

theorem group_attains_priority (s : Token → AuditStatus) (i : Fin 6) :
    ∃ t ∈ groupTokens i, groupPriority s i=priority (s t) :=
  Finset.exists_mem_eq_sup _ (group_nonempty i) _

theorem priority_groupStatus (s : Token → AuditStatus) (i : Fin 6) :
    priority (groupStatus s i)=groupPriority s i := by
  obtain ⟨t,_,ht⟩ := group_attains_priority s i
  unfold groupStatus
  rw [ht,decode_priority]

theorem group_attained (s : Token → AuditStatus) (i : Fin 6) :
    ∃ t ∈ groupTokens i, s t=groupStatus s i := by
  obtain ⟨t,ht,hp⟩ := group_attains_priority s i
  refine ⟨t,ht,?_⟩
  unfold groupStatus
  rw [hp,decode_priority]

theorem group_maximum (s : Token → AuditStatus) (i : Fin 6) :
    ∀ t ∈ groupTokens i, priority (s t) ≤ priority (groupStatus s i) := by
  intro t ht
  rw [priority_groupStatus]
  exact Finset.le_sup (f:=fun t => priority (s t)) ht

theorem group_status_unique (s : Token → AuditStatus) (i : Fin 6) :
    ∃! q : AuditStatus,
      (∃ t ∈ groupTokens i, s t=q) ∧ (∀ t ∈ groupTokens i, priority (s t) ≤ priority q) := by
  refine ⟨groupStatus s i,⟨group_attained s i,group_maximum s i⟩,?_⟩
  rintro q ⟨⟨t,ht,hq⟩,hmax⟩
  apply priority_injective
  apply le_antisymm
  · rw [← hq]
    exact group_maximum s i t ht
  · rw [priority_groupStatus]
    exact Finset.sup_le hmax

theorem group_tokens_image (c : Token ≃ Token) (groups : Fin 6 ≃ Fin 6)
    (hc : ∀ t, (c t).1=groups t.1) (i : Fin 6) :
    (groupTokens i).image c = groupTokens (groups i) := by
  ext t
  simp only [Finset.mem_image,groupTokens,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨a,ha,rfl⟩
    rw [hc,ha]
  · intro ht
    obtain ⟨a,rfl⟩ := c.surjective t
    have hga : groups a.1=groups i := (hc a).symm.trans ht
    exact ⟨a,groups.injective hga,rfl⟩

theorem group_status_covariance (c : Token ≃ Token) (groups : Fin 6 ≃ Fin 6)
    (hc : ∀ t, (c t).1=groups t.1)
    (s t : Token → AuditStatus) (hs : ∀ a, t (c a)=s a) (i : Fin 6) :
    groupStatus t (groups i)=groupStatus s i := by
  unfold groupStatus groupPriority
  rw [← group_tokens_image c groups hc i,group_priority_covariance c s t hs]

theorem audit_pass_exact (f e p q : Bool) :
    lift p (state f e p q)=.pass ↔ state f e p q=.sat := by
  cases f <;> cases e <;> cases p <;> cases q <;> decide

theorem audit_fail_exact (f e p q : Bool) :
    lift p (state f e p q)=.fail ↔ state f e p q=.failed := by
  cases f <;> cases e <;> cases p <;> cases q <;> decide

theorem native_failed_fiber (f e c : Token → Bool) :
    {x | auditOutput f e c x=.fail} = {x | run f e c 40 x=.failed} := by
  ext x
  have hx := finite_run_solves f e c x
  rw [← step_eq_native] at hx
  change lift (predecessorPass (run f e c 40) x) (run f e c 40 x)=.fail ↔ run f e c 40 x=.failed
  rw [hx]
  exact audit_fail_exact (f x) (e x) (predecessorPass (run f e c 40) x) (c x)

theorem native_pass_iff (f e c : Token → Bool) (x : Token) :
    auditOutput f e c x=.pass ↔ run f e c 40 x=.sat := by
  have hx := finite_run_solves f e c x
  rw [← step_eq_native] at hx
  change lift (predecessorPass (run f e c 40) x) (run f e c 40 x)=.pass ↔ run f e c 40 x=.sat
  rw [hx]
  exact audit_pass_exact (f x) (e x) (predecessorPass (run f e c 40) x) (c x)

end LCTR.CoreAuditGroups
