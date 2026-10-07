theory Core_Audit_State_Transport
  imports Main
begin

datatype internal_state = SAT | Failed | NotFormed | NotEvaluable
datatype audit_status = Pass | Indeterminate | Unformed | Blocked | Fail

definition state where
  "state f e p q = (if \<not> (f \<and> p) then NotFormed else if \<not> e then NotEvaluable
    else if q then SAT else Failed)"
fun lift where
  "lift False s = Blocked"
| "lift True SAT = Pass"
| "lift True Failed = Fail"
| "lift True NotFormed = Unformed"
| "lift True NotEvaluable = Indeterminate"
fun priority :: "audit_status \<Rightarrow> nat" where
  "priority Pass = 0"
| "priority Indeterminate = 1"
| "priority Unformed = 2"
| "priority Blocked = 3"
| "priority Fail = 4"

definition recurs where
  "recurs E f e q s = (\<forall>x. s x = state (f x) (e x) (\<forall>y. E y x \<longrightarrow> s y = SAT) (q x))"
definition audit_at where
  "audit_at E s x = lift (\<forall>y. E y x \<longrightarrow> s y = SAT) (s x)"

lemma priority_injective: "inj priority"
proof (rule injI)
  fix a b
  assume "priority a = priority b"
  then show "a=b" by (cases a; cases b) auto
qed

locale audit_transport =
  fixes c :: "'a \<Rightarrow> 'b" and E :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and F :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
  assumes bij: "bij c" and edges: "\<And>a b. E a b \<longleftrightarrow> F (c a) (c b)"
begin

lemma predecessors_pass_iff:
  "(\<forall>y. F y (c x) \<longrightarrow> s y = SAT) \<longleftrightarrow> (\<forall>a. E a x \<longrightarrow> s (c a) = SAT)"
  using edges bij[THEN bij_is_surj] unfolding surj_def by metis

lemma recursion_pullback:
  assumes forms: "\<And>a. f1 (c a) = f0 a" and evals: "\<And>a. e1 (c a) = e0 a"
    and conditions: "\<And>a. q1 (c a) = q0 a" and rec: "recurs F f1 e1 q1 s"
  shows "recurs E f0 e0 q0 (s \<circ> c)"
proof (unfold recurs_def, intro allI)
  fix x
  have at_x: "s (c x) = state (f1 (c x)) (e1 (c x))
    (\<forall>y. F y (c x) \<longrightarrow> s y = SAT) (q1 (c x))"
    by (rule spec[OF rec[unfolded recurs_def]])
  show "(s \<circ> c) x = state (f0 x) (e0 x)
    (\<forall>y. E y x \<longrightarrow> (s \<circ> c) y = SAT) (q0 x)"
    using at_x by (simp only: o_def forms evals conditions predecessors_pass_iff)
qed

lemma state_covariance:
  assumes wf: "wfP E"
    and forms: "\<And>a. f1 (c a) = f0 a" and evals: "\<And>a. e1 (c a) = e0 a"
    and conditions: "\<And>a. q1 (c a) = q0 a"
    and h0: "recurs E f0 e0 q0 s0" and h1: "recurs F f1 e1 q1 s1"
  shows "s1 (c a) = s0 a"
proof -
  have hp: "recurs E f0 e0 q0 (s1 \<circ> c)"
    by (rule recursion_pullback[OF forms evals conditions h1])
  show ?thesis
  proof (rule wfp_induct[OF wf])
    fix x
    assume ih: "\<forall>y. E y x \<longrightarrow> s1 (c y) = s0 y"
    have same_pred: "(\<forall>y. E y x \<longrightarrow> s1 (c y) = SAT) =
      (\<forall>y. E y x \<longrightarrow> s0 y = SAT)" using ih by auto
    have eq1: "s1 (c x) = state (f0 x) (e0 x) (\<forall>y. E y x \<longrightarrow> s1 (c y) = SAT) (q0 x)"
      using spec[OF hp[unfolded recurs_def], of x] by (simp only: o_def)
    have eq0: "s0 x = state (f0 x) (e0 x) (\<forall>y. E y x \<longrightarrow> s0 y = SAT) (q0 x)"
      by (rule spec[OF h0[unfolded recurs_def]])
    have same_rhs: "state (f0 x) (e0 x) (\<forall>y. E y x \<longrightarrow> s1 (c y) = SAT) (q0 x) =
      state (f0 x) (e0 x) (\<forall>y. E y x \<longrightarrow> s0 y = SAT) (q0 x)"
      by (rule arg_cong[where f="\<lambda>p. state (f0 x) (e0 x) p (q0 x)", OF same_pred])
    show "s1 (c x) = s0 x" by (rule trans[OF eq1 trans[OF same_rhs sym[OF eq0]]])
  qed
qed

lemma audit_at_covariance:
  assumes states: "\<And>a. s1 (c a) = s0 a"
  shows "audit_at F s1 (c a) = audit_at E s0 a"
  unfolding audit_at_def by (simp add: predecessors_pass_iff states)

lemma audit_fiber_image:
  assumes states: "\<And>a. t (c a) = s a"
  shows "c ` {a. s a=q} = {b. t b=q}"
proof (rule set_eqI)
  fix b
  show "b \<in> c ` {a. s a=q} \<longleftrightarrow> b \<in> {b. t b=q}"
  proof
    assume "b \<in> c ` {a. s a=q}"
    then obtain a where ha: "s a=q" and hb: "b=c a" by blast
    show "b \<in> {b. t b=q}" using ha states[of a] unfolding hb by simp
  next
    assume hb: "b \<in> {b. t b=q}"
    obtain a where ca: "b=c a" using bij[THEN bij_is_surj] unfolding surj_def by blast
    have ha: "s a=q" using states[of a] hb ca by simp
    show "b \<in> c ` {a. s a=q}" using ha ca by blast
  qed
qed

lemma group_priority_covariance:
  assumes states: "\<And>a. t (c a) = s a"
  shows "Max (insert 0 ((priority \<circ> t) ` (c ` G))) = Max (insert 0 ((priority \<circ> s) ` G))"
proof -
  have "(priority \<circ> t) ` (c ` G) = (priority \<circ> s) ` G"
    by (simp add: image_image states)
  then show ?thesis by simp
qed

lemma indeterminate_signature_covariance:
  "(\<And>a. t (c a) = s a) \<Longrightarrow> (t (c a)=Indeterminate) = (s a=Indeterminate)"
  by simp

lemma audit_state_transport:
  assumes wf: "wfP E"
    and forms: "\<And>a. f1 (c a) = f0 a" and evals: "\<And>a. e1 (c a) = e0 a"
    and conditions: "\<And>a. q1 (c a) = q0 a"
    and h0: "recurs E f0 e0 q0 s0" and h1: "recurs F f1 e1 q1 s1"
  shows "(\<forall>a. audit_at F s1 (c a) = audit_at E s0 a) \<and>
    (\<forall>q. c ` {a. audit_at E s0 a=q} = {b. audit_at F s1 b=q})"
proof -
  have states: "\<And>a. s1 (c a) = s0 a"
    by (rule state_covariance[OF wf forms evals conditions h0 h1])
  have audits: "\<And>a. audit_at F s1 (c a) = audit_at E s0 a"
    by (rule audit_at_covariance; rule states)
  have fibers: "\<And>q. c ` {a. audit_at E s0 a=q} = {b. audit_at F s1 b=q}"
    by (rule audit_fiber_image; rule audits)
  show ?thesis using audits fibers by blast
qed
end

lemma blocked_and_unformed_distinct: "lift False NotFormed \<noteq> lift True NotFormed" by simp
lemma audit_failure_exact:
  "lift p (state f e p q) = Fail \<longleftrightarrow> f \<and> e \<and> p \<and> \<not>q"
  unfolding state_def by (cases f; cases e; cases p; cases q) auto
lemma missing_formation_not_failure: "lift p (state False e p q) \<noteq> Fail"
  unfolding state_def by (cases p) auto

ML \<open>
val roots = @{thms audit_transport.predecessors_pass_iff audit_transport.recursion_pullback audit_transport.state_covariance priority_injective audit_transport.audit_at_covariance audit_transport.audit_fiber_image audit_transport.group_priority_covariance audit_transport.indeterminate_signature_covariance blocked_and_unformed_distinct audit_failure_exact missing_formation_not_failure audit_transport.audit_state_transport};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
