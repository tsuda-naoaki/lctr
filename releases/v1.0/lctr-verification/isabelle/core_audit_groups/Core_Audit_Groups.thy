theory Core_Audit_Groups
  imports "../support/core_finite_audit/Core_Finite_Audit"
    "../core_audit_state_transport/Core_Audit_State_Transport"
begin

type_synonym report_status = Core_Audit_State_Transport.audit_status
fun native_status :: "Core_Finite_Audit.audit_status \<Rightarrow> report_status" where
  "native_status Core_Finite_Audit.Pass = Core_Audit_State_Transport.Pass"
| "native_status Core_Finite_Audit.Indeterminate = Core_Audit_State_Transport.Indeterminate"
| "native_status Core_Finite_Audit.Unformed = Core_Audit_State_Transport.Unformed"
| "native_status Core_Finite_Audit.Blocked = Core_Audit_State_Transport.Blocked"
| "native_status Core_Finite_Audit.Fail = Core_Audit_State_Transport.Fail"
fun native_state :: "Core_Finite_Audit.internal_state \<Rightarrow> Core_Audit_State_Transport.internal_state" where
  "native_state Core_Finite_Audit.SAT = Core_Audit_State_Transport.SAT"
| "native_state Core_Finite_Audit.Failed = Core_Audit_State_Transport.Failed"
| "native_state Core_Finite_Audit.NotFormed = Core_Audit_State_Transport.NotFormed"
| "native_state Core_Finite_Audit.NotEvaluable = Core_Audit_State_Transport.NotEvaluable"
lemma native_status_bijective: "bij native_status"
proof -
  have injective: "inj native_status"
  proof (rule injI)
    fix x y assume "native_status x = native_status y"
    then show "x=y" by (cases x; cases y) simp_all
  qed
  have surjective: "surj native_status"
    unfolding surj_def
    by (metis native_status.simps Core_Audit_State_Transport.audit_status.exhaust)
  show ?thesis using injective surjective by (simp add: bij_def)
qed
lemma native_state_exact:
  "native_state (Core_Finite_Audit.state f e p q) = Core_Audit_State_Transport.state f e p q"
  by (simp add: Core_Finite_Audit.state_def Core_Audit_State_Transport.state_def)
lemma native_lift_exact:
  "native_status (Core_Finite_Audit.lift p x) = Core_Audit_State_Transport.lift p (native_state x)"
  by (cases p; cases x) simp_all

definition group_tokens :: "nat \<Rightarrow> Core_Finite_Audit.token set" where
  "group_tokens i = {t \<in> Core_Finite_Audit.tokens. fst t=i}"
definition decode :: "nat \<Rightarrow> report_status" where
  "decode n = (if n=0 then Core_Audit_State_Transport.Pass
    else if n=1 then Core_Audit_State_Transport.Indeterminate
    else if n=2 then Core_Audit_State_Transport.Unformed
    else if n=3 then Core_Audit_State_Transport.Blocked else Core_Audit_State_Transport.Fail)"
definition group_priority where
  "group_priority s i = Max (image (\<lambda>t. Core_Audit_State_Transport.priority (s t)) (group_tokens i))"
definition group_status where "group_status s i = decode (group_priority s i)"

lemma finite_tokens: "finite Core_Finite_Audit.tokens"
  using Core_Finite_Audit.token_list_exact by (metis finite_set)
lemma finite_group: "finite (group_tokens i)"
  by (simp add: group_tokens_def finite_tokens)
lemma group_nonempty:
  assumes i: "i<6"
  shows "group_tokens i \<noteq> {}"
proof -
  have cases: "i=0 \<or> i=1 \<or> i=2 \<or> i=3 \<or> i=4 \<or> i=5" using i by presburger
  have "(i,1) \<in> group_tokens i"
    using cases by (auto simp: group_tokens_def Core_Finite_Audit.tokens_def Core_Finite_Audit.count_def)
  then show ?thesis by blast
qed
lemma decode_priority: "decode (Core_Audit_State_Transport.priority s) = s"
  by (cases s) (simp_all add: decode_def)
lemma group_attains_priority:
  assumes i: "i<6"
  shows "\<exists>t\<in>group_tokens i. group_priority s i = Core_Audit_State_Transport.priority (s t)"
proof -
  have fin: "finite (image (\<lambda>t. Core_Audit_State_Transport.priority (s t)) (group_tokens i))"
    by (rule finite_imageI[OF finite_group])
  have ne: "image (\<lambda>t. Core_Audit_State_Transport.priority (s t)) (group_tokens i) \<noteq> {}"
    using group_nonempty[OF i] by simp
  have mem: "group_priority s i \<in> image (\<lambda>t. Core_Audit_State_Transport.priority (s t)) (group_tokens i)"
    unfolding group_priority_def by (rule Max_in[OF fin ne])
  then show ?thesis by blast
qed
lemma priority_groupStatus:
  "i<6 \<Longrightarrow> Core_Audit_State_Transport.priority (group_status s i) = group_priority s i"
  using group_attains_priority by (metis group_status_def decode_priority)
lemma group_attained:
  "i<6 \<Longrightarrow> \<exists>t\<in>group_tokens i. s t=group_status s i"
  using group_attains_priority by (metis group_status_def decode_priority)
lemma group_maximum:
  assumes i: "i<6" and t: "t \<in> group_tokens i"
  shows "Core_Audit_State_Transport.priority (s t) \<le> Core_Audit_State_Transport.priority (group_status s i)"
proof -
  have "Core_Audit_State_Transport.priority (s t) \<le> group_priority s i"
    unfolding group_priority_def by (rule Max_ge; simp add: finite_group t)
  then show ?thesis by (simp only: priority_groupStatus[OF i])
qed
lemma group_status_unique:
  assumes i: "i<6"
  shows "\<exists>!q. (\<exists>t\<in>group_tokens i. s t=q) \<and>
    (\<forall>t\<in>group_tokens i. Core_Audit_State_Transport.priority (s t) \<le> Core_Audit_State_Transport.priority q)"
proof (rule ex1I[of _ "group_status s i"])
  show "(\<exists>t\<in>group_tokens i. s t=group_status s i) \<and>
    (\<forall>t\<in>group_tokens i. Core_Audit_State_Transport.priority (s t) \<le> Core_Audit_State_Transport.priority (group_status s i))"
    using group_attained[OF i] group_maximum[OF i] by blast
next
  fix q
  assume q: "(\<exists>t\<in>group_tokens i. s t=q) \<and>
    (\<forall>t\<in>group_tokens i. Core_Audit_State_Transport.priority (s t) \<le> Core_Audit_State_Transport.priority q)"
  have le: "Core_Audit_State_Transport.priority q \<le> Core_Audit_State_Transport.priority (group_status s i)"
    using q group_maximum[OF i] by blast
  have ge: "Core_Audit_State_Transport.priority (group_status s i) \<le> Core_Audit_State_Transport.priority q"
  proof -
    obtain t where t: "t\<in>group_tokens i" and st: "s t=group_status s i"
      using group_attained[OF i, where s=s] by blast
    have bound: "Core_Audit_State_Transport.priority (s t) \<le> Core_Audit_State_Transport.priority q"
      using q t by blast
    show ?thesis using bound by (simp only: st)
  qed
  have eq_priority: "Core_Audit_State_Transport.priority q = Core_Audit_State_Transport.priority (group_status s i)"
    using le ge by (rule antisym)
  show "q=group_status s i"
    by (rule injD[OF Core_Audit_State_Transport.priority_injective eq_priority])
qed

locale group_transport =
  fixes c :: "Core_Finite_Audit.token \<Rightarrow> Core_Finite_Audit.token" and g :: "nat \<Rightarrow> nat"
  assumes cb: "bij_betw c Core_Finite_Audit.tokens Core_Finite_Audit.tokens"
    and gb: "bij_betw g {..<6} {..<6}"
    and series: "\<And>t. t\<in>Core_Finite_Audit.tokens \<Longrightarrow> fst (c t)=g (fst t)"
begin
lemma group_tokens_image:
  assumes i: "i<6"
  shows "image c (group_tokens i) = group_tokens (g i)"
proof (rule set_eqI, rule iffI)
  fix t assume "t \<in> image c (group_tokens i)"
  then obtain a where a: "a\<in>group_tokens i" and t: "t=c a" by blast
  have at: "a\<in>Core_Finite_Audit.tokens" and ai: "fst a=i" using a by (auto simp: group_tokens_def)
  have ct: "c a\<in>Core_Finite_Audit.tokens" using cb at by (meson bij_betwE)
  show "t\<in>group_tokens (g i)" using ct series[OF at] ai by (simp add: group_tokens_def t)
next
  fix t assume t: "t\<in>group_tokens (g i)"
  then have tt: "t\<in>Core_Finite_Audit.tokens" and ti: "fst t=g i" by (auto simp: group_tokens_def)
  have ci: "image c Core_Finite_Audit.tokens = Core_Finite_Audit.tokens"
    by (rule conjunct2[OF cb[unfolded bij_betw_def]])
  have tm: "t\<in>image c Core_Finite_Audit.tokens" using tt by (simp only: ci)
  obtain a where a: "a\<in>Core_Finite_Audit.tokens" and ca: "c a=t"
    using tm by auto
  have af: "fst a<6" using a by (auto simp: Core_Finite_Audit.tokens_def)
  have eq: "g (fst a)=g i" using series[OF a] ca ti by simp
  have gi: "inj_on g {..<6}" by (rule conjunct1[OF gb[unfolded bij_betw_def]])
  have ai: "fst a=i" by (rule inj_onD[OF gi eq]) (use af i in auto)
  have "a\<in>group_tokens i" using a ai by (simp add: group_tokens_def)
  then show "t\<in>image c (group_tokens i)" using ca by blast
qed
lemma group_status_covariance:
  assumes i: "i<6" and st: "\<And>a. a\<in>Core_Finite_Audit.tokens \<Longrightarrow> t (c a)=s a"
  shows "group_status t (g i)=group_status s i"
proof -
  have images: "image (\<lambda>a. Core_Audit_State_Transport.priority (t (c a))) (group_tokens i) =
    image (\<lambda>a. Core_Audit_State_Transport.priority (s a)) (group_tokens i)"
    by (rule image_cong) (auto simp: group_tokens_def st)
  show ?thesis
    unfolding group_status_def group_priority_def
    by (simp only: group_tokens_image[OF i, symmetric] image_image images)
qed
end

lemma audit_pass_exact:
  "Core_Audit_State_Transport.lift p (Core_Audit_State_Transport.state f e p q) = Core_Audit_State_Transport.Pass
    \<longleftrightarrow> Core_Audit_State_Transport.state f e p q = Core_Audit_State_Transport.SAT"
  by (cases f; cases e; cases p; cases q) (simp_all add: Core_Audit_State_Transport.state_def)
lemma audit_fail_exact:
  "Core_Audit_State_Transport.lift p (Core_Audit_State_Transport.state f e p q) = Core_Audit_State_Transport.Fail
    \<longleftrightarrow> Core_Audit_State_Transport.state f e p q = Core_Audit_State_Transport.Failed"
  by (cases f; cases e; cases p; cases q) (simp_all add: Core_Audit_State_Transport.state_def)
lemma native_pass_state:
  "native_status (Core_Finite_Audit.lift p (Core_Finite_Audit.state f e p q))=Core_Audit_State_Transport.Pass
    \<longleftrightarrow> Core_Finite_Audit.state f e p q=Core_Finite_Audit.SAT"
  by (cases f; cases e; cases p; cases q) (simp_all add: Core_Finite_Audit.state_def)
lemma native_fail_state:
  "native_status (Core_Finite_Audit.lift p (Core_Finite_Audit.state f e p q))=Core_Audit_State_Transport.Fail
    \<longleftrightarrow> Core_Finite_Audit.state f e p q=Core_Finite_Audit.Failed"
  by (cases f; cases e; cases p; cases q) (simp_all add: Core_Finite_Audit.state_def)
lemma native_failed_fiber:
  "{x\<in>Core_Finite_Audit.tokens. native_status (Core_Finite_Audit.auditOutput f e q x)=Core_Audit_State_Transport.Fail} =
    {x\<in>Core_Finite_Audit.tokens. Core_Finite_Audit.run f e q 40 x=Core_Finite_Audit.Failed}"
proof (rule set_eqI)
  fix x
  have rec: "x\<in>Core_Finite_Audit.tokens \<Longrightarrow> Core_Finite_Audit.run f e q 40 x =
    Core_Finite_Audit.state (f x) (e x) (Core_Finite_Audit.predPass (Core_Finite_Audit.run f e q 40) x) (q x)"
    using Core_Finite_Audit.finite_run_solves[of f e q]
    by (simp add: Core_Finite_Audit.recurs_def Core_Finite_Audit.step_def)
  have exact: "x\<in>Core_Finite_Audit.tokens \<Longrightarrow>
    (native_status (Core_Finite_Audit.auditOutput f e q x)=Core_Audit_State_Transport.Fail
    \<longleftrightarrow> Core_Finite_Audit.run f e q 40 x=Core_Finite_Audit.Failed)"
  proof -
    assume x: "x\<in>Core_Finite_Audit.tokens"
    show "native_status (Core_Finite_Audit.auditOutput f e q x)=Core_Audit_State_Transport.Fail
      \<longleftrightarrow> Core_Finite_Audit.run f e q 40 x=Core_Finite_Audit.Failed"
      by (simp only: Core_Finite_Audit.auditOutput_def rec[OF x] native_fail_state)
  qed
  show "x\<in>{x\<in>Core_Finite_Audit.tokens. native_status (Core_Finite_Audit.auditOutput f e q x)=Core_Audit_State_Transport.Fail}
    \<longleftrightarrow> x\<in>{x\<in>Core_Finite_Audit.tokens. Core_Finite_Audit.run f e q 40 x=Core_Finite_Audit.Failed}"
    using exact by auto
qed
lemma native_pass_iff:
  assumes x: "x\<in>Core_Finite_Audit.tokens"
  shows "native_status (Core_Finite_Audit.auditOutput f e q x)=Core_Audit_State_Transport.Pass
    \<longleftrightarrow> Core_Finite_Audit.run f e q 40 x=Core_Finite_Audit.SAT"
proof -
  have rec: "Core_Finite_Audit.run f e q 40 x =
    Core_Finite_Audit.state (f x) (e x) (Core_Finite_Audit.predPass (Core_Finite_Audit.run f e q 40) x) (q x)"
    using Core_Finite_Audit.finite_run_solves[of f e q] x
    by (simp add: Core_Finite_Audit.recurs_def Core_Finite_Audit.step_def)
  show ?thesis by (simp only: Core_Finite_Audit.auditOutput_def rec native_pass_state)
qed

ML \<open>
val roots = @{thms group_nonempty decode_priority group_attains_priority priority_groupStatus group_attained group_maximum group_status_unique group_transport.group_tokens_image group_transport.group_status_covariance audit_pass_exact audit_fail_exact native_failed_fiber native_pass_iff};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
