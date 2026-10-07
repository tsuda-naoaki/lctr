theory Core_Series_Validity
  imports LCTR_Core_Finite_Audit.Core_Finite_Audit
begin

definition series_complete :: "(token\<Rightarrow>internal_state)\<Rightarrow>nat\<Rightarrow>bool" where
  "series_complete q i = (\<forall>t\<in>tokens. fst t=i \<longrightarrow> q t=SAT)"
definition full where "full q = (\<forall>i<6. series_complete q i)"
definition strict_complete where "strict_complete q = (\<forall>i<6. i\<noteq>3 \<longrightarrow> series_complete q i)"
definition approx_complete where "approx_complete q = series_complete q 3"

lemma series_completion_iff: "full q = (\<forall>t\<in>tokens. q t=SAT)"
  unfolding full_def series_complete_def tokens_def by auto

lemma completion_split: "full q = (strict_complete q \<and> approx_complete q)"
  unfolding full_def strict_complete_def approx_complete_def by auto

lemma completion_clears_failures:
  assumes "full q"
  shows "{t\<in>tokens. q t=Failed}={} \<and>
    {t\<in>tokens. fst t\<noteq>3 \<and> q t=Failed}={} \<and>
    {t\<in>tokens. fst t=3 \<and> q t=Failed}={}"
  using assms by (auto simp: series_completion_iff)

lemma no_failure_does_not_imply_completion:
  "\<exists>q::token\<Rightarrow>internal_state. {t\<in>tokens. q t=Failed}={} \<and> \<not>full q"
proof -
  have t: "(0,1)\<in>tokens" by (simp add: tokens_def count_def)
  have no: "{t\<in>tokens. (\<lambda>_. NotFormed) t=Failed}={}" by simp
  have notfull: "\<not>full (\<lambda>_. NotFormed)"
    using t by (auto simp: series_completion_iff)
  show ?thesis by (rule exI[of _ "\<lambda>_. NotFormed"], intro conjI; fact)
qed

lemma native_completion_iff_inputs:
  "full (run f e c 40) = (\<forall>t\<in>tokens. f t \<and> e t \<and> c t)"
proof
  assume full: "full (run f e c 40)"
  have sat: "\<And>t. t\<in>tokens \<Longrightarrow> run f e c 40 t=SAT"
    using full by (simp add: series_completion_iff)
  show "\<forall>t\<in>tokens. f t \<and> e t \<and> c t"
  proof (intro ballI)
    fix t
    assume t: "t\<in>tokens"
    have rec: "run f e c 40 t=state (f t) (e t) (predPass (run f e c 40) t) (c t)"
      using finite_run_solves[of f e c] t by (simp add: recurs_def step_def)
    show "f t \<and> e t \<and> c t"
      using rec sat[OF t] by (auto simp: state_def split: if_splits)
  qed
next
  assume inputs: "\<forall>t\<in>tokens. f t \<and> e t \<and> c t"
  have rec: "recurs f e c (\<lambda>_. SAT)"
    using inputs by (auto simp: recurs_def step_def predPass_def state_def)
  have sat: "\<And>t. t\<in>tokens \<Longrightarrow> run f e c 40 t=SAT"
    using finite_run_unique[OF rec] by simp
  show "full (run f e c 40)" using sat by (simp add: series_completion_iff)
qed

lemma native_audit_pass_iff_completion:
  "(\<forall>t\<in>tokens. auditOutput f e c t=Pass) = full (run f e c 40)"
proof -
  have lift_exact: "\<And>f e p c. (lift p (state f e p c)=Pass) = (state f e p c=SAT)"
    by (rename_tac f e p c, case_tac f; case_tac e; case_tac p; case_tac c)
      (simp_all add: state_def)
  have rec: "\<And>t. t\<in>tokens \<Longrightarrow> run f e c 40 t =
      state (f t) (e t) (predPass (run f e c 40) t) (c t)"
    using finite_run_solves[of f e c] by (simp add: recurs_def step_def)
  have exact: "\<And>t. t\<in>tokens \<Longrightarrow>
      (auditOutput f e c t=Pass) = (run f e c 40 t=SAT)"
  proof -
    fix t
    assume t: "t\<in>tokens"
    show "(auditOutput f e c t=Pass) = (run f e c 40 t=SAT)"
      unfolding auditOutput_def
      by (simp only: rec[OF t] lift_exact)
  qed
  show ?thesis using exact by (simp add: series_completion_iff)
qed

definition profile_state where
  "profile_state strict approx e l t = (if fst t=3 then approx e l (snd t) else strict e t)"
definition profile_strict_complete where
  "profile_strict_complete strict e = (\<forall>t\<in>tokens. fst t\<noteq>3 \<longrightarrow> strict e t=SAT)"
definition profile_approx_complete where
  "profile_approx_complete approx e l = (\<forall>j. 1\<le>j \<and> j\<le>count 3 \<longrightarrow> approx e l j=SAT)"

lemma profile_completion_iff:
  "full (profile_state strict approx e l) =
    (profile_strict_complete strict e \<and> profile_approx_complete approx e l)"
  unfolding series_completion_iff profile_state_def profile_strict_complete_def
    profile_approx_complete_def tokens_def
  by auto

lemma profile_strict_scale_independent:
  "fst t\<noteq>3 \<Longrightarrow> profile_state strict approx e a t = profile_state strict approx e b t"
  by (simp add: profile_state_def)

lemma validity_domain_intersection:
  "{l. full (profile_state strict approx e l)} =
    {l. profile_strict_complete strict e} \<inter> {l. profile_approx_complete approx e l}"
  by (auto simp: profile_completion_iff)

ML \<open>
val roots = @{thms series_completion_iff completion_split completion_clears_failures
  no_failure_does_not_imply_completion native_completion_iff_inputs
  native_audit_pass_iff_completion profile_completion_iff
  profile_strict_scale_independent validity_domain_intersection};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
