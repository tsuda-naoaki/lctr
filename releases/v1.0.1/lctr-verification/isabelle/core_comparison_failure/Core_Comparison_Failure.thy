theory Core_Comparison_Failure
  imports LCTR_Core_Finite_Audit.Core_Finite_Audit
begin

definition cmp_indices :: "nat set" where "cmp_indices={1..8}"
definition cmp_token :: "nat\<Rightarrow>token" where "cmp_token i=(0,i)"
lemma cmp_typed: "i\<in>cmp_indices \<Longrightarrow> cmp_token i\<in>tokens"
  by (simp add: cmp_indices_def cmp_token_def tokens_def count_def)
lemma comparison_incoming_exact:
  assumes i: "i\<in>cmp_indices" and t: "t\<in>tokens"
  shows "edge t (cmp_token i) = (\<exists>j\<in>cmp_indices. t=cmp_token j \<and> j+1=i)"
  using i t
  by (cases t; auto simp: cmp_indices_def cmp_token_def edge_def within_def tokens_def count_def; arith)

definition prefix where "prefix c i = (\<forall>j\<in>cmp_indices. j<i \<longrightarrow> c (cmp_token j))"
definition first where "first c i = (prefix c i \<and> \<not>c (cmp_token i))"

lemma incoming_from_prior_sat:
  assumes ii: "i\<in>cmp_indices"
    and prior: "\<And>j. j\<in>cmp_indices \<Longrightarrow> j<i \<Longrightarrow>
      (s (cmp_token j)=SAT) = (\<forall>k\<in>cmp_indices. k\<le>j \<longrightarrow> c (cmp_token k))"
  shows "predPass s (cmp_token i) = prefix c i"
proof
  assume passed: "predPass s (cmp_token i)"
  show "prefix c i"
  proof (unfold prefix_def, intro ballI impI)
    fix j
    assume ji: "j\<in>cmp_indices" and lt: "j<i"
    have p: "i-1\<in>cmp_indices" and pi: "i-1<i" and pred: "(i-1)+1=i"
      using ii ji lt unfolding cmp_indices_def by auto
    have edge: "edge (cmp_token (i-1)) (cmp_token i)"
      using comparison_incoming_exact[OF ii cmp_typed[OF p]] p pred by blast
    have sat: "s (cmp_token (i-1))=SAT"
      using passed cmp_typed[OF p] edge unfolding predPass_def by blast
    have all: "\<forall>k\<in>cmp_indices. k\<le>i-1 \<longrightarrow> c (cmp_token k)"
      using prior[OF p pi] sat by simp
    show "c (cmp_token j)" using all ji lt by auto
  qed
next
  assume pre: "prefix c i"
  show "predPass s (cmp_token i)"
  proof (unfold predPass_def, intro ballI impI)
    fix t
    assume tt: "t\<in>tokens" and edge: "edge t (cmp_token i)"
    obtain j where ji: "j\<in>cmp_indices" and tj: "t=cmp_token j" and suc: "j+1=i"
      using comparison_incoming_exact[OF ii tt] edge by blast
    have lt: "j<i" using suc by arith
    have all: "\<forall>k\<in>cmp_indices. k\<le>j \<longrightarrow> c (cmp_token k)"
      using pre lt unfolding prefix_def by auto
    show "s t=SAT" using prior[OF ji lt] all tj by simp
  qed
qed

locale ready_comparison =
  fixes f e c :: "token\<Rightarrow>bool" and s :: "token\<Rightarrow>internal_state"
  assumes rec: "recurs f e c s"
    and ready: "\<And>i. i\<in>cmp_indices \<Longrightarrow> f (cmp_token i) \<and> e (cmp_token i)"
begin
lemma comparison_sat_prefix:
  assumes ii: "i\<in>cmp_indices"
  shows "(s (cmp_token i)=SAT) = (\<forall>j\<in>cmp_indices. j\<le>i \<longrightarrow> c (cmp_token j))"
  using ii
proof (induction i rule: less_induct)
  case (less i)
  have ii: "i\<in>cmp_indices" by fact
  have incoming: "predPass s (cmp_token i) = prefix c i"
    by (rule incoming_from_prior_sat[OF ii]) (use less.IH in blast)
  have at: "s (cmp_token i)=state (f (cmp_token i)) (e (cmp_token i))
      (predPass s (cmp_token i)) (c (cmp_token i))"
    using rec cmp_typed[OF ii] by (simp add: recurs_def step_def)
  have exact: "(s (cmp_token i)=SAT) = (prefix c i \<and> c (cmp_token i))"
    using at ready[OF ii] incoming by (auto simp: state_def)
  show ?case using ii exact unfolding prefix_def by (auto simp: le_eq_less_or_eq)
qed

lemma comparison_failed_prefix:
  assumes ii: "i\<in>cmp_indices"
  shows "(s (cmp_token i)=Failed) = first c i"
proof -
  have incoming: "predPass s (cmp_token i)=prefix c i"
    by (rule incoming_from_prior_sat[OF ii]) (use comparison_sat_prefix in blast)
  have at: "s (cmp_token i)=state (f (cmp_token i)) (e (cmp_token i))
      (predPass s (cmp_token i)) (c (cmp_token i))"
    using rec cmp_typed[OF ii] by (simp add: recurs_def step_def)
  show ?thesis using at ready[OF ii] incoming by (auto simp: state_def first_def)
qed
end

lemma first_index_unique:
  assumes ii: "i\<in>cmp_indices" and ji: "j\<in>cmp_indices"
    and fi: "first c i" and fj: "first c j"
  shows "i=j"
  using assms unfolding first_def prefix_def by (metis less_linear)

lemma first_failure_partition:
  "(\<not>(\<forall>i\<in>cmp_indices. c (cmp_token i))) = (\<exists>!i. i\<in>cmp_indices \<and> first c i)"
proof
  assume fails: "\<not>(\<forall>i\<in>cmp_indices. c (cmp_token i))"
  let ?bad = "{i\<in>cmp_indices. \<not>c (cmp_token i)}"
  have finite: "finite ?bad" by (simp add: cmp_indices_def)
  have ne: "?bad\<noteq>{}" using fails by blast
  have mem: "Min ?bad\<in>?bad" by (rule Min_in[OF finite ne])
  have lower: "\<And>j. j\<in>?bad \<Longrightarrow> Min ?bad\<le>j" by (rule Min_le[OF finite])
  have p: "prefix c (Min ?bad)" using lower unfolding prefix_def by fastforce
  have fi: "first c (Min ?bad)" using mem p unfolding first_def by simp
  show "\<exists>!i. i\<in>cmp_indices \<and> first c i"
  proof (rule ex1I[of _ "Min ?bad"])
    show "Min ?bad\<in>cmp_indices \<and> first c (Min ?bad)" using mem fi by simp
    fix j
    assume j: "j\<in>cmp_indices \<and> first c j"
    show "j=Min ?bad" by (rule first_index_unique) (use j mem fi in auto)
  qed
next
  assume "\<exists>!i. i\<in>cmp_indices \<and> first c i"
  then obtain i where "i\<in>cmp_indices" "first c i" by blast
  then show "\<not>(\<forall>i\<in>cmp_indices. c (cmp_token i))" unfolding first_def by blast
qed

locale native_comparison =
  fixes f e c :: "token\<Rightarrow>bool"
  assumes ready: "\<And>i. i\<in>cmp_indices \<Longrightarrow> f (cmp_token i) \<and> e (cmp_token i)"
begin
sublocale R: ready_comparison f e c "run f e c 40"
  by unfold_locales (fact finite_run_solves, fact ready)

lemma native_failure_partition:
  "(\<not>(\<forall>i\<in>cmp_indices. c (cmp_token i))) =
    (\<exists>!i. i\<in>cmp_indices \<and> run f e c 40 (cmp_token i)=Failed)"
proof -
  have exact: "\<And>i. (i\<in>cmp_indices \<and> run f e c 40 (cmp_token i)=Failed) =
    (i\<in>cmp_indices \<and> first c i)"
    using R.comparison_failed_prefix by auto
  show ?thesis by (simp only: exact first_failure_partition)
qed

definition signature where "signature j = (if run f e c 40 (cmp_token j)=Failed then 1 else 0::nat)"
definition basis where "basis i j = (if j=i then 1 else 0::nat)"

lemma native_signature_at_failure:
  assumes ii: "i\<in>cmp_indices" and hi: "run f e c 40 (cmp_token i)=Failed"
  shows "\<forall>j\<in>cmp_indices. signature j=basis i j"
proof (intro ballI)
  fix j
  assume ji: "j\<in>cmp_indices"
  have fi: "first c i" using R.comparison_failed_prefix[OF ii] hi by simp
  have iff: "(run f e c 40 (cmp_token j)=Failed) = (j=i)"
    using first_index_unique[OF ji ii _ fi] R.comparison_failed_prefix[OF ji] hi by blast
  show "signature j=basis i j" by (simp add: signature_def basis_def iff)
qed

lemma native_signature_unique:
  assumes fails: "\<not>(\<forall>i\<in>cmp_indices. c (cmp_token i))"
  shows "\<exists>!i. i\<in>cmp_indices \<and> (\<forall>j\<in>cmp_indices. signature j=basis i j)"
proof -
  obtain i where ii: "i\<in>cmp_indices" and hi: "run f e c 40 (cmp_token i)=Failed"
    using native_failure_partition fails by blast
  have sig: "\<forall>j\<in>cmp_indices. signature j=basis i j" by (rule native_signature_at_failure[OF ii hi])
  show ?thesis
  proof (rule ex1I[of _ i])
    show "i\<in>cmp_indices \<and> (\<forall>j\<in>cmp_indices. signature j=basis i j)" using ii sig by simp
    fix j
    assume j: "j\<in>cmp_indices \<and> (\<forall>k\<in>cmp_indices. signature k=basis j k)"
    have at: "signature i=basis j i" using j ii by blast
    have "basis j i=1" using at hi by (simp add: signature_def)
    then show "j=i" by (auto simp: basis_def split: if_splits)
  qed
qed

lemma native_signature_component_sum:
  assumes fails: "\<not>(\<forall>i\<in>cmp_indices. c (cmp_token i))"
  shows "sum signature cmp_indices=1"
proof -
  obtain i where ii: "i\<in>cmp_indices" and sig: "\<forall>j\<in>cmp_indices. signature j=basis i j"
    using native_signature_unique[OF fails] by blast
  have eq: "sum signature cmp_indices=sum (basis i) cmp_indices"
    by (rule sum.cong) (use sig in auto)
  show ?thesis using eq ii by (simp add: basis_def cmp_indices_def)
qed
end

lemma first_and_last_conditions:
  "(first c 1 = (\<not>c (cmp_token 1))) \<and>
   (first c 8 = ((\<forall>i\<in>{1..7}. c (cmp_token i)) \<and> \<not>c (cmp_token 8)))"
  unfolding first_def prefix_def cmp_indices_def by auto

lemma native_region_union:
  assumes ready: "\<And>x i. i\<in>cmp_indices \<Longrightarrow> f x (cmp_token i) \<and> e x (cmp_token i)"
  shows "{x. \<not>(\<forall>i\<in>cmp_indices. c x (cmp_token i))} =
    (\<Union>i\<in>cmp_indices. {x. run (f x) (e x) (c x) 40 (cmp_token i)=Failed})"
proof (rule set_eqI)
  fix x
  interpret N: native_comparison "f x" "e x" "c x" by standard (fact ready)
  show "(x\<in>{x. \<not>(\<forall>i\<in>cmp_indices. c x (cmp_token i))}) =
    (x\<in>(\<Union>i\<in>cmp_indices. {x. run (f x) (e x) (c x) 40 (cmp_token i)=Failed}))"
    using N.native_failure_partition N.R.comparison_failed_prefix
    by (auto simp: first_def)
qed

lemma native_regions_disjoint:
  assumes ready: "\<And>x i. i\<in>cmp_indices \<Longrightarrow> f x (cmp_token i) \<and> e x (cmp_token i)"
    and ii: "i\<in>cmp_indices" and ji: "j\<in>cmp_indices" and ne: "i\<noteq>j"
  shows "{x. run (f x) (e x) (c x) 40 (cmp_token i)=Failed} \<inter>
    {x. run (f x) (e x) (c x) 40 (cmp_token j)=Failed}={}"
proof (rule ccontr)
  assume "\<not>?thesis"
  then obtain x where hi: "run (f x) (e x) (c x) 40 (cmp_token i)=Failed"
    and hj: "run (f x) (e x) (c x) 40 (cmp_token j)=Failed" by blast
  interpret N: native_comparison "f x" "e x" "c x" by standard (fact ready)
  have fi: "first (c x) i" using N.R.comparison_failed_prefix[OF ii] hi by simp
  have fj: "first (c x) j" using N.R.comparison_failed_prefix[OF ji] hj by simp
  show False using first_index_unique[OF ii ji fi fj] ne by simp
qed

lemma unrefined_region_signature:
  assumes ready: "\<And>x i. i\<in>cmp_indices \<Longrightarrow> f x (cmp_token i) \<and> e x (cmp_token i)"
    and ii: "i\<in>cmp_indices"
    and sub: "R\<subseteq>{x. run (f x) (e x) (c x) 40 (cmp_token i)=Failed}"
    and xr: "x\<in>R"
  shows "\<forall>j\<in>cmp_indices. native_comparison.signature (f x) (e x) (c x) j =
    native_comparison.basis i j"
proof -
  interpret N: native_comparison "f x" "e x" "c x" by standard (fact ready)
  have fail: "run (f x) (e x) (c x) 40 (cmp_token i)=Failed" using sub xr by blast
  show ?thesis by (rule N.native_signature_at_failure[OF ii fail])
qed

ML \<open>
val roots = @{thms comparison_incoming_exact incoming_from_prior_sat
  ready_comparison.comparison_sat_prefix ready_comparison.comparison_failed_prefix
  first_index_unique first_failure_partition native_comparison.native_failure_partition
  native_comparison.native_signature_at_failure native_comparison.native_signature_unique
  native_comparison.native_signature_component_sum first_and_last_conditions
  native_region_union native_regions_disjoint unrefined_region_signature};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
