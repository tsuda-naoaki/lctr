theory Core_Continuum_Topology
  imports LCTR_Core_Continuum_Integration.Core_Continuum_Integration
begin

definition lower_semicontinuous_ereal :: "('a::topological_space\<Rightarrow>ereal)\<Rightarrow>bool" where
  "lower_semicontinuous_ereal m = (\<forall>a. open {x. a<m x})"

lemma positive_domain_open:
  fixes m :: "'a::topological_space\<Rightarrow>'i\<Rightarrow>ereal"
  assumes fin: "finite J" and lsc: "\<And>i. i\<in>J \<Longrightarrow> lower_semicontinuous_ereal (\<lambda>x. m x i)"
  shows "open {x. \<forall>i\<in>J. 0<m x i}"
proof -
  have oi: "\<forall>i\<in>J. open {x. 0<m x i}" using lsc unfolding lower_semicontinuous_ereal_def by blast
  have op: "open (\<Inter>i\<in>J. {x. 0<m x i})" by (rule open_INT[OF fin oi])
  have eq: "{x. \<forall>i\<in>J. 0<m x i} = (\<Inter>i\<in>J. {x. 0<m x i})" by blast
  show ?thesis unfolding eq by (rule op)
qed

lemma open_neighborhood_iff:
  "open V \<Longrightarrow> (x\<in>V) = (\<exists>W. open W \<and> x\<in>W \<and> W\<subseteq>V)"
  by blast

definition operational_robust where
  "operational_robust s d eps = ((\<forall>i\<in>approx_set. s i=Sat) \<and>
    (\<forall>i\<in>approx_set. 0<margin (eps i) (d i)))"

lemma robust_positive_iff:
  fixes d eps :: "token\<Rightarrow>ereal"
  assumes recurs: "s=eval_update edges f e c s" and inp: "input_sat f e s"
    and dn: "\<And>i. i\<in>approx_set \<Longrightarrow> 0\<le>d i"
    and en: "\<And>i. i\<in>approx_set \<Longrightarrow> 0\<le>eps i"
    and encoding: "\<And>i. i\<in>approx_set \<Longrightarrow> c i = (d i\<le>eps i)"
  shows "operational_robust s d eps = (\<forall>i\<in>approx_set. 0<margin (eps i) (d i))"
proof
  assume "operational_robust s d eps"
  then show "\<forall>i\<in>approx_set. 0<margin (eps i) (d i)" unfolding operational_robust_def by blast
next
  assume pos: "\<forall>i\<in>approx_set. 0<margin (eps i) (d i)"
  have num: "valid approx_set d eps"
    unfolding valid_def using margin_nonneg[OF en dn] pos by fastforce
  have all: "((\<forall>i\<in>approx_set. s i=Sat) = valid approx_set d eps)"
    using quantitative_validity[where f=f and e=e and c=c and s=s and d=d and eps=eps,
      OF recurs inp dn en encoding] by blast
  show "operational_robust s d eps" using all num pos unfolding operational_robust_def by blast
qed

locale approximation_margin_topology =
  fixes f e c :: "'a::topological_space\<Rightarrow>token\<Rightarrow>bool"
    and s :: "'a\<Rightarrow>token\<Rightarrow>eval_state"
    and d :: "'a\<Rightarrow>token\<Rightarrow>ereal" and eps :: "token\<Rightarrow>ereal"
  assumes recurs: "\<And>x. s x=eval_update edges (f x) (e x) (c x) (s x)"
    and inp: "\<And>x. input_sat (f x) (e x) (s x)"
    and dn: "\<And>x i. i\<in>approx_set \<Longrightarrow> 0\<le>d x i"
    and en: "\<And>i. i\<in>approx_set \<Longrightarrow> 0\<le>eps i"
    and encoding: "\<And>x i. i\<in>approx_set \<Longrightarrow> c x i = (d x i\<le>eps i)"
    and lsc: "\<And>i. i\<in>approx_set \<Longrightarrow> lower_semicontinuous_ereal (\<lambda>x. margin (eps i) (d x i))"
begin

lemma robust_domain_eq:
  "{x. operational_robust (s x) (d x) eps} = {x. \<forall>i\<in>approx_set. 0<margin (eps i) (d x i)}"
proof (rule Collect_cong)
  fix x
  show "operational_robust (s x) (d x) eps = (\<forall>i\<in>approx_set. 0<margin (eps i) (d x i))"
    by (rule robust_positive_iff[where f="f x" and e="e x" and c="c x" and s="s x" and d="d x" and eps=eps,
      OF recurs inp dn en encoding])
qed

lemma operational_robust_domain_open: "open {x. operational_robust (s x) (d x) eps}"
proof -
  have fin: "finite approx_set" unfolding approx_set_def using finite_tokens by simp
  show ?thesis unfolding robust_domain_eq by (rule positive_domain_open[OF fin lsc])
qed

lemma robust_open_neighborhood:
  "operational_robust (s x) (d x) eps =
    (\<exists>W. open W \<and> x\<in>W \<and> W\<subseteq>{y. operational_robust (s y) (d y) eps})"
  using open_neighborhood_iff[OF operational_robust_domain_open, of x] by simp
end

lemma missing_input_control:
  "(\<lambda>t. Unformed) = eval_update edges (\<lambda>t. False) (\<lambda>t. True) (\<lambda>t. True) (\<lambda>t. Unformed)"
  "\<forall>i\<in>approx_set. 0<margin 1 0"
  "\<not>operational_robust (\<lambda>t. Unformed) (\<lambda>t. 0) (\<lambda>t. 1)"
  by (auto simp: eval_update_def local_state_def margin_def operational_robust_def approx_set_exact)

ML \<open>
val roots = @{thms positive_domain_open open_neighborhood_iff robust_positive_iff
  approximation_margin_topology.robust_domain_eq approximation_margin_topology.operational_robust_domain_open
  approximation_margin_topology.robust_open_neighborhood missing_input_control};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
