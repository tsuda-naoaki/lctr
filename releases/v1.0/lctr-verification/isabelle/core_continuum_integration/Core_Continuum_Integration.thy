theory Core_Continuum_Integration
  imports "LCTR_Core_Continuum_Boundary.Core_Continuum_Boundary"
    "LCTR_Core_Token_Graph.Core_Token_Graph"
begin

lemma all_sat_iff_tests:
  assumes wf: "wf E" and recurs: "s = eval_update E f e c s"
    and inputs: "\<And>x. x\<in>J \<Longrightarrow> f x \<and> e x"
    and outside: "\<And>x y. x\<in>J \<Longrightarrow> (y,x)\<in>E \<Longrightarrow> y\<notin>J \<Longrightarrow> s y=Sat"
  shows "(\<forall>x\<in>J. s x=Sat) = (\<forall>x\<in>J. c x)"
proof
  assume sat: "\<forall>x\<in>J. s x=Sat"
  show "\<forall>x\<in>J. c x"
  proof (intro ballI)
    fix x assume x: "x\<in>J"
    have ev: "local_state (f x) (e x) (\<forall>y. (y,x)\<in>E \<longrightarrow> s y=Sat) (c x)=Sat"
      using fun_cong[OF recurs, of x] sat x unfolding eval_update_def by simp
    show "c x" using state_sat_iff[THEN iffD1, OF ev] by blast
  qed
next
  assume cond: "\<forall>x\<in>J. c x"
  have result: "\<And>x. x\<in>J \<Longrightarrow> s x=Sat"
  proof -
    fix x
    show "x\<in>J \<Longrightarrow> s x=Sat"
      using wf
    proof (induction x rule: wf_induct_rule)
      case (less x)
      have pred: "\<forall>y. (y,x)\<in>E \<longrightarrow> s y=Sat"
      proof (intro allI impI)
        fix y assume yx: "(y,x)\<in>E"
        show "s y=Sat"
        proof (cases "y\<in>J")
          case True
          show ?thesis by (rule less.IH[OF yx True])
        next
          case False
          show ?thesis by (rule outside[OF less.prems yx False])
        qed
      qed
      have fx: "f x" and ex: "e x" using inputs[OF less.prems] by auto
      have cx: "c x" using cond less.prems by blast
      have ev: "local_state (f x) (e x) (\<forall>y. (y,x)\<in>E \<longrightarrow> s y=Sat) (c x)=Sat"
        by (simp add: state_sat_iff fx ex pred cx)
      show ?case using fun_cong[OF recurs, of x] ev unfolding eval_update_def by simp
    qed
  qed
  show "\<forall>x\<in>J. s x=Sat" using result by blast
qed

definition approx_set :: "token set" where "approx_set={t\<in>tokens. fst t=3}"

lemma approx_set_exact: "approx_set = {(3,i) |i. 1\<le>i \<and> i\<le>9}"
  by (auto simp: approx_set_def token_carrier_exact count_def)
lemma approx_set_card: "card approx_set=9"
  using strict_approx_card unfolding approx_set_def by blast

lemma approx_predecessor_kinds:
  "x\<in>approx_set \<Longrightarrow> (y,x)\<in>edges \<Longrightarrow> y\<in>approx_set \<or> (y\<in>tokens \<and> fst y=2)"
  by (auto simp: approx_set_def edges_def edge_def between_def)

definition input_sat where
  "input_sat f e s = ((\<forall>t\<in>tokens. fst t=2 \<longrightarrow> s t=Sat) \<and>
    (\<forall>t\<in>approx_set. f t \<and> e t))"

lemma approx_states_iff_conditions:
  assumes recurs: "s=eval_update edges f e c s" and inp: "input_sat f e s"
  shows "(\<forall>t\<in>approx_set. s t=Sat) = (\<forall>t\<in>approx_set. c t)"
proof -
  have fin: "finite edges" using finite_tokens edges_typed finite_subset by blast
  have wf: "wf edges" by (rule finite_acyclic_wf[OF fin concrete_acyclic])
  have inputs: "\<And>x. x\<in>approx_set \<Longrightarrow> f x \<and> e x"
    using inp unfolding input_sat_def by blast
  have outside: "\<And>x y. x\<in>approx_set \<Longrightarrow> (y,x)\<in>edges \<Longrightarrow> y\<notin>approx_set \<Longrightarrow> s y=Sat"
    using approx_predecessor_kinds inp unfolding input_sat_def by blast
  show ?thesis by (rule all_sat_iff_tests[OF wf recurs inputs outside])
qed

lemma quantitative_validity:
  fixes d eps :: "token\<Rightarrow>ereal"
  assumes recurs: "s=eval_update edges f e c s" and inp: "input_sat f e s"
    and dn: "\<And>i. i\<in>approx_set \<Longrightarrow> 0\<le>d i"
    and en: "\<And>i. i\<in>approx_set \<Longrightarrow> 0\<le>eps i"
    and encoding: "\<And>i. i\<in>approx_set \<Longrightarrow> c i = (d i\<le>eps i)"
  shows "((\<forall>i\<in>approx_set. s i=Sat) = valid approx_set d eps) \<and>
    ((\<forall>i\<in>approx_set. s i=Sat) = (\<forall>i\<in>approx_set. 0\<le>margin (eps i) (d i))) \<and>
    ((\<forall>i\<in>approx_set. s i=Sat) = (\<forall>i\<in>approx_set. excess (eps i) (d i)=0)) \<and>
    ((\<forall>i\<in>approx_set. s i=Sat) = (exceeded approx_set d eps={}))"
proof -
  interpret F: nonnegative_family approx_set d eps by standard (auto intro: dn en)
  have v: "(\<forall>i\<in>approx_set. s i=Sat) = valid approx_set d eps"
    using approx_states_iff_conditions[OF recurs inp] encoding unfolding valid_def by auto
  show ?thesis using v F.validity_characterizations by blast
qed

lemma operational_first_excess:
  fixes d :: "'a::linorder\<Rightarrow>token\<Rightarrow>ereal" and eps :: "token\<Rightarrow>ereal"
  assumes recurs: "\<And>x. s x=eval_update edges (f x) (e x) (c x) (s x)"
    and inp: "\<And>x. input_sat (f x) (e x) (s x)"
    and dn: "\<And>x i. i\<in>approx_set \<Longrightarrow> 0\<le>d x i"
    and en: "\<And>i. i\<in>approx_set \<Longrightarrow> 0\<le>eps i"
    and encoding: "\<And>x i. i\<in>approx_set \<Longrightarrow> c x i = (d x i\<le>eps i)"
    and mono: "\<And>i x y. i\<in>approx_set \<Longrightarrow> x\<le>y \<Longrightarrow> d x i\<le>d y i"
    and b: "least_in {x. \<not>(\<forall>i\<in>approx_set. s x i=Sat)} b"
  shows "maximal_initial {x. \<forall>i\<in>approx_set. s x i=Sat} = {x. x<b} \<and>
    exceeded approx_set (d b) eps\<noteq>{} \<and> (\<forall>x<b. exceeded approx_set (d x) eps={})"
proof -
  interpret G: nonnegative_scale_family approx_set d eps by standard (auto intro: dn en mono)
  have v: "\<And>x. (\<forall>i\<in>approx_set. s x i=Sat) = valid approx_set (d x) eps"
  proof -
    fix x
    have all: "((\<forall>i\<in>approx_set. s x i=Sat) = valid approx_set (d x) eps) \<and>
      ((\<forall>i\<in>approx_set. s x i=Sat) = (\<forall>i\<in>approx_set. 0\<le>margin (eps i) (d x i))) \<and>
      ((\<forall>i\<in>approx_set. s x i=Sat) = (\<forall>i\<in>approx_set. excess (eps i) (d x i)=0)) \<and>
      ((\<forall>i\<in>approx_set. s x i=Sat) = (exceeded approx_set (d x) eps={}))"
      by (rule quantitative_validity[where f="f x" and e="e x" and c="c x" and s="s x" and d="d x" and eps=eps,
        OF recurs inp dn en encoding])
    then show "(\<forall>i\<in>approx_set. s x i=Sat) = valid approx_set (d x) eps" by blast
  qed
  have hb: "least_in {x. \<not>valid approx_set (d x) eps} b" using b by (simp only: v)
  have domain: "{x. \<forall>i\<in>approx_set. s x i=Sat} = {x. valid approx_set (d x) eps}"
    by (rule Collect_cong, rule v)
  show ?thesis unfolding domain by (rule G.first_excess[OF hb])
qed

ML \<open>
val roots = @{thms all_sat_iff_tests approx_set_exact approx_set_card approx_predecessor_kinds
  approx_states_iff_conditions quantitative_validity operational_first_excess};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
