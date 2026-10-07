theory Core_Continuum_Boundary
  imports "HOL-Library.Extended_Real"
begin

definition margin :: "ereal \<Rightarrow> ereal \<Rightarrow> ereal" where
  "margin a b = (if a=\<infinity> then if b=\<infinity> then 0 else \<infinity>
    else if b=\<infinity> then -\<infinity> else a-b)"
definition excess where "excess a b = max 0 (-margin a b)"

lemma margin_nonneg:
  "0\<le>a \<Longrightarrow> 0\<le>b \<Longrightarrow> (0\<le>margin a b) = (b\<le>a)"
  by (cases a; cases b) (auto simp: margin_def)
lemma margin_zero:
  "0\<le>a \<Longrightarrow> 0\<le>b \<Longrightarrow> (margin a b=0) = (b=a)"
  by (cases a; cases b) (auto simp: margin_def)
lemma margin_negative:
  "0\<le>a \<Longrightarrow> 0\<le>b \<Longrightarrow> (margin a b<0) = (a<b)"
  using margin_nonneg by (metis not_le)
lemma margin_positive:
  "0\<le>a \<Longrightarrow> 0\<le>b \<Longrightarrow> (0<margin a b) = (b<a)"
  using margin_nonneg margin_zero by (metis less_le)
lemma excess_nonneg: "0\<le>excess a b" unfolding excess_def by simp
lemma excess_zero:
  assumes a: "0\<le>a" and b: "0\<le>b"
  shows "(excess a b=0) = (b\<le>a)"
proof -
  have eq: "(excess a b=0) = (excess a b\<le>0)"
    using excess_nonneg[of a b] by auto
  have sign: "(excess a b\<le>0) = (0\<le>margin a b)"
    unfolding excess_def by simp
  show ?thesis using eq sign margin_nonneg[OF a b] by blast
qed
lemma excess_positive:
  "0\<le>a \<Longrightarrow> 0\<le>b \<Longrightarrow> (0<excess a b) = (a<b)"
  using excess_nonneg excess_zero by (metis less_le not_le)

definition valid where "valid J d e = (\<forall>i\<in>J. d i\<le>e i)"
definition saturated where "saturated J d e = {i\<in>J. margin (e i) (d i)=0}"
definition exceeded where "exceeded J d e = {i\<in>J. 0<excess (e i) (d i)}"
definition robust where "robust J d e = (valid J d e \<and> (\<forall>i\<in>J. 0<margin (e i) (d i)))"

locale nonnegative_family =
  fixes J :: "'i set" and d e :: "'i\<Rightarrow>ereal"
  assumes d_nonneg: "i\<in>J \<Longrightarrow> 0\<le>d i" and e_nonneg: "i\<in>J \<Longrightarrow> 0\<le>e i"
begin

lemma validity_characterizations:
  "(valid J d e = (\<forall>i\<in>J. 0\<le>margin (e i) (d i))) \<and>
   (valid J d e = (\<forall>i\<in>J. excess (e i) (d i)=0)) \<and>
   (valid J d e = (exceeded J d e={}))"
  unfolding valid_def exceeded_def
  using margin_nonneg[OF e_nonneg d_nonneg] excess_zero[OF e_nonneg d_nonneg]
    excess_positive[OF e_nonneg d_nonneg] by auto

lemma saturation_excess_disjoint: "saturated J d e \<inter> exceeded J d e = {}"
  unfolding saturated_def exceeded_def
  using margin_zero[OF e_nonneg d_nonneg] excess_positive[OF e_nonneg d_nonneg] by fastforce

lemma valid_not_robust:
  "(valid J d e \<and> \<not>robust J d e) = (saturated J d e\<noteq>{} \<and> exceeded J d e={})"
proof
  assume lhs: "valid J d e \<and> \<not>robust J d e"
  then obtain i where i: "i\<in>J" and np: "\<not>0<margin (e i) (d i)"
    unfolding robust_def by blast
  have nn: "0\<le>margin (e i) (d i)" using lhs validity_characterizations i by blast
  have mz: "margin (e i) (d i)=0" using nn np by simp
  have sat: "saturated J d e\<noteq>{}" using i mz unfolding saturated_def by blast
  have exc: "exceeded J d e={}" using lhs validity_characterizations by blast
  show "saturated J d e\<noteq>{} \<and> exceeded J d e={}" using sat exc by simp
next
  assume rhs: "saturated J d e\<noteq>{} \<and> exceeded J d e={}"
  then have v: "valid J d e" using validity_characterizations by blast
  obtain i where i: "i\<in>J" and mz: "margin (e i) (d i)=0"
    using rhs unfolding saturated_def by blast
  have nr: "\<not>robust J d e"
  proof
    assume r: "robust J d e"
    have "0<margin (e i) (d i)" using r i unfolding robust_def by blast
    then show False using mz by simp
  qed
  show "valid J d e \<and> \<not>robust J d e" using v nr by simp
qed

lemma subset_saturation:
  "A\<subseteq>J \<Longrightarrow> (A\<subseteq>saturated J d e) = (\<forall>i\<in>A. d i=e i)"
  unfolding saturated_def using margin_zero[OF e_nonneg d_nonneg] by auto
lemma subset_excess:
  "A\<subseteq>J \<Longrightarrow> (A\<subseteq>exceeded J d e) = (\<forall>i\<in>A. e i<d i)"
  unfolding exceeded_def using excess_positive[OF e_nonneg d_nonneg] by auto
end

definition initial :: "'a::preorder set\<Rightarrow>bool" where
  "initial A = (\<forall>x y. x\<le>y \<longrightarrow> y\<in>A \<longrightarrow> x\<in>A)"
definition initial_family where "initial_family V = {A. A\<subseteq>V \<and> initial A}"
definition maximal_initial where "maximal_initial V = \<Union>(initial_family V)"

lemma maximal_initial_greatest:
  "maximal_initial V\<in>initial_family V \<and> (\<forall>A\<in>initial_family V. A\<subseteq>maximal_initial V)"
  unfolding maximal_initial_def initial_family_def initial_def by blast
lemma maximal_initial_eq:
  "initial V \<Longrightarrow> maximal_initial V=V"
  using maximal_initial_greatest unfolding initial_family_def by blast

lemma monotone_defects_initial:
  fixes d :: "'a::preorder\<Rightarrow>'i\<Rightarrow>ereal" and e :: "'i\<Rightarrow>ereal"
  assumes "\<And>i x y. i\<in>J \<Longrightarrow> x\<le>y \<Longrightarrow> d x i\<le>d y i"
  shows "initial {x. valid J (d x) e}"
proof (unfold initial_def, intro allI impI)
  fix x y
  assume xy: "x\<le>y" and vy: "y\<in>{x. valid J (d x) e}"
  have all: "\<forall>i\<in>J. d x i\<le>e i"
  proof (intro ballI)
    fix i
    assume i: "i\<in>J"
    have dxy: "d x i\<le>d y i" by (rule assms[OF i xy])
    have dye: "d y i\<le>e i" using vy i unfolding valid_def by simp
    show "d x i\<le>e i" by (rule order_trans[OF dxy dye])
  qed
  then show "x\<in>{x. valid J (d x) e}" unfolding valid_def by simp
qed

definition least_in :: "'a::order set\<Rightarrow>'a\<Rightarrow>bool" where
  "least_in A a = (a\<in>A \<and> (\<forall>x\<in>A. a\<le>x))"

lemma least_subset:
  "S\<subseteq>T \<Longrightarrow> least_in S a \<Longrightarrow> least_in T b \<Longrightarrow> b\<le>a"
  unfolding least_in_def by blast
lemma initial_boundary:
  fixes b :: "'a::linorder"
  assumes "initial V" "least_in (-V) b"
  shows "V = {x. x<b}"
proof (rule set_eqI)
  fix x
  have bn: "b\<notin>V" and low: "\<And>y. y\<notin>V \<Longrightarrow> b\<le>y"
    using assms(2) unfolding least_in_def by auto
  show "(x\<in>V) = (x\<in>{x. x<b})"
  proof
    assume xv: "x\<in>V"
    have "\<not>b\<le>x"
    proof
      assume bx: "b\<le>x"
      have "b\<in>V" using assms(1) bx xv unfolding initial_def by blast
      then show False using bn by simp
    qed
    then show "x\<in>{x. x<b}" by simp
  next
    assume "x\<in>{x. x<b}"
    then have xb: "x<b" by simp
    show "x\<in>V"
    proof (rule ccontr)
      assume xn: "x\<notin>V"
      have "b\<le>x" by (rule low[OF xn])
      then show False using xb by simp
    qed
  qed
qed

lemma maximal_effective_interval:
  fixes d :: "'a::preorder\<Rightarrow>'i\<Rightarrow>ereal" and e :: "'i\<Rightarrow>ereal"
  assumes "\<And>i x y. i\<in>J \<Longrightarrow> x\<le>y \<Longrightarrow> d x i\<le>d y i"
  shows "maximal_initial {x. valid J (d x) e} = {x. valid J (d x) e}"
  by (rule maximal_initial_eq[OF monotone_defects_initial[OF assms]])

locale nonnegative_scale_family =
  fixes J :: "'i set" and d :: "'a::linorder\<Rightarrow>'i\<Rightarrow>ereal" and e :: "'i\<Rightarrow>ereal"
  assumes d_nonneg: "i\<in>J \<Longrightarrow> 0\<le>d x i" and e_nonneg: "i\<in>J \<Longrightarrow> 0\<le>e i"
    and monotone: "i\<in>J \<Longrightarrow> x\<le>y \<Longrightarrow> d x i\<le>d y i"
begin

lemma validity_excess: "valid J (d x) e = (exceeded J (d x) e={})"
proof -
  interpret F: nonnegative_family J "d x" e
    by standard (auto intro: d_nonneg e_nonneg)
  show ?thesis using F.validity_characterizations by blast
qed

lemma first_excess:
  assumes b: "least_in {x. \<not>valid J (d x) e} b"
  shows "maximal_initial {x. valid J (d x) e} = {x. x<b} \<and>
    exceeded J (d b) e\<noteq>{} \<and> (\<forall>x<b. exceeded J (d x) e={})"
proof -
  have hb: "least_in (-{x. valid J (d x) e}) b" using b unfolding least_in_def by auto
  have bound: "{x. valid J (d x) e}={x. x<b}"
    by (rule initial_boundary[OF monotone_defects_initial[OF monotone] hb])
  have maxeq: "maximal_initial {x. valid J (d x) e}={x. x<b}"
    using maximal_effective_interval[where J=J and d=d and e=e, OF monotone] bound by simp
  show ?thesis using maxeq bound b validity_excess unfolding least_in_def by blast
qed

lemma maximum_has_no_excess:
  "a\<in>maximal_initial {x. valid J (d x) e} \<Longrightarrow> exceeded J (d a) e={}"
  using maximal_initial_greatest[of "{x. valid J (d x) e}"] validity_excess
  unfolding initial_family_def by blast
end

lemma infinite_saturation_control: "margin \<infinity> \<infinity>=0 \<and> excess \<infinity> \<infinity>=0"
  by (simp add: margin_def excess_def)

lemma no_least_open_excess_control: "\<not>(\<exists>b::real. least_in {x. 0<x} b)"
proof
  assume "\<exists>b::real. least_in {x. 0<x} b"
  then obtain b::real where hb: "least_in {x. 0<x} b" by blast
  then have bp: "0<b" unfolding least_in_def by simp
  obtain x where xp: "0<x" and xb: "x<b" using dense[OF bp] by blast
  have "b\<le>x" using hb xp unfolding least_in_def by blast
  then show False using xb by simp
qed

ML \<open>
val roots = @{thms margin_nonneg margin_zero margin_negative margin_positive excess_zero excess_positive
  nonnegative_family.validity_characterizations nonnegative_family.saturation_excess_disjoint
  nonnegative_family.valid_not_robust nonnegative_family.subset_saturation nonnegative_family.subset_excess
  maximal_initial_greatest maximal_initial_eq monotone_defects_initial least_subset initial_boundary
  maximal_effective_interval nonnegative_scale_family.first_excess
  nonnegative_scale_family.maximum_has_no_excess infinite_saturation_control no_least_open_excess_control};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
