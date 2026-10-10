theory Core_Nonmonotone_Boundary_Data
  imports "HOL-Library.Extended_Nonnegative_Real"
begin

definition envelope :: "'a::preorder set\<Rightarrow>('a\<Rightarrow>ennreal)\<Rightarrow>'a\<Rightarrow>ennreal" where
  "envelope D f x = Sup (f ` {y. y\<in>D \<and> y\<le>x})"
lemma envelope_member_bound:
  "y\<in>D \<Longrightarrow> y\<le>x \<Longrightarrow> f y\<le>envelope D f x"
  unfolding envelope_def by (rule Sup_upper) auto
lemma envelope_dominates: "x\<in>D \<Longrightarrow> f x\<le>envelope D f x"
  by (rule envelope_member_bound) simp_all
lemma envelope_monotone:
  "\<forall>x y. x\<le>y \<longrightarrow> envelope (D::'a::preorder set) f x\<le>envelope D f y"
proof (intro allI impI)
  fix x y :: 'a assume h: "x\<le>y"
  have "f ` {z. z\<in>D \<and> z\<le>x} \<subseteq> f ` {z. z\<in>D \<and> z\<le>y}"
    using h by (auto intro: order_trans)
  then show "envelope D f x\<le>envelope D f y"
    unfolding envelope_def by (rule Sup_subset_mono)
qed
lemma envelope_least:
  "(\<And>y. y\<in>D \<Longrightarrow> y\<le>x \<Longrightarrow> f y\<le>b) \<Longrightarrow> envelope D f x\<le>b"
  unfolding envelope_def by (rule Sup_least) auto
definition finite_envelope where "finite_envelope D f = (\<forall>x\<in>D. envelope D f x<top)"
lemma finite_envelope_exact:
  "finite_envelope D f = (\<forall>x\<in>D. envelope D f x<top)"
  by (simp add: finite_envelope_def)
lemma finite_envelope_defects_finite:
  assumes h: "finite_envelope D f" and x: "x\<in>D"
  shows "f x<top"
proof -
  have "envelope D f x<top" using h x unfolding finite_envelope_def by blast
  with envelope_dominates[OF x] show ?thesis by (rule le_less_trans)
qed
lemma infinite_defect_no_finite_envelope:
  "x\<in>D \<Longrightarrow> f x=top \<Longrightarrow> \<not>finite_envelope D f"
  using finite_envelope_defects_finite by fastforce

record ('k,'a) partition_data =
  active_indices :: "'k set"
  region :: "'k\<Rightarrow>'a set"
definition partition_typed :: "'a::preorder set\<Rightarrow>('a\<Rightarrow>ennreal)\<Rightarrow>('k,'a) partition_data\<Rightarrow>bool" where
  "partition_typed D f p = (finite (active_indices p) \<and>
    (\<forall>x. x\<in>D = (\<exists>k\<in>active_indices p. x\<in>region p k)) \<and>
    (\<forall>i\<in>active_indices p. \<forall>j\<in>active_indices p. i\<noteq>j \<longrightarrow> region p i\<inter>region p j={}) \<and>
    (\<forall>k\<in>active_indices p. \<forall>a\<in>region p k. \<forall>c\<in>region p k. \<forall>b.
      a\<le>b \<longrightarrow> b\<le>c \<longrightarrow> b\<in>region p k) \<and>
    (\<forall>k\<in>active_indices p. \<forall>a\<in>region p k. \<forall>b\<in>region p k.
      a\<le>b \<longrightarrow> f a\<le>f b))"
lemma partition_cover:
  "partition_typed D f p \<Longrightarrow> finite (active_indices p) \<and>
    (\<forall>x. x\<in>D = (\<exists>k\<in>active_indices p. x\<in>region p k))"
  by (simp add: partition_typed_def)
lemma partition_unique:
  assumes p: "partition_typed D f p" and x: "x\<in>D"
  shows "\<exists>!k. k\<in>active_indices p \<and> x\<in>region p k"
proof -
  obtain k where k: "k\<in>active_indices p" "x\<in>region p k"
    using partition_cover[OF p] x by blast
  have disjoint: "\<forall>i\<in>active_indices p. \<forall>j\<in>active_indices p.
    i\<noteq>j \<longrightarrow> region p i\<inter>region p j={}"
    using p unfolding partition_typed_def by simp
  have unique: "j=k" if j: "j\<in>active_indices p" "x\<in>region p j" for j
  proof (rule ccontr)
    assume "j\<noteq>k"
    then have "region p j\<inter>region p k={}"
      using disjoint k(1) j(1) by blast
    with j(2) k(2) show False by blast
  qed
  show ?thesis using k unique by blast
qed
lemma partition_order_convex:
  "partition_typed D f p \<Longrightarrow> k\<in>active_indices p \<Longrightarrow>
    a\<in>region p k \<Longrightarrow> c\<in>region p k \<Longrightarrow> a\<le>b \<Longrightarrow> b\<le>c \<Longrightarrow> b\<in>region p k"
  unfolding partition_typed_def by blast
lemma partition_monotone:
  "partition_typed D f p \<Longrightarrow> k\<in>active_indices p \<Longrightarrow>
    a\<in>region p k \<Longrightarrow> b\<in>region p k \<Longrightarrow> a\<le>b \<Longrightarrow> f a\<le>f b"
  unfolding partition_typed_def by blast

datatype method = EnvelopeMethod | PartitionMethod | UnformedMethod
fun stated_permission where
  "stated_permission e p EnvelopeMethod=e"
| "stated_permission e p PartitionMethod=p"
| "stated_permission e p UnformedMethod=(\<not>e \<and> \<not>p)"
lemma envelope_method_permission: "e \<Longrightarrow> stated_permission e p EnvelopeMethod" by simp
lemma partition_method_permission: "p \<Longrightarrow> stated_permission e p PartitionMethod" by simp
lemma unformed_when_neither:
  "\<not>e \<Longrightarrow> \<not>p \<Longrightarrow> stated_permission e p m = (m=UnformedMethod)"
  by (cases m) simp_all
lemma no_priority_when_both:
  "e \<Longrightarrow> p \<Longrightarrow> stated_permission e p EnvelopeMethod \<and> stated_permission e p PartitionMethod"
  by simp

ML \<open>
val roots = @{thms envelope_member_bound envelope_dominates envelope_monotone envelope_least
  finite_envelope_exact finite_envelope_defects_finite infinite_defect_no_finite_envelope
  partition_cover partition_unique partition_order_convex partition_monotone
  envelope_method_permission partition_method_permission unformed_when_neither no_priority_when_both};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
