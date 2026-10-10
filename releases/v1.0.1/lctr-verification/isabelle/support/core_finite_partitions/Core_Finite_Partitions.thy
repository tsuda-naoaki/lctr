theory Core_Finite_Partitions
  imports Main
begin

definition tagged_image where "tagged_image T I f = Sigma T (\<lambda>t. f t ` I t)"
definition component where "component T I f t = {(s,x)\<in>tagged_image T I f. s=t}"
definition encoding where "encoding f p = (fst p, f (fst p) (snd p))"

lemma tagged_encoding_bijective:
  assumes inj: "\<And>t. t\<in>T \<Longrightarrow> inj_on (f t) (I t)"
  shows "bij_betw (encoding f) (Sigma T I) (tagged_image T I f)"
  using inj unfolding bij_betw_def inj_on_def tagged_image_def encoding_def by (auto; force)

theorem tagged_card:
  assumes "finite T" "\<And>t. t\<in>T \<Longrightarrow> finite (I t)"
    "\<And>t. t\<in>T \<Longrightarrow> inj_on (f t) (I t)"
  shows "card (tagged_image T I f) = (\<Sum>t\<in>T. card (I t))"
  unfolding tagged_image_def using assms by (simp add: card_image)

theorem tagged_partition:
  assumes ft: "finite T" and fi: "\<And>t. t\<in>T \<Longrightarrow> finite (I t)"
    and ni: "\<And>t. t\<in>T \<Longrightarrow> I t\<noteq>{}"
  shows "finite (tagged_image T I f)"
    and "\<Union>(component T I f ` T) = tagged_image T I f"
    and "\<And>t. t\<in>T \<Longrightarrow> component T I f t\<noteq>{}"
    and "\<And>s t. s\<noteq>t \<Longrightarrow> component T I f s \<inter> component T I f t = {}"
  using assms unfolding tagged_image_def component_def by auto

definition classified where
  "classified P p = (fst p, snd p, P (fst p) (snd p))"

lemma classification_of_indices:
  "bij_betw (classified P) (Sigma T I) {(t,i,P t i) |t i. t\<in>T \<and> i\<in>I t}"
  unfolding bij_betw_def inj_on_def classified_def by (auto; force)

definition classify_image where
  "classify_image T I f P = classified P \<circ> inv_into (Sigma T I) (encoding f)"

theorem classification_bijective:
  assumes inj: "\<And>t. t\<in>T \<Longrightarrow> inj_on (f t) (I t)"
  shows "bij_betw (classify_image T I f P) (tagged_image T I f)
    {(t,i,P t i) |t i. t\<in>T \<and> i\<in>I t}"
  unfolding classify_image_def
  by (rule bij_betw_trans[OF bij_betw_inv_into[OF tagged_encoding_bijective[OF inj]] classification_of_indices])

theorem classification_on_generator:
  assumes inj: "\<And>t. t\<in>T \<Longrightarrow> inj_on (f t) (I t)" and t: "t\<in>T" and i: "i\<in>I t"
  shows "classify_image T I f P (t,f t i) = (t,i,P t i)"
proof -
  have bij: "bij_betw (encoding f) (Sigma T I) (tagged_image T I f)"
    by (rule tagged_encoding_bijective[OF inj])
  have inv: "inv_into (Sigma T I) (encoding f) (encoding f (t,i)) = (t,i)"
    by (rule bij_betw_inv_into_left[OF bij]) (use t i in auto)
  show ?thesis using inv by (simp add: classify_image_def encoding_def classified_def)
qed

definition first :: "nat \<Rightarrow> (nat\<Rightarrow>bool) \<Rightarrow> nat \<Rightarrow> bool" where
  "first n K i = (1\<le>i \<and> i\<le>n \<and> \<not>K i \<and> (\<forall>j. 1\<le>j \<and> j<i \<longrightarrow> K j))"

lemma first_components_disjoint:
  assumes "first n K i" "first n K j"
  shows "i=j"
  using assms unfolding first_def by (metis less_linear)

theorem first_failure_unique:
  assumes failed: "\<not> (\<forall>i. 1\<le>i \<and> i\<le>n \<longrightarrow> K i)"
  shows "\<exists>!i. first n K i"
proof -
  let ?P = "\<lambda>i. 1\<le>i \<and> i\<le>n \<and> \<not>K i"
  have ex: "\<exists>i. ?P i" using failed by auto
  let ?i = "LEAST i. ?P i"
  have pi: "?P ?i" by (rule LeastI_ex[OF ex])
  have prior: "\<forall>j. 1\<le>j \<and> j<?i \<longrightarrow> K j"
  proof (intro allI impI)
    fix j
    assume bounds: "1\<le>j \<and> j<?i"
    show "K j"
    proof (rule ccontr)
      assume "\<not>K j"
      then have pj: "?P j" using bounds pi by auto
      have "?i\<le>j" by (rule Least_le[where P="?P" and k=j, OF pj])
      then show False using bounds by simp
    qed
  qed
  have f: "first n K ?i" using pi prior unfolding first_def by blast
  show ?thesis
  proof (rule ex1I[where P="first n K" and a="?i", OF f])
    fix j
    assume fj: "first n K j"
    show "j=?i" by (rule first_components_disjoint[OF fj f])
  qed
qed

theorem first_failure_partition:
  "(\<not> (\<forall>i. 1\<le>i \<and> i\<le>n \<longrightarrow> K i)) = (\<exists>!i. first n K i)"
proof
  assume h: "\<not> (\<forall>i. 1\<le>i \<and> i\<le>n \<longrightarrow> K i)"
  show "\<exists>!i. first n K i" by (rule first_failure_unique[OF h])
next
  assume "\<exists>!i. first n K i"
  then obtain i where "first n K i" by auto
  then show "\<not> (\<forall>i. 1\<le>i \<and> i\<le>n \<longrightarrow> K i)" by (auto simp: first_def)
qed

theorem first_failure_sets:
  "{y. \<not> (\<forall>i. 1\<le>i \<and> i\<le>n \<longrightarrow> K i y)} =
    (\<Union>i\<in>{1..n}. {y. first n (\<lambda>j. K j y) i})"
proof (rule set_eqI)
  fix y
  have eq: "(\<not> (\<forall>i. 1\<le>i \<and> i\<le>n \<longrightarrow> K i y)) = (\<exists>!i. first n (\<lambda>j. K j y) i)"
    by (rule first_failure_partition)
  show "(y\<in>{y. \<not> (\<forall>i. 1\<le>i \<and> i\<le>n \<longrightarrow> K i y)}) =
    (y\<in>(\<Union>i\<in>{1..n}. {y. first n (\<lambda>j. K j y) i}))"
    using eq first_components_disjoint[of n "\<lambda>j. K j y"]
    by (auto simp: first_def)
qed

lemma empty_sequence: "\<not> (\<exists>i. first 0 K i)" by (simp add: first_def)
lemma minimum_index:
  "first n K i \<Longrightarrow> 1\<le>j \<Longrightarrow> j\<le>n \<Longrightarrow> \<not>K j \<Longrightarrow> i\<le>j"
  unfolding first_def by (metis not_less)

lemma omitted_prefix_not_unique:
  "\<exists>i j::nat. i\<noteq>j \<and> (1\<le>i \<and> i\<le>2 \<and> \<not>False) \<and> (1\<le>j \<and> j\<le>2 \<and> \<not>False)"
  by (rule exI[of _ 1], rule exI[of _ 2]) simp

lemma injection_is_necessary: "\<not>(\<exists>g::unit\<Rightarrow>bool. \<forall>b. g ()=b)" by auto

ML \<open>
val roots = @{thms tagged_encoding_bijective tagged_card tagged_partition classification_bijective
  classification_on_generator first_failure_unique first_failure_partition first_failure_sets
  first_components_disjoint empty_sequence minimum_index omitted_prefix_not_unique injection_is_necessary};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
