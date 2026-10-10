theory Core_Finite_Partitions_Alignment
  imports "../support/core_finite_partitions/Core_Finite_Partitions"
begin

lemma tagged_finite:
  "finite T \<Longrightarrow> (\<And>t. t\<in>T \<Longrightarrow> finite (I t)) \<Longrightarrow>
    finite (tagged_image T I f)"
  unfolding tagged_image_def by auto
lemmas tagged_card = Core_Finite_Partitions.tagged_card
lemma tagged_partition:
  assumes nonempty: "\<And>t. t\<in>T \<Longrightarrow> I t\<noteq>{}"
  shows "(\<forall>x\<in>tagged_image T I f. \<exists>!t. t\<in>T \<and> fst x=t) \<and>
    (\<forall>t\<in>T. \<exists>x\<in>tagged_image T I f. fst x=t)"
  using nonempty unfolding tagged_image_def by (auto; blast)
lemmas classification_on_generator = Core_Finite_Partitions.classification_on_generator
lemmas classification_bijective = Core_Finite_Partitions.classification_bijective
lemmas first_failure_unique = Core_Finite_Partitions.first_failure_unique
lemmas first_failure_partition = Core_Finite_Partitions.first_failure_partition
lemma first_failure_sets:
  "{y. \<not> (\<forall>i. 1\<le>i \<and> i\<le>n \<longrightarrow> K i y)} =
    (\<Union>i::nat. {y. first n (\<lambda>j. K j y) i})"
proof -
  have bounds: "\<And>i y. first n (\<lambda>j. K j y) i \<Longrightarrow> i\<in>{1..n}"
    by (simp add: first_def)
  show ?thesis using Core_Finite_Partitions.first_failure_sets[of n K] bounds by blast
qed
lemmas first_failure_components_disjoint = Core_Finite_Partitions.first_components_disjoint
lemma bounded_extensionality:
  assumes agree: "\<And>j. 1\<le>j \<Longrightarrow> j\<le>n \<Longrightarrow> K j=L j"
  shows "first n K i=first n L i"
proof (cases "1\<le>i \<and> i\<le>n")
  case False then show ?thesis by (auto simp: first_def)
next
  case True
  have current: "K i=L i" using True by (intro agree) auto
  have prior: "\<And>j. 1\<le>j \<and> j<i \<Longrightarrow> K j=L j"
    using True by (intro agree) auto
  show ?thesis using current prior by (auto simp: first_def)
qed
lemmas empty_sequence = Core_Finite_Partitions.empty_sequence
lemmas minimum_index = Core_Finite_Partitions.minimum_index
lemmas omitted_prefix_not_unique = Core_Finite_Partitions.omitted_prefix_not_unique
lemmas injection_is_necessary = Core_Finite_Partitions.injection_is_necessary

ML \<open>
val roots = @{thms tagged_finite tagged_card tagged_partition classification_on_generator classification_bijective first_failure_unique first_failure_partition first_failure_sets first_failure_components_disjoint bounded_extensionality empty_sequence minimum_index omitted_prefix_not_unique injection_is_necessary};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
