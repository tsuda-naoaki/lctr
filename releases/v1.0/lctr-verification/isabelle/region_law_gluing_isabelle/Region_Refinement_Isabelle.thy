theory Region_Refinement_Isabelle
imports Main
begin

definition covered :: "'i set => ('i => 'p set) => 'p set" where
  "covered I F = (\<Union>i\<in>I. F i)"

definition unrefined :: "'p set => 'i set => ('i => 'p set) => 'p set" where
  "unrefined P I F = P - covered I F"

definition pairwise_disjoint_on :: "'i set => ('i => 'p set) => bool" where
  "pairwise_disjoint_on I F =
   (\<forall>i\<in>I. \<forall>j\<in>I. i \<noteq> j \<longrightarrow> F i \<inter> F j = {})"

definition disjoint_decomposition :: "'p set => 'p set => 'p set => bool" where
  "disjoint_decomposition P C U = (P = C \<union> U \<and> C \<inter> U = {})"

definition disjoint_family_with_remainder ::
  "'p set => 'i set => ('i => 'p set) => 'p set => bool" where
  "disjoint_family_with_remainder P I F U =
   (P = covered I F \<union> U
    \<and> pairwise_disjoint_on I F
    \<and> (\<forall>i\<in>I. F i \<inter> U = {}))"

lemma covered_subset_parent:
  assumes sub: "\<And>i. i \<in> I \<Longrightarrow> F i \<subseteq> P"
  shows "covered I F \<subseteq> P"
  using sub unfolding covered_def by auto

lemma refspl_decomposition:
  assumes sub: "\<And>i. i \<in> I \<Longrightarrow> F i \<subseteq> P"
  shows "disjoint_decomposition P (covered I F) (unrefined P I F)"
proof -
  have cov: "covered I F \<subseteq> P"
    using sub unfolding covered_def by auto
  show ?thesis
    using cov unfolding disjoint_decomposition_def unrefined_def by auto
qed

lemma conditional_indexed_disjoint_decomposition:
  assumes sub: "\<And>i. i \<in> I \<Longrightarrow> F i \<subseteq> P"
      and pw: "pairwise_disjoint_on I F"
  shows "disjoint_family_with_remainder P I F (unrefined P I F)"
proof -
  have cov: "covered I F \<subseteq> P"
    using sub unfolding covered_def by auto
  show ?thesis
    using cov pw
    unfolding disjoint_family_with_remainder_def unrefined_def
              pairwise_disjoint_on_def covered_def
    by auto
qed

lemma covered_refinement_monotone:
  assumes hi: "I0 \<subseteq> I1"
      and hs: "\<And>i. i \<in> I0 \<Longrightarrow> F0 i = F1 i"
  shows "covered I0 F0 \<subseteq> covered I1 F1"
  using hi hs unfolding covered_def by auto

lemma unrefined_refinement_antitone:
  assumes hi: "I0 \<subseteq> I1"
      and hs: "\<And>i. i \<in> I0 \<Longrightarrow> F0 i = F1 i"
  shows "unrefined P I1 F1 \<subseteq> unrefined P I0 F0"
proof -
  have cov: "covered I0 F0 \<subseteq> covered I1 F1"
    using hi hs unfolding covered_def by auto
  show ?thesis
    using cov unfolding unrefined_def by auto
qed

theorem covered_unrefined_region_refinement_monotonicity:
  assumes hi: "I0 \<subseteq> I1"
      and h0: "\<And>i. i \<in> I0 \<Longrightarrow> F0 i \<subseteq> P"
      and h1: "\<And>i. i \<in> I1 \<Longrightarrow> F1 i \<subseteq> P"
      and hs: "\<And>i. i \<in> I0 \<Longrightarrow> F0 i = F1 i"
  shows "disjoint_decomposition P (covered I0 F0) (unrefined P I0 F0)"
    and "disjoint_decomposition P (covered I1 F1) (unrefined P I1 F1)"
    and "pairwise_disjoint_on I0 F0
         \<Longrightarrow> disjoint_family_with_remainder P I0 F0 (unrefined P I0 F0)"
    and "pairwise_disjoint_on I1 F1
         \<Longrightarrow> disjoint_family_with_remainder P I1 F1 (unrefined P I1 F1)"
    and "covered I0 F0 \<subseteq> covered I1 F1"
    and "unrefined P I1 F1 \<subseteq> unrefined P I0 F0"
proof -
  show "disjoint_decomposition P (covered I0 F0) (unrefined P I0 F0)"
  proof -
    have cov0: "covered I0 F0 \<subseteq> P"
      using h0 unfolding covered_def by auto
    show ?thesis
      using cov0 unfolding disjoint_decomposition_def unrefined_def by auto
  qed
  show "disjoint_decomposition P (covered I1 F1) (unrefined P I1 F1)"
  proof -
    have cov1: "covered I1 F1 \<subseteq> P"
      using h1 unfolding covered_def by auto
    show ?thesis
      using cov1 unfolding disjoint_decomposition_def unrefined_def by auto
  qed
  show "pairwise_disjoint_on I0 F0
        \<Longrightarrow> disjoint_family_with_remainder P I0 F0 (unrefined P I0 F0)"
  proof -
    assume pw0: "pairwise_disjoint_on I0 F0"
    have cov0: "covered I0 F0 \<subseteq> P"
      using h0 unfolding covered_def by auto
    show "disjoint_family_with_remainder P I0 F0 (unrefined P I0 F0)"
      using cov0 pw0
      unfolding disjoint_family_with_remainder_def unrefined_def
                pairwise_disjoint_on_def covered_def
      by auto
  qed
  show "pairwise_disjoint_on I1 F1
        \<Longrightarrow> disjoint_family_with_remainder P I1 F1 (unrefined P I1 F1)"
  proof -
    assume pw1: "pairwise_disjoint_on I1 F1"
    have cov1: "covered I1 F1 \<subseteq> P"
      using h1 unfolding covered_def by auto
    show "disjoint_family_with_remainder P I1 F1 (unrefined P I1 F1)"
      using cov1 pw1
      unfolding disjoint_family_with_remainder_def unrefined_def
                pairwise_disjoint_on_def covered_def
      by auto
  qed
  show "covered I0 F0 \<subseteq> covered I1 F1"
    using hi hs unfolding covered_def by auto
  show "unrefined P I1 F1 \<subseteq> unrefined P I0 F0"
  proof -
    have cov: "covered I0 F0 \<subseteq> covered I1 F1"
      using hi hs unfolding covered_def by auto
    show ?thesis
      using cov unfolding unrefined_def by auto
  qed
qed

lemma empty_parent_refsplit:
  assumes sub: "\<And>i. i \<in> I \<Longrightarrow> F i \<subseteq> {}"
  shows "covered I F = {}" and "unrefined {} I F = {}"
proof -
  have cov: "covered I F = {}"
    using sub unfolding covered_def by auto
  show "covered I F = {}" using cov .
  show "unrefined {} I F = {}"
    using cov unfolding unrefined_def by simp
qed

lemma empty_index_refsplit:
  shows "covered {} F = {}" and "unrefined P {} F = P"
  unfolding covered_def unrefined_def by auto

end
