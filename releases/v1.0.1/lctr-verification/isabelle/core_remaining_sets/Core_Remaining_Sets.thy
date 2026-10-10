theory Core_Remaining_Sets
  imports Main
begin

definition arrival_image where
  "arrival_image domains arrival r i = arrival r i ` domains r i"
definition native_carrier where
  "native_carrier U domains arrival r = Sigma U (arrival_image domains arrival r)"
definition native_region where
  "native_region U domains arrival r i =
    {p\<in>native_carrier U domains arrival r. fst p=i}"

lemma native_arrival_cover:
  "(\<Union>i\<in>U. native_region U domains arrival r i) = native_carrier U domains arrival r"
  unfolding native_region_def native_carrier_def by auto
lemma native_arrival_disjoint:
  "i\<noteq>j \<Longrightarrow> native_region U domains arrival r i \<inter> native_region U domains arrival r j = {}"
  unfolding native_region_def by auto

definition covered where "covered I R = (\<Union>i\<in>I. R i)"
definition unrefined where "unrefined P S = P-S"
definition disjoint_decomposition where
  "disjoint_decomposition P C R \<longleftrightarrow> P=C\<union>R \<and> C\<inter>R={}"
definition pairwise_parts where
  "pairwise_parts I R \<longleftrightarrow> (\<forall>i\<in>I. \<forall>j\<in>I. i\<noteq>j \<longrightarrow> R i\<inter>R j={})"
definition family_with_remainder where
  "family_with_remainder I R U \<longleftrightarrow>
    pairwise_parts I R \<and> (\<forall>i\<in>I. R i\<inter>U={})"

lemma decomposition:
  assumes within: "\<And>i. i\<in>I \<Longrightarrow> R i\<subseteq>P"
  shows "disjoint_decomposition P (covered I R) (unrefined P (covered I R))"
  using within unfolding disjoint_decomposition_def covered_def unrefined_def by auto
lemma remainder_disjoint:
  "pairwise_parts I R \<Longrightarrow> family_with_remainder I R (unrefined P (covered I R))"
  unfolding family_with_remainder_def covered_def unrefined_def by auto

lemma full_refinement_contract:
  assumes idx: "I0\<subseteq>I1"
    and shared: "\<And>i. i\<in>I0 \<Longrightarrow> R0 i=R1 i"
    and within0: "\<And>i. i\<in>I0 \<Longrightarrow> R0 i\<subseteq>P"
    and within1: "\<And>i. i\<in>I1 \<Longrightarrow> R1 i\<subseteq>P"
  shows
    "disjoint_decomposition P (covered I0 R0) (unrefined P (covered I0 R0)) \<and>
     disjoint_decomposition P (covered I1 R1) (unrefined P (covered I1 R1)) \<and>
     (pairwise_parts I0 R0 \<longrightarrow> family_with_remainder I0 R0 (unrefined P (covered I0 R0))) \<and>
     (pairwise_parts I1 R1 \<longrightarrow> family_with_remainder I1 R1 (unrefined P (covered I1 R1))) \<and>
     covered I0 R0\<subseteq>covered I1 R1 \<and>
     unrefined P (covered I1 R1)\<subseteq>unrefined P (covered I0 R0)"
proof -
  have inc: "covered I0 R0\<subseteq>covered I1 R1"
    using idx shared unfolding covered_def by blast
  have rem: "unrefined P (covered I1 R1)\<subseteq>unrefined P (covered I0 R0)"
    using inc unfolding unrefined_def by blast
  have d0: "disjoint_decomposition P (covered I0 R0) (unrefined P (covered I0 R0))"
    by (rule decomposition[OF within0])
  have d1: "disjoint_decomposition P (covered I1 R1) (unrefined P (covered I1 R1))"
    by (rule decomposition[OF within1])
  have r0: "pairwise_parts I0 R0 \<longrightarrow> family_with_remainder I0 R0 (unrefined P (covered I0 R0))"
    by (rule impI, rule remainder_disjoint)
  have r1: "pairwise_parts I1 R1 \<longrightarrow> family_with_remainder I1 R1 (unrefined P (covered I1 R1))"
    by (rule impI, rule remainder_disjoint)
  show ?thesis by (intro conjI) (fact d0, fact d1, fact r0, fact r1, fact inc, fact rem)
qed

ML \<open>
val roots = @{thms native_arrival_cover native_arrival_disjoint full_refinement_contract};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
