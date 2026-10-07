theory Negative_Cases
  imports Order_Embedding_Isabelle
begin

lemma missing_kernel_equivalence_blocks_injective_factor:
  "\<not> (\<exists>iota::bool \<Rightarrow> bool.
      image iota UNIV \<subseteq> {False} \<and> inj_on iota UNIV)"
  unfolding inj_on_def by auto

definition P3 :: "nat set" where
  "P3 = {0, 1, 2}"

definition edge02 :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "edge02 x y \<longleftrightarrow> x = 0 \<and> y = 2"

lemma edge02_is_strict_partial_on_P3:
  "strict_on P3 edge02"
  unfolding strict_on_def P3_def edge02_def by auto

lemma edge02_incomparability_not_transitive:
  "\<not> inc_trans_on P3 edge02"
proof
  assume tr: "inc_trans_on P3 edge02"
  have a: "inc_on P3 edge02 0 1"
    unfolding inc_on_def P3_def edge02_def by auto
  have b: "inc_on P3 edge02 1 2"
    unfolding inc_on_def P3_def edge02_def by auto
  have c: "\<not> inc_on P3 edge02 0 2"
    unfolding inc_on_def P3_def edge02_def by auto
  have "inc_on P3 edge02 0 2"
    using tr a b unfolding inc_trans_on_def P3_def by blast
  with c show False by contradiction
qed

definition rho0 :: "nat \<Rightarrow> nat" where
  "rho0 x = 0"

lemma noninjective_map_has_no_left_inverse_on_two_points:
  "\<not> (\<exists>g::nat \<Rightarrow> nat.
      \<forall>x\<in>{0, 1}. g (rho0 x) = x)"
  unfolding rho0_def by auto

end
