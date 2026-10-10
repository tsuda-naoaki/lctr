theory Core_Native_Differential_Predicates
  imports "LCTR_Core_Native_Joint_Jets.Core_Native_Joint_Jets"
begin

definition total_curve where "total_curve N q = (\<lambda>t. if t\<in>N then q t else 0)"
definition native_diff2 where
  "native_diff2 N q k \<longleftrightarrow> open N \<and> higher_differentiable_on N (total_curve N q) k"
definition canonical_pair where
  "canonical_pair N q k theta = (theta,jet k theta (total_curve N q))"
definition native_diff3 where
  "native_diff3 N q k Rel \<longleftrightarrow> native_diff2 N q k \<and>
    (\<forall>theta\<in>N. canonical_pair N q k theta\<in>Rel)"

lemma total_curve_on_domain: "theta\<in>N \<Longrightarrow> total_curve N q theta=q theta"
  by (simp add: total_curve_def)
lemma diff2_exact:
  "native_diff2 N q k \<longleftrightarrow> open N \<and> higher_differentiable_on N (total_curve N q) k"
  by (simp add: native_diff2_def)

lemma curve_ck_germ:
  assumes f: "curve_ck_at k a f" and eq: "eventually (\<lambda>x. g x=f x) (nhds a)"
  shows "curve_ck_at k a g"
proof -
  obtain S where S: "open S" "a\<in>S" "higher_differentiable_on S f k"
    using f unfolding curve_ck_at_def by blast
  obtain T where T: "open T" "a\<in>T" "\<forall>x\<in>T. g x=f x"
    using eq unfolding eventually_nhds by blast
  have O: "open (S\<inter>T)" using S T by auto
  have F: "higher_differentiable_on (S\<inter>T) f k"
    by (rule higher_differentiable_on_subset[OF S(3)]) auto
  have G: "higher_differentiable_on (S\<inter>T) g k"
    by (rule higher_differentiable_on_congI[OF O F]) (use T(3) in auto)
  show ?thesis using O G S(2) T(2) unfolding curve_ck_at_def by blast
qed

lemma curve_ck_everywhere_on:
  assumes all: "\<And>x. x\<in>N \<Longrightarrow> curve_ck_at k x f"
  shows "higher_differentiable_on N f k"
  by (rule higher_differentiable_on_open_subsetsI) (use all in \<open>auto simp: curve_ck_at_def\<close>)

lemma certified_data:
  fixes q :: "real\<Rightarrow>'a::real_normed_vector\<times>'b::real_normed_vector"
  assumes h: "native_diff2 N q k"
  shows "atlas_jet_data N (fst \<circ> q) k (fst \<circ> total_curve N q)"
    and "atlas_jet_data N (snd \<circ> q) k (snd \<circ> total_curve N q)"
proof -
  have O: "open N" and H: "higher_differentiable_on N (total_curve N q) k"
    using h by (auto simp: native_diff2_def)
  have I: "higher_differentiable_on N (fst \<circ> total_curve N q) k"
    using higher_differentiable_on_fst_comp[OF H O] by (simp add: comp_def)
  have V: "higher_differentiable_on N (snd \<circ> total_curve N q) k"
    using higher_differentiable_on_snd_comp[OF H O] by (simp add: comp_def)
  show "atlas_jet_data N (fst \<circ> q) k (fst \<circ> total_curve N q)"
    unfolding atlas_jet_data_def
    using curve_ck_on_at[OF O _ I] by (auto simp: total_curve_def)
  show "atlas_jet_data N (snd \<circ> q) k (snd \<circ> total_curve N q)"
    unfolding atlas_jet_data_def
    using curve_ck_on_at[OF O _ V] by (auto simp: total_curve_def)
qed

lemma diff2_iff_smooth_realizations:
  fixes q :: "real\<Rightarrow>'a::real_normed_vector\<times>'b::real_normed_vector"
  shows "native_diff2 N q k \<longleftrightarrow> open N \<and>
    (\<exists>di do. atlas_jet_data N (fst \<circ> q) k di \<and> atlas_jet_data N (snd \<circ> q) k do)"
proof
  assume h: "native_diff2 N q k"
  show "open N \<and> (\<exists>di do. atlas_jet_data N (fst \<circ> q) k di \<and> atlas_jet_data N (snd \<circ> q) k do)"
    using h certified_data[OF h] by (auto simp: native_diff2_def)
next
  assume h: "open N \<and> (\<exists>di do. atlas_jet_data N (fst \<circ> q) k di \<and> atlas_jet_data N (snd \<circ> q) k do)"
  obtain di do where d: "atlas_jet_data N (fst \<circ> q) k di" "atlas_jet_data N (snd \<circ> q) k do"
    using h by blast
  have O: "open N" using h by simp
  have ck: "curve_ck_at k theta (total_curve N q)" if theta: "theta\<in>N" for theta
  proof -
    have I: "curve_ck_at k theta di" and V: "curve_ck_at k theta do"
      using d theta by (auto simp: atlas_jet_data_def)
    have J: "curve_ck_at k theta (joint_extension di do)"
      using curve_ck_pair[OF I V] by (simp add: joint_extension_def)
    have ev: "eventually (\<lambda>z. z\<in>N) (nhds theta)"
      by (rule eventually_nhds_in_open[OF O theta])
    have eq: "eventually (\<lambda>z. total_curve N q z=joint_extension di do z) (nhds theta)"
      using ev by eventually_elim (use d in \<open>auto simp: atlas_jet_data_def joint_extension_def total_curve_def\<close>)
    show ?thesis by (rule curve_ck_germ[OF J eq])
  qed
  show "native_diff2 N q k" using O curve_ck_everywhere_on[OF ck] by (simp add: native_diff2_def)
qed

lemma canonical_pair_from_any_realization:
  assumes h: "native_diff2 N q k" and theta: "theta\<in>N"
    and di: "atlas_jet_data N (fst \<circ> q) k di"
    and do: "atlas_jet_data N (snd \<circ> q) k do"
  shows "canonical_pair N q k theta = joint_generated_pair k di do theta"
proof -
  have O: "open N" using h by (simp add: native_diff2_def)
  have ev: "eventually (\<lambda>z. z\<in>N) (nhds theta)"
    by (rule eventually_nhds_in_open[OF O theta])
  have eq: "eventually (\<lambda>z. total_curve N q z=joint_extension di do z) (nhds theta)"
    using ev by eventually_elim (use di do in \<open>auto simp: atlas_jet_data_def joint_extension_def total_curve_def\<close>)
  show ?thesis using jet_germ[OF eq] by (simp add: canonical_pair_def joint_generated_pair_def joint_jet_def)
qed

lemma diff3_requires_diff2: "native_diff3 N q k Rel \<Longrightarrow> native_diff2 N q k"
  by (simp add: native_diff3_def)
lemma diff3_restricts:
  "native_diff2 N q k \<Longrightarrow> native_diff3 N q k Rel \<longleftrightarrow> (\<forall>theta\<in>N. canonical_pair N q k theta\<in>Rel)"
  by (simp add: native_diff3_def)
lemma diff3_realization_independent:
  assumes h: "native_diff2 N q k"
    and di: "atlas_jet_data N (fst \<circ> q) k di" and do: "atlas_jet_data N (snd \<circ> q) k do"
  shows "native_diff3 N q k Rel \<longleftrightarrow> (\<forall>theta\<in>N. joint_generated_pair k di do theta\<in>Rel)"
  using canonical_pair_from_any_realization[OF h _ di do]
  by (simp add: diff3_restricts[OF h])
lemma diff3_false_outside: "\<not>native_diff2 N q k \<Longrightarrow> \<not>native_diff3 N q k Rel"
  by (simp add: native_diff3_def)

context real_transported_atlas
begin
lemma transported_total_curve:
  assumes i: "i\<in>Charts"
  shows "total_curve (pushed.numeric i) (pushed.curve i) = total_curve (original.numeric i) (original.curve i)"
  using curve_at_transported_coordinate[OF i] numeric_domain_preserved[OF i]
  by (auto simp: fun_eq_iff total_curve_def source_theta_def)
lemma diff2_transport:
  assumes i: "i\<in>Charts"
  shows "native_diff2 (pushed.numeric i) (pushed.curve i) k \<longleftrightarrow>
    native_diff2 (original.numeric i) (original.curve i) k"
  unfolding native_diff2_def
  apply (subst transported_total_curve[OF i])
  by (simp add: numeric_domain_preserved[OF i])
lemma canonical_pair_transport:
  "i\<in>Charts \<Longrightarrow> canonical_pair (pushed.numeric i) (pushed.curve i) k theta =
    canonical_pair (original.numeric i) (original.curve i) k (source_theta theta)"
  by (simp add: canonical_pair_def transported_total_curve source_theta_def)
lemma diff3_transport:
  assumes i: "i\<in>Charts"
  shows "native_diff3 (pushed.numeric i) (pushed.curve i) k Rel \<longleftrightarrow>
    native_diff3 (original.numeric i) (original.curve i) k Rel"
  unfolding native_diff3_def
  apply (simp only: diff2_transport[OF i] canonical_pair_transport[OF i] source_theta_def)
  by (simp only: numeric_domain_preserved[OF i])
end

ML \<open>
val roots = @{thms total_curve_on_domain diff2_exact diff2_iff_smooth_realizations
  canonical_pair_from_any_realization diff3_requires_diff2 diff3_restricts diff3_realization_independent
  diff3_false_outside real_transported_atlas.transported_total_curve real_transported_atlas.diff2_transport
  real_transported_atlas.canonical_pair_transport real_transported_atlas.diff3_transport};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
