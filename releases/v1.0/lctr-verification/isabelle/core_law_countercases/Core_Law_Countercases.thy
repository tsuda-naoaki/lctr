theory Core_Law_Countercases
  imports "LCTR_Core_Native_Law_Family.Core_Native_Law_Family"
begin

definition empty_time where "empty_time d \<longleftrightarrow> (\<exists>a\<in>law_indices d. eval_times (components d a) = {})"
definition out_eval where "out_eval d \<longleftrightarrow> (\<exists>a\<in>law_indices d. \<exists>t\<in>eval_times (components d a).
  (t,input_value (components d a) t) \<notin> eval_domain (components d a))"
definition nonunique where "nonunique d a t x \<longleftrightarrow> (\<exists>y z.
  ((t,x),y) \<in> law_relation (components d a) \<and>
  ((t,x),z) \<in> law_relation (components d a) \<and> y \<noteq> z)"
definition global_conflict where "global_conflict d \<longleftrightarrow> (\<exists>a\<in>law_indices d. \<exists>t x.
  (t,x) \<in> eval_domain (components d a) \<and> nonunique d a t x)"
definition gen_conflict where "gen_conflict d \<longleftrightarrow> (\<exists>a\<in>law_indices d. \<exists>t\<in>eval_times (components d a).
  (t,input_value (components d a) t) \<in> eval_domain (components d a) \<and>
  nonunique d a t (input_value (components d a) t))"
definition off_gen_conflict where "off_gen_conflict d \<longleftrightarrow> global_conflict d \<and> \<not> gen_conflict d"
definition missing_output where "missing_output d a t \<longleftrightarrow>
  ((t,input_value (components d a) t),output_value (components d a) t) \<notin> law_relation (components d a)"
definition fiber_nonempty where "fiber_nonempty d a t \<longleftrightarrow> (\<exists>y.
  ((t,input_value (components d a) t),y) \<in> law_relation (components d a))"
definition empty_fiber where "empty_fiber d \<longleftrightarrow> (\<exists>a\<in>law_indices d. \<exists>t\<in>eval_times (components d a).
  missing_output d a t \<and> \<not> fiber_nonempty d a t)"
definition alt_output where "alt_output d \<longleftrightarrow> (\<exists>a\<in>law_indices d. \<exists>t\<in>eval_times (components d a).
  missing_output d a t \<and> fiber_nonempty d a t)"
definition loss where "loss d \<longleftrightarrow> (\<exists>f. typed_reindex_family d f \<and> faithful_family d f \<and>
  (\<exists>a\<in>law_indices d. \<exists>z\<in>tuple_carrier d a.
    z \<in> law_relation (components d a) \<and> forward_map (f a) z \<notin> law_relation (components d a)))"
definition gain where "gain d \<longleftrightarrow> (\<exists>f. typed_reindex_family d f \<and> faithful_family d f \<and>
  (\<exists>a\<in>law_indices d. \<exists>z\<in>tuple_carrier d a.
    z \<notin> law_relation (components d a) \<and> forward_map (f a) z \<in> law_relation (components d a)))"
definition empty_common where "empty_common d \<longleftrightarrow> common_times d = {}"
definition inadmissible_common where "inadmissible_common d \<longleftrightarrow>
  common_times d \<noteq> {} \<and> \<not> admissible_common d (common_times d)"
definition pure_pair where "pure_pair p q \<longleftrightarrow> (p \<and> \<not> q) \<or> (q \<and> \<not> p)"

lemma condition1_countercases: "\<not> K1 d \<longleftrightarrow> empty_time d \<or> out_eval d"
  unfolding K1_def individual_admissible_def empty_time_def out_eval_def by blast
lemma condition2_countercase:
  assumes wf: "well_typed_family d"
  shows "\<not> K2 d \<longleftrightarrow> global_conflict d"
  using component_domain_guard[OF wf]
  unfolding K2_def right_unique_def global_conflict_def nonunique_def by blast
lemma generated_conflict_is_global: "gen_conflict d \<Longrightarrow> global_conflict d"
  unfolding gen_conflict_def global_conflict_def by blast
lemma condition2_remainder:
  "well_typed_family d \<Longrightarrow> \<not> K2 d \<Longrightarrow> (\<not> gen_conflict d \<longleftrightarrow> off_gen_conflict d)"
  using condition2_countercase unfolding off_gen_conflict_def by blast
lemma condition3_countercases:
  "K1 d \<Longrightarrow> (\<not> K3 d \<longleftrightarrow> empty_fiber d \<or> alt_output d)"
  unfolding K3_def generated_member_def empty_fiber_def alt_output_def missing_output_def by blast
lemma alternate_output_is_distinct:
  "missing_output d a t \<Longrightarrow> fiber_nonempty d a t \<Longrightarrow>
   (\<exists>y. ((t,input_value (components d a) t),y) \<in> law_relation (components d a) \<and>
    y \<noteq> output_value (components d a) t)"
  unfolding missing_output_def fiber_nonempty_def by blast

lemma carrier_image_invariance:
  assumes r: "reindex_on Z f" and sub: "P \<subseteq> Z"
  shows "forward_map f ` P = P \<longleftrightarrow> (\<forall>z\<in>Z. (forward_map f z \<in> P \<longleftrightarrow> z \<in> P))"
proof -
  have left: "\<And>z. z \<in> Z \<Longrightarrow> inverse_map f (forward_map f z) = z"
    and right: "\<And>z. z \<in> Z \<Longrightarrow> forward_map f (inverse_map f z) = z"
    and inv: "inverse_map f ` Z \<subseteq> Z"
    using r unfolding reindex_on_def by auto
  show ?thesis
  proof
    assume eq: "forward_map f ` P = P"
    show "\<forall>z\<in>Z. (forward_map f z \<in> P \<longleftrightarrow> z \<in> P)"
    proof (intro ballI iffI)
      fix z assume z: "z \<in> Z" and fz: "forward_map f z \<in> P"
      have fim: "forward_map f z \<in> forward_map f ` P" using fz by (simp only: eq)
      obtain w where w: "w \<in> P" "forward_map f w = forward_map f z" using fim by auto
      have wz: "w \<in> Z" using sub w(1) by auto
      have "w = z" using left[OF z] left[OF wz] w(2) by metis
      then show "z \<in> P" using w by simp
    next
      fix z assume "z \<in> Z" "z \<in> P"
      then show "forward_map f z \<in> P" using eq by auto
    qed
  next
    assume h: "\<forall>z\<in>Z. (forward_map f z \<in> P \<longleftrightarrow> z \<in> P)"
    show "forward_map f ` P = P"
    proof
      show "forward_map f ` P \<subseteq> P" using h sub by auto
      show "P \<subseteq> forward_map f ` P"
      proof
        fix z assume z: "z \<in> P"
        have zz: "z \<in> Z" using sub z by auto
        have iz: "inverse_map f z \<in> Z" using inv zz by auto
        have fr: "forward_map f (inverse_map f z) \<in> P" using right[OF zz] z by simp
        have ip: "inverse_map f z \<in> P" by (rule iffD1[OF bspec[OF h iz] fr])
        have "forward_map f (inverse_map f z) \<in> forward_map f ` P" by (rule imageI[OF ip])
        then show "z \<in> forward_map f ` P" by (simp only: right[OF zz])
      qed
    qed
  qed
qed

lemma K4_elementwise:
  assumes wf: "well_typed_family d"
  shows "K4 d \<longleftrightarrow> (\<forall>f. typed_reindex_family d f \<longrightarrow> faithful_family d f \<longrightarrow>
    (\<forall>a\<in>law_indices d. \<forall>z\<in>tuple_carrier d a.
      (forward_map (f a) z \<in> law_relation (components d a) \<longleftrightarrow> z \<in> law_relation (components d a))))"
proof -
  have local_eq: "image_invariant (components d a) (f a) \<longleftrightarrow>
      (\<forall>z\<in>tuple_carrier d a. (forward_map (f a) z \<in> law_relation (components d a)
        \<longleftrightarrow> z \<in> law_relation (components d a)))"
    if tf: "typed_reindex_family d f" and a: "a \<in> law_indices d" for f a
  proof -
    have r: "reindex_on (tuple_carrier d a) (f a)"
      using tf a unfolding typed_reindex_family_def by auto
    show ?thesis unfolding image_invariant_def
      by (rule carrier_image_invariance[OF r relation_subset_tuple[OF wf a]])
  qed
  show ?thesis unfolding K4_def using local_eq by blast
qed
lemma condition4_countercases:
  "well_typed_family d \<Longrightarrow> (\<not> K4 d \<longleftrightarrow> loss d \<or> gain d)"
  unfolding loss_def gain_def using K4_elementwise[of d] by blast
lemma condition5_countercases:
  "K3 d \<Longrightarrow> (\<not> K5 d \<longleftrightarrow> empty_common d \<or> inadmissible_common d)"
  by (auto simp: K5_def empty_common_def inadmissible_common_def)
lemma condition5_cases_exclusive: "\<not> (empty_common d \<and> inadmissible_common d)"
  by (simp add: empty_common_def inadmissible_common_def)
lemma pair_remainder: "p \<or> q \<Longrightarrow> (\<not> pure_pair p q \<longleftrightarrow> p \<and> q)"
  by (auto simp: pure_pair_def)
lemma condition135_remainders:
  "(\<not> K1 d \<longrightarrow> (\<not> pure_pair (empty_time d) (out_eval d) \<longleftrightarrow> empty_time d \<and> out_eval d)) \<and>
   (K1 d \<longrightarrow> \<not> K3 d \<longrightarrow> (\<not> pure_pair (empty_fiber d) (alt_output d) \<longleftrightarrow> empty_fiber d \<and> alt_output d)) \<and>
   (K3 d \<longrightarrow> \<not> K5 d \<longrightarrow> pure_pair (empty_common d) (inadmissible_common d))"
  using condition1_countercases[of d] condition3_countercases[of d]
    condition5_countercases[of d] condition5_cases_exclusive[of d]
  unfolding pure_pair_def by blast
lemma condition4_remainder:
  "well_typed_family d \<Longrightarrow> \<not> K4 d \<Longrightarrow> (\<not> pure_pair (loss d) (gain d) \<longleftrightarrow> loss d \<and> gain d)"
  using condition4_countercases[of d] pair_remainder[of "loss d" "gain d"] by blast

ML \<open>
val roots = @{thms condition1_countercases condition2_countercase generated_conflict_is_global
  condition2_remainder condition3_countercases alternate_output_is_distinct condition4_countercases
  condition5_countercases condition5_cases_exclusive pair_remainder condition135_remainders condition4_remainder};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int (length roots));
\<close>
end
