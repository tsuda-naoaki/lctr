theory Core_Native_Law_Family
  imports "LCTR_Core_Law_Failure.Core_Law_Failure"
begin

record ('t, 'x, 'y) law_component =
  eval_times :: "'t set"
  input_value :: "'t \<Rightarrow> 'x"
  output_value :: "'t \<Rightarrow> 'y"
  eval_domain :: "('t \<times> 'x) set"
  law_relation :: "(('t \<times> 'x) \<times> 'y) set"

record 'z carrier_reindex =
  forward_map :: "'z \<Rightarrow> 'z"
  inverse_map :: "'z \<Rightarrow> 'z"

definition reindex_on where
  "reindex_on Z f \<longleftrightarrow>
    forward_map f ` Z \<subseteq> Z \<and> inverse_map f ` Z \<subseteq> Z \<and>
    (\<forall>z\<in>Z. inverse_map f (forward_map f z) = z) \<and>
    (\<forall>z\<in>Z. forward_map f (inverse_map f z) = z)"

record ('t, 'a, 'x, 'y) law_family =
  time_carrier :: "'t set"
  law_indices :: "'a set"
  input_carrier :: "'a \<Rightarrow> 'x set"
  output_carrier :: "'a \<Rightarrow> 'y set"
  components :: "'a \<Rightarrow> ('t, 'x, 'y) law_component"
  admissible_common :: "'t set \<Rightarrow> bool"
  faithful_family :: "('a \<Rightarrow> (('t \<times> 'x) \<times> 'y) carrier_reindex) \<Rightarrow> bool"

definition tuple_carrier where
  "tuple_carrier d a = (time_carrier d \<times> input_carrier d a) \<times> output_carrier d a"
definition typed_reindex_family where
  "typed_reindex_family d f \<longleftrightarrow>
    (\<forall>a\<in>law_indices d. reindex_on (tuple_carrier d a) (f a))"
definition same_reindex_family where
  "same_reindex_family d f g \<longleftrightarrow>
    (\<forall>a\<in>law_indices d. \<forall>z\<in>tuple_carrier d a.
      forward_map (f a) z = forward_map (g a) z \<and>
      inverse_map (f a) z = inverse_map (g a) z)"
definition well_typed_family where
  "well_typed_family d \<longleftrightarrow> law_indices d \<noteq> {} \<and>
    (\<forall>a\<in>law_indices d.
      eval_times (components d a) \<subseteq> time_carrier d \<and>
      input_value (components d a) ` eval_times (components d a) \<subseteq> input_carrier d a \<and>
      output_value (components d a) ` eval_times (components d a) \<subseteq> output_carrier d a \<and>
      eval_domain (components d a) \<subseteq> time_carrier d \<times> input_carrier d a \<and>
      law_relation (components d a) \<subseteq> eval_domain (components d a) \<times> output_carrier d a) \<and>
    (\<forall>f g. typed_reindex_family d f \<longrightarrow> typed_reindex_family d g \<longrightarrow>
      same_reindex_family d f g \<longrightarrow> (faithful_family d f \<longleftrightarrow> faithful_family d g))"

definition individual_admissible where
  "individual_admissible c \<longleftrightarrow> eval_times c \<noteq> {} \<and>
    (\<forall>t\<in>eval_times c. (t, input_value c t) \<in> eval_domain c)"
definition right_unique where
  "right_unique c \<longleftrightarrow> (\<forall>t x y z.
    ((t,x),y) \<in> law_relation c \<longrightarrow> ((t,x),z) \<in> law_relation c \<longrightarrow> y = z)"
definition generated_member where
  "generated_member c \<longleftrightarrow> (\<forall>t\<in>eval_times c.
    ((t,input_value c t),output_value c t) \<in> law_relation c)"
definition valid_times where
  "valid_times c = {t\<in>eval_times c. ((t,input_value c t),output_value c t) \<in> law_relation c}"
definition common_times where
  "common_times d = {t\<in>time_carrier d. \<forall>a\<in>law_indices d. t \<in> valid_times (components d a)}"
definition image_invariant where
  "image_invariant c f \<longleftrightarrow> forward_map f ` law_relation c = law_relation c"

definition K1 where "K1 d \<longleftrightarrow> (\<forall>a\<in>law_indices d. individual_admissible (components d a))"
definition K2 where "K2 d \<longleftrightarrow> (\<forall>a\<in>law_indices d. right_unique (components d a))"
definition K3 where "K3 d \<longleftrightarrow> K1 d \<and> (\<forall>a\<in>law_indices d. generated_member (components d a))"
definition K4 where "K4 d \<longleftrightarrow> (\<forall>f. typed_reindex_family d f \<longrightarrow> faithful_family d f \<longrightarrow>
  (\<forall>a\<in>law_indices d. image_invariant (components d a) (f a)))"
definition K5 where "K5 d \<longleftrightarrow> K3 d \<and> common_times d \<noteq> {} \<and> admissible_common d (common_times d)"
definition all_conditions where "all_conditions d \<longleftrightarrow> K1 d \<and> K2 d \<and> K3 d \<and> K4 d \<and> K5 d"

fun condition where
  "condition d Law1 = K1 d" | "condition d Law2 = K2 d" |
  "condition d Law3 = K3 d" | "condition d Law4 = K4 d" | "condition d Law5 = K5 d"

lemma roots_exact: "(\<not> (\<exists>i. edge i j)) \<longleftrightarrow> j = Law1 \<or> j = Law2 \<or> j = Law4"
  by (cases j) (auto simp: edge_def)
lemma ancestor_sets:
  "(\<forall>i. \<not> ancestor i Law1 \<and> \<not> ancestor i Law2 \<and> \<not> ancestor i Law4) \<and>
   (\<forall>i. ancestor i Law3 \<longleftrightarrow> i = Law1) \<and>
   (\<forall>i. ancestor i Law5 \<longleftrightarrow> i = Law1 \<or> i = Law3)"
  by (auto simp: ancestor_def edge_def)
lemma condition_vector_exact:
  "condition d Law1 = K1 d \<and> condition d Law2 = K2 d \<and>
   condition d Law3 = K3 d \<and> condition d Law4 = K4 d \<and> condition d Law5 = K5 d"
  by simp
lemma all_conditions_exact: "(\<forall>i. condition d i) \<longleftrightarrow> all_conditions d"
  by (simp add: forall_nodes all_conditions_def)
lemma condition_dependency: "edge i j \<Longrightarrow> condition d j \<Longrightarrow> condition d i"
  by (auto simp: edge_def K3_def K5_def)
lemma ancestor_conditions_hold: "tranclp edge i j \<Longrightarrow> condition d j \<Longrightarrow> condition d i"
  by (induction rule: tranclp_induct) (auto intro: condition_dependency)

lemma component_domain_guard:
  "well_typed_family d \<Longrightarrow> a \<in> law_indices d \<Longrightarrow>
   ((t,x),y) \<in> law_relation (components d a) \<Longrightarrow>
   (t,x) \<in> eval_domain (components d a)"
  unfolding well_typed_family_def by auto
lemma common_time_guard:
  "t \<in> common_times d \<Longrightarrow> t \<in> time_carrier d"
  by (simp add: common_times_def)

lemma common_times_as_intersection:
  assumes wf: "well_typed_family d"
  shows "common_times d = (\<Inter>a\<in>law_indices d. valid_times (components d a))"
proof -
  have ne: "law_indices d \<noteq> {}"
    using wf unfolding well_typed_family_def by auto
  obtain a where a: "a \<in> law_indices d"
    using ne by auto
  have sub: "eval_times (components d a) \<subseteq> time_carrier d"
    using wf a unfolding well_typed_family_def by auto
  show ?thesis using a sub unfolding common_times_def valid_times_def by auto
qed

lemma relation_subset_tuple:
  "well_typed_family d \<Longrightarrow> a \<in> law_indices d \<Longrightarrow>
   law_relation (components d a) \<subseteq> tuple_carrier d a"
  unfolding well_typed_family_def tuple_carrier_def by auto

lemma reindex_extension_irrelevant:
  assumes wf: "well_typed_family d" and a: "a \<in> law_indices d"
    and same: "same_reindex_family d f g"
  shows "image_invariant (components d a) (f a) = image_invariant (components d a) (g a)"
proof -
  have eq: "forward_map (f a) z = forward_map (g a) z"
    if "z \<in> law_relation (components d a)" for z
    using same a relation_subset_tuple[OF wf a] that
    unfolding same_reindex_family_def by blast
  have "forward_map (f a) ` law_relation (components d a) =
        forward_map (g a) ` law_relation (components d a)"
    using eq by auto
  then show ?thesis unfolding image_invariant_def by simp
qed

ML \<open>
val roots = @{thms edge_rank ancestors_exact graph_acyclic roots_exact ancestor_sets
  condition_vector_exact all_conditions_exact condition_dependency ancestor_conditions_hold};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int (length roots));
\<close>
end
