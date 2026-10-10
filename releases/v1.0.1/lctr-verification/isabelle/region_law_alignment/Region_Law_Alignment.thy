theory Region_Law_Alignment
  imports "LCTR_Region_Law_Gluing_Isabelle.LawEvalDatSp_Adapter_Isabelle"
          "LCTR_Region_Law_Gluing_Isabelle.Abstract_Gluing_Isabelle"
begin

definition typed_pointwise_graph where
  "typed_pointwise_graph E Y R f \<longleftrightarrow>
    maps_dom_into (cand_rel_dom E Y R) Y f \<and>
    (\<forall>x\<in>cand_rel_dom E Y R. \<forall>y\<in>Y. (x,y)\<in>R \<longleftrightarrow> y=f x)"

locale actual_law_component =
  fixes E :: "('time\<times>'in) set" and Y :: "'out set" and R :: "(('time\<times>'in)\<times>'out) set"
  assumes typed_relation: "R\<subseteq>E\<times>Y"
begin

lemma alignment_evalPoint_is_in_actual_evalDom: "x\<in>E \<Longrightarrow> x\<in>E" by assumption
lemma alignment_candRelDom_is_exact_relation_domain:
  "x\<in>E \<Longrightarrow> (\<exists>y\<in>Y. (x,y)\<in>R) \<longleftrightarrow> (\<exists>dx\<in>cand_rel_dom E Y R. dx=x)"
  by (auto simp: cand_rel_dom_def)
lemma alignment_graph_set_equality_of_pointwise:
  assumes f: "typed_pointwise_graph E Y R f"
  shows "R=restricted_graph (cand_rel_dom E Y R) f"
proof (rule subset_antisym)
  show "R\<subseteq>restricted_graph (cand_rel_dom E Y R) f"
  proof
    fix p assume p: "p\<in>R"
    obtain x y where pair: "p=(x,y)" by (cases p)
    have xy: "(x,y)\<in>R" using p pair by simp
    have xe: "x\<in>E" and yy: "y\<in>Y" using typed_relation xy by auto
    have xd: "x\<in>cand_rel_dom E Y R" using xe yy xy unfolding cand_rel_dom_def by blast
    have eq: "y=f x" using f xd yy xy unfolding typed_pointwise_graph_def by blast
    show "p\<in>restricted_graph (cand_rel_dom E Y R) f"
      using pair xd eq unfolding restricted_graph_def by blast
  qed
  show "restricted_graph (cand_rel_dom E Y R) f\<subseteq>R"
  proof
    fix p assume p: "p\<in>restricted_graph (cand_rel_dom E Y R) f"
    obtain x where xd: "x\<in>cand_rel_dom E Y R" and pair: "p=(x,f x)"
      using p unfolding restricted_graph_def by blast
    have fy: "f x\<in>Y" using f xd unfolding typed_pointwise_graph_def maps_dom_into_def by blast
    have "(x,f x)\<in>R" using f xd fy unfolding typed_pointwise_graph_def by blast
    then show "p\<in>R" using pair by simp
  qed
qed

lemma choice_pointwise:
  assumes ru: "right_unique E Y R"
  shows "typed_pointwise_graph E Y R (out_choice R)"
  unfolding typed_pointwise_graph_def maps_dom_into_def
  using out_choice_in_output[OF typed_relation] out_choice_in_relation
    right_unique_choice[OF typed_relation ru] by auto

lemma pointwise_unique:
  assumes f: "typed_pointwise_graph E Y R f" and g: "typed_pointwise_graph E Y R g"
    and x: "x\<in>cand_rel_dom E Y R"
  shows "g x=f x"
proof -
  have gy: "g x\<in>Y" using g x unfolding typed_pointwise_graph_def maps_dom_into_def by blast
  have gr: "(x,g x)\<in>R" using g x gy unfolding typed_pointwise_graph_def by blast
  show ?thesis using f x gy gr unfolding typed_pointwise_graph_def by blast
qed

lemma alignment_law_candidate_relation_partial_output_map:
  assumes ru: "right_unique E Y R"
  shows "\<exists>f. typed_pointwise_graph E Y R f \<and>
    (\<forall>g. typed_pointwise_graph E Y R g \<longrightarrow> (\<forall>x\<in>cand_rel_dom E Y R. g x=f x))"
  using choice_pointwise[OF ru] pointwise_unique by blast
lemma alignment_law_candidate_relation_literal_graph:
  assumes ru: "right_unique E Y R"
  shows "\<exists>f. maps_dom_into (cand_rel_dom E Y R) Y f \<and>
    R=restricted_graph (cand_rel_dom E Y R) f \<and>
    (\<forall>g. typed_pointwise_graph E Y R g \<longrightarrow> (\<forall>x\<in>cand_rel_dom E Y R. g x=f x))"
  using alignment_law_candidate_relation_partial_output_map[OF ru]
    alignment_graph_set_equality_of_pointwise unfolding typed_pointwise_graph_def by blast
lemma alignment_empty_relation_has_empty_domain:
  "R={} \<Longrightarrow> cand_rel_dom E Y R={}"
  by (simp add: cand_rel_dom_def)
lemma alignment_no_graph_if_right_uniqueness_fails:
  assumes a: "(x,y0)\<in>R" and b: "(x,y1)\<in>R" and ne: "y0\<noteq>y1"
  shows "\<not>(\<exists>f. typed_pointwise_graph E Y R f)"
proof
  assume "\<exists>f. typed_pointwise_graph E Y R f"
  then obtain f where f: "typed_pointwise_graph E Y R f" by blast
  have xe: "x\<in>E" and y0: "y0\<in>Y" and y1: "y1\<in>Y"
    using typed_relation a b by auto
  have xd: "x\<in>cand_rel_dom E Y R" using xe y0 a unfolding cand_rel_dom_def by blast
  have e0: "y0=f x" using f xd y0 a unfolding typed_pointwise_graph_def by blast
  have e1: "y1=f x" using f xd y1 b unfolding typed_pointwise_graph_def by blast
  show False using e0 e1 ne by simp
qed
end

lemma alignment_req_contains_operative: "Op\<in>abs_req_layer C Op Repr Out k"
  by (rule abs_op_in_req_layer)
lemma alignment_dep_rule_iff:
  "r\<in>abs_dep_repr C Op Repr Out \<longleftrightarrow>
    (\<exists>k<4. fst r=abs_req_layer C Op Repr Out k \<and> snd r\<in>Out k)"
  by (cases r) (auto simp: abs_dep_repr_def)
lemma alignment_genDef_is_least_closure_membership:
  "abs_gen_def Dep y In \<longleftrightarrow> (\<forall>S. In\<subseteq>S \<longrightarrow> abs_dep_closed Dep S \<longrightarrow> y\<in>S)"
  by (auto simp: abs_gen_def_def abs_gen_closure_def)
lemma alignment_safeSet_closed:
  "abs_dep_closed (abs_dep_repr C Op Repr Out) (abs_safe_set Op Out)"
  by (rule abs_safe_set_dep_closed)
lemma alignment_closure_subset_safeSet:
  assumes "paper_ctx_output_separation C Op L7Expr NotGExpr NotOpExpr Out"
  shows "abs_gen_closure (abs_dep_repr C Op Repr Out) (abs_ctx_notG C L7Expr NotGExpr NotOpExpr)
    \<subseteq>abs_safe_set Op Out"
  by (rule abs_gen_closure_least[OF separation_is_exact_ctx_subset[OF assms] abs_safe_set_dep_closed])
lemma alignment_canonical_output_not_generated:
  assumes sep: "paper_ctx_output_separation C Op L7Expr NotGExpr NotOpExpr Out"
    and k: "k<4" and y: "y\<in>Out k"
  shows "\<not>abs_gen_def (abs_dep_repr C Op Repr Out) y (abs_ctx_notG C L7Expr NotGExpr NotOpExpr)"
proof -
  have out: "y\<in>abs_out_notG Out" using k y unfolding abs_out_notG_def by auto
  show ?thesis by (rule abstract_designated_outputs_absent[OF sep out])
qed
lemma alignment_operative_failure_from_definition:
  "(L7\<and>G \<longleftrightarrow> operative) \<Longrightarrow> L7 \<Longrightarrow> \<not>G \<Longrightarrow> \<not>operative"
  by blast
lemma alignment_global_gluing_failure_blocks_representation_entry:
  assumes eq: "(L7\<and>G \<longleftrightarrow> operative)" and l: L7 and ng: "\<not>G"
    and sep: "paper_ctx_output_separation C Op L7Expr NotGExpr NotOpExpr Out"
  shows "\<not>operative \<and> (\<forall>k<4. \<forall>y\<in>Out k.
    \<not>abs_gen_def (abs_dep_repr C Op Repr Out) y (abs_ctx_notG C L7Expr NotGExpr NotOpExpr))"
  using alignment_operative_failure_from_definition[OF eq l ng]
    alignment_canonical_output_not_generated[OF sep] by blast
lemma alignment_supplied_output_remains_generated:
  "abs_gen_def (abs_dep_repr C Op Repr Out) y (insert y (abs_ctx_notG C L7Expr NotGExpr NotOpExpr))"
  unfolding abs_gen_def_def abs_gen_closure_def by auto

lemma actual_domain_in_eval_domain: "cand_rel_dom E Y R\<subseteq>E"
  by (auto simp: cand_rel_dom_def)
lemma empty_output_supported: "cand_rel_dom E {} R={}"
  by (simp add: cand_rel_dom_def)

ML \<open>
val roots = @{thms actual_law_component.alignment_evalPoint_is_in_actual_evalDom
  actual_law_component.alignment_candRelDom_is_exact_relation_domain
  actual_law_component.alignment_graph_set_equality_of_pointwise
  actual_law_component.alignment_law_candidate_relation_partial_output_map
  actual_law_component.alignment_law_candidate_relation_literal_graph
  actual_law_component.alignment_empty_relation_has_empty_domain
  alignment_req_contains_operative alignment_dep_rule_iff alignment_genDef_is_least_closure_membership
  alignment_safeSet_closed alignment_closure_subset_safeSet alignment_canonical_output_not_generated
  alignment_operative_failure_from_definition alignment_global_gluing_failure_blocks_representation_entry
  actual_law_component.alignment_no_graph_if_right_uniqueness_fails alignment_supplied_output_remains_generated};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
