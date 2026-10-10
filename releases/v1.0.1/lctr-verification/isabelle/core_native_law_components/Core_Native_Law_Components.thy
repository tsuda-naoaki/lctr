theory Core_Native_Law_Components
  imports "LCTR_Core_Native_Curves.Core_Native_Curves"
    "LCTR_Core_Native_Law_Family.Core_Native_Law_Family" "HOL-Library.FuncSet"
begin
record ('i,'v) native_component_input =
  in_indices :: "'i set"
  out_indices :: "'i set"
  evaluation_times :: "real set"
  evaluation_domain :: "(real \<times> ('i\<Rightarrow>'v)) set"
  candidate_relation :: "((real \<times> ('i\<Rightarrow>'v)) \<times> ('i\<Rightarrow>'v)) set"

locale native_law_context = observer_real C D B R Bind source_order rho
  for C :: "'c set" and D :: "'d set" and B :: "'b set"
    and R :: "('c \<times> 'd \<times> 'b) set"
    and Bind :: "(('c \<times> 'd \<times> 'b) \<times> ('c \<times> 'd \<times> 'b)) set"
    and source_order :: "('c \<times> 'c) set" and rho :: "'c set set \<Rightarrow> real" +
  fixes indices :: "'i set" and val_carriers :: "'i \<Rightarrow> 'v set"
    and observable :: "'i \<Rightarrow> 'b set \<Rightarrow> 'v"
  assumes single: "\<And>t s s'. (t,s)\<in>trajectory_rel \<Longrightarrow> (t,s')\<in>trajectory_rel \<Longrightarrow> s=s'"
    and fiber: fiber_condition
    and observable_typed: "\<And>i. i\<in>indices \<Longrightarrow> observable i`State \<subseteq> val_carriers i"
begin
definition curve where "curve i = real_curve (observable i)"
definition component_input_typed where
  "component_input_typed a \<longleftrightarrow>
    in_indices a\<subseteq>indices \<and> out_indices a\<subseteq>indices \<and>
    evaluation_times a\<subseteq>real_domain \<and>
    evaluation_domain a\<subseteq>real_domain \<times> PiE (in_indices a) val_carriers \<and>
    candidate_relation a\<subseteq>evaluation_domain a \<times> PiE (out_indices a) val_carriers"
definition generated where
  "generated a = \<lparr>eval_times = evaluation_times a,
    input_value = (\<lambda>t. restrict (\<lambda>i. curve i t) (in_indices a)),
    output_value = (\<lambda>t. restrict (\<lambda>i. curve i t) (out_indices a)),
    eval_domain = evaluation_domain a, law_relation = candidate_relation a\<rparr>"
definition evaluation_tuple where
  "evaluation_tuple a t = ((t,input_value (generated a) t),output_value (generated a) t)"

lemma curve_typed:
  assumes i: "i\<in>indices" and t: "t\<in>real_domain"
  shows "curve i t\<in>val_carriers i"
proof -
  obtain x where x: "x\<in>trajectory_domain" and tx: "t=rho(restricted_projection x)"
    using t unfolding real_domain_def order_domain_def by blast
  have state_member: "canonical_trajectory x\<in>State" using trajectory_map_typed x by blast
  have eq: "observable i(canonical_trajectory x)=real_curve(observable i)(rho(restricted_projection x))"
    using bspec[OF conjunct1[OF observable_factorization[OF fiber, of "observable i"]] x] by simp
  have "observable i(canonical_trajectory x)\<in>val_carriers i"
    using observable_typed[OF i] state_member by blast
  then show ?thesis unfolding curve_def using eq tx by simp
qed
lemma generated_values_typed:
  assumes a: "component_input_typed a" and t: "t\<in>evaluation_times a"
  shows "input_value (generated a) t\<in>PiE (in_indices a) val_carriers"
    and "output_value (generated a) t\<in>PiE (out_indices a) val_carriers"
  using a t unfolding component_input_typed_def generated_def
  by (auto simp: restrict_PiE_iff intro: curve_typed)
lemma generated_value_components:
  "input_value (generated a) t=restrict (\<lambda>i. curve i t) (in_indices a) \<and>
   output_value (generated a) t=restrict (\<lambda>i. curve i t) (out_indices a)"
  by (simp add: generated_def)
lemma evaluation_tuple_components:
  "evaluation_tuple a t=((t,restrict (\<lambda>i. curve i t) (in_indices a)),
    restrict (\<lambda>i. curve i t) (out_indices a))"
  by (simp add: evaluation_tuple_def generated_def)
lemma individual_input_typed:
  assumes a: "component_input_typed a" and t: "t\<in>eval_times (generated a)"
  shows "t\<in>evaluation_times a \<and> fst(fst(evaluation_tuple a t))=t \<and>
    (t,input_value (generated a) t)\<in>real_domain \<times> PiE (in_indices a) val_carriers"
  using a t generated_values_typed(1)[OF a] unfolding component_input_typed_def
    generated_def evaluation_tuple_def by auto
lemma evaluation_tuple_domain_typed:
  "individual_admissible (generated a) \<Longrightarrow> t\<in>eval_times (generated a) \<Longrightarrow>
    fst(evaluation_tuple a t)\<in>evaluation_domain a"
  by (auto simp: individual_admissible_def evaluation_tuple_def generated_def)
lemma candidate_relation_typed:
  "component_input_typed a \<Longrightarrow> p\<in>candidate_relation a \<Longrightarrow>
    fst p\<in>evaluation_domain a"
  unfolding component_input_typed_def by auto
lemma generated_membership_contract:
  "generated_member (generated a) \<longleftrightarrow>
    (\<forall>t\<in>eval_times (generated a). evaluation_tuple a t\<in>candidate_relation a)"
  by (simp add: generated_member_def evaluation_tuple_def generated_def)

lemma native_partial_output:
  assumes a: "component_input_typed a" and unique: "right_unique (generated a)"
  shows "\<exists>f. f`Domain(candidate_relation a)\<subseteq>PiE (out_indices a) val_carriers \<and>
    (\<forall>x\<in>Domain(candidate_relation a). \<forall>y. ((x,y)\<in>candidate_relation a \<longleftrightarrow> y=f x)) \<and>
    (\<forall>other. (\<forall>x\<in>Domain(candidate_relation a). \<forall>y.
      ((x,y)\<in>candidate_relation a \<longleftrightarrow> y=other x)) \<longrightarrow>
      (\<forall>x\<in>Domain(candidate_relation a). other x=f x))"
proof -
  let ?S = "candidate_relation a"
  let ?f = "graph_map ?S"
  have single: "\<And>x y z. (x,y)\<in>?S \<Longrightarrow> (x,z)\<in>?S \<Longrightarrow> y=z"
    using unique unfolding right_unique_def generated_def by (auto split: prod.splits)
  have relation_typed: "?S\<subseteq>evaluation_domain a \<times> PiE (out_indices a) val_carriers"
    using a unfolding component_input_typed_def by blast
  have typed: "?f`Domain ?S\<subseteq>PiE (out_indices a) val_carriers"
    using relation_typed graph_map_member[where S="?S"] by blast
  have exact: "\<And>x y. x\<in>Domain ?S \<Longrightarrow> ((x,y)\<in>?S \<longleftrightarrow> y=?f x)"
    using single graph_map_member[where S="?S"] by blast
  have uniq: "\<And>other. (\<forall>x\<in>Domain ?S. \<forall>y. ((x,y)\<in>?S \<longleftrightarrow> y=other x))
    \<Longrightarrow> (\<forall>x\<in>Domain ?S. other x=?f x)"
    using exact by blast
  show ?thesis using typed exact uniq by blast
qed

definition native_family where
  "native_family A a allowed faithful = \<lparr>time_carrier=real_domain, law_indices=A,
    input_carrier=(\<lambda>j. PiE (in_indices (a j)) val_carriers),
    output_carrier=(\<lambda>j. PiE (out_indices (a j)) val_carriers),
    components=(\<lambda>j. generated (a j)), admissible_common=allowed, faithful_family=faithful\<rparr>"
lemma native_family_typed:
  assumes ne: "A\<noteq>{}" and typed: "\<And>j. j\<in>A \<Longrightarrow> component_input_typed (a j)"
    and ext: "\<And>f g. typed_reindex_family (native_family A a allowed faithful) f \<Longrightarrow>
      typed_reindex_family (native_family A a allowed faithful) g \<Longrightarrow>
      same_reindex_family (native_family A a allowed faithful) f g \<Longrightarrow> (faithful f \<longleftrightarrow> faithful g)"
  shows "well_typed_family (native_family A a allowed faithful)"
proof -
  have data: "\<forall>j\<in>A. eval_times (generated (a j))\<subseteq>real_domain \<and>
    input_value (generated (a j)) ` eval_times (generated (a j))\<subseteq>PiE (in_indices (a j)) val_carriers \<and>
    output_value (generated (a j)) ` eval_times (generated (a j))\<subseteq>PiE (out_indices (a j)) val_carriers \<and>
    eval_domain (generated (a j))\<subseteq>real_domain \<times> PiE (in_indices (a j)) val_carriers \<and>
    law_relation (generated (a j))\<subseteq>eval_domain (generated (a j)) \<times> PiE (out_indices (a j)) val_carriers"
  proof (intro ballI)
    fix j assume j: "j\<in>A"
    have aj: "component_input_typed (a j)" by (rule typed[OF j])
    have ev: "eval_times (generated (a j))=evaluation_times (a j)" by (simp add: generated_def)
    have it: "input_value (generated (a j)) ` eval_times (generated (a j))\<subseteq>PiE (in_indices (a j)) val_carriers"
      using generated_values_typed(1)[OF aj] ev by blast
    have ot: "output_value (generated (a j)) ` eval_times (generated (a j))\<subseteq>PiE (out_indices (a j)) val_carriers"
      using generated_values_typed(2)[OF aj] ev by blast
    show "eval_times (generated (a j))\<subseteq>real_domain \<and>
      input_value (generated (a j)) ` eval_times (generated (a j))\<subseteq>PiE (in_indices (a j)) val_carriers \<and>
      output_value (generated (a j)) ` eval_times (generated (a j))\<subseteq>PiE (out_indices (a j)) val_carriers \<and>
      eval_domain (generated (a j))\<subseteq>real_domain \<times> PiE (in_indices (a j)) val_carriers \<and>
      law_relation (generated (a j))\<subseteq>eval_domain (generated (a j)) \<times> PiE (out_indices (a j)) val_carriers"
      using aj it ot unfolding component_input_typed_def generated_def
      by (simp only: law_component.select_convs; blast)
  qed
  show ?thesis using ne data ext unfolding well_typed_family_def native_family_def
    by (simp only: law_family.select_convs; blast)
qed
lemma native_common_valid_contract:
  assumes k5: "K5 (native_family A a allowed faithful)"
  shows "common_times (native_family A a allowed faithful)\<noteq>{} \<and>
    allowed (common_times (native_family A a allowed faithful)) \<and>
    (\<forall>t\<in>common_times (native_family A a allowed faithful). \<forall>j\<in>A.
      t\<in>evaluation_times (a j) \<and> evaluation_tuple (a j) t\<in>candidate_relation (a j))"
  using k5 by (auto simp: K5_def common_times_def native_family_def valid_times_def
    generated_def evaluation_tuple_def)
end
lemma empty_index_values_unique:
  "f\<in>PiE {} V \<Longrightarrow> g\<in>PiE {} V \<Longrightarrow> f=g"
  by simp
ML \<open>
val roots = @{thms native_law_context.generated_value_components
 native_law_context.evaluation_tuple_components native_law_context.individual_input_typed
 native_law_context.evaluation_tuple_domain_typed native_law_context.candidate_relation_typed
 native_law_context.generated_membership_contract native_law_context.native_partial_output
 native_law_context.native_common_valid_contract empty_index_values_unique};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = if null (Thm_Deps.all_oracles @{thms native_law_context.native_family_typed
  native_law_context.curve_typed native_law_context.generated_values_typed})
  then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
