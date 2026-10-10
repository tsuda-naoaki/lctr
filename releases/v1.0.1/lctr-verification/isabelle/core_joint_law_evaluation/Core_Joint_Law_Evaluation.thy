theory Core_Joint_Law_Evaluation
 imports "LCTR_Core_Native_Joint_Relation.Core_Native_Joint_Relation"
 "LCTR_Core_Native_Law_Failure.Core_Native_Law_Failure"
begin
locale native_joint_law =
 native_joint_curves C D B J base R Bind source_order +
 base_time: observer_real C D B "R base" "Bind base" "source_order base" rho
 for C :: "'c set" and D :: "'d set" and B :: "'b set" and J :: "'i set" and base :: "'i"
 and R :: "'i\<Rightarrow>('c\<times>'d\<times>'b)set"
 and Bind :: "'i\<Rightarrow>(('c\<times>'d\<times>'b)\<times>('c\<times>'d\<times>'b))set"
 and source_order :: "'i\<Rightarrow>('c\<times>'c)set" and rho :: "'c set set\<Rightarrow>real" +
 fixes obs_indices :: "'i\<Rightarrow>'l set" and obs_carrier :: "('i\<times>'l)\<Rightarrow>'v set"
 and observable :: "('i\<times>'l)\<Rightarrow>'b set\<Rightarrow>'v"
 and rel_indices :: "'r set" and rel_carrier :: "'r\<Rightarrow>'w set"
 and source_relation :: "'r\<Rightarrow>(('i\<Rightarrow>'b)\<times>'w)set"
 assumes observable_typed: "\<And>i l b. i\<in>J \<Longrightarrow> l\<in>obs_indices i \<Longrightarrow>
 b\<in>observer_seed.State C D B (R i)(Bind i) \<Longrightarrow> observable(i,l)b\<in>obs_carrier(i,l)"
 and source_typed: "\<And>r. r\<in>rel_indices \<Longrightarrow> source_relation r\<subseteq>source_product\<times>rel_carrier r"
begin
definition real_time where "real_time=image rho common_domain"
definition order_inverse where "order_inverse=inv_into common_domain rho"
lemma common_domain_typed: "common_domain\<subseteq>base_time.OrderTime"
 using base_member base_time.order_domain_typed
 unfolding common_domain_def individual_domain_def by blast
lemma real_value_injective: "inj_on rho common_domain"
 by (rule inj_on_subset[OF base_time.embedding_injective common_domain_typed])
lemma real_projection_bijective: "bij_betw rho common_domain real_time"
 by (simp add: bij_betw_def real_time_def real_value_injective)
lemma inverse_on_projection: "q\<in>common_domain \<Longrightarrow> order_inverse(rho q)=q"
 unfolding order_inverse_def by (rule inv_into_f_f[OF real_value_injective])
lemma inverse_typed: "t\<in>real_time \<Longrightarrow> order_inverse t\<in>common_domain"
 unfolding real_time_def order_inverse_def by (rule inv_into_into) blast

definition real_relation where
 "real_relation r={(t,v). t\<in>real_time \<and> (order_inverse t,v)\<in>joint_relation(rel_carrier r)(source_relation r)}"
definition relation_domain where "relation_domain r=Domain(real_relation r)"
definition observation_valid where
 "observation_valid obs \<longleftrightarrow> (\<forall>r\<in>rel_indices. \<forall>t\<in>relation_domain r. (t,obs r t)\<in>real_relation r)"
definition selection_valid where
 "selection_valid Oidx Ridx H \<longleftrightarrow> H\<subseteq>real_time \<and>
  (\<forall>s. Oidx(s::bool)\<subseteq>Sigma J obs_indices \<and> Ridx s\<subseteq>rel_indices \<and>
    (\<forall>r\<in>Ridx s. H\<subseteq>relation_domain r))"
definition side_space where
 "side_space Oidx Ridx s=PiE (Oidx s) obs_carrier\<times>PiE (Ridx s) rel_carrier"
definition side_value where
 "side_value obs Oidx Ridx s t=
  (restrict(\<lambda>p. observable p(joint_curve(order_inverse t)(fst p)))(Oidx s),
   restrict(\<lambda>r. obs r t)(Ridx s))"

lemma individual_observable_component:
 "p\<in>Oidx s \<Longrightarrow> fst(side_value obs Oidx Ridx s t)p=
 observable p(joint_curve(order_inverse t)(fst p))"
 by (simp add: side_value_def)
lemma joint_relation_component_valid:
 assumes obs: "observation_valid obs" and sel: "selection_valid Oidx Ridx H"
 and t: "t\<in>H" and r: "r\<in>Ridx s"
 shows "(t,snd(side_value obs Oidx Ridx s t)r)\<in>real_relation r"
 using obs sel t r unfolding observation_valid_def selection_valid_def side_value_def by (auto; blast)
lemma joint_relation_source_valid:
 assumes obs: "observation_valid obs" and sel: "selection_valid Oidx Ridx H"
 and t: "t\<in>H" and r: "r\<in>Ridx s"
 and dom: "A\<subseteq>source_product" and sat: "source_saturated A (rel_carrier r)(source_relation r)"
 and x: "x\<in>source_product" and same: "source_projection x=joint_curve(order_inverse t)"
 shows "(x,snd(side_value obs Oidx Ridx s t)r)\<in>source_relation r"
proof -
 have rr: "r\<in>rel_indices"
  using sel r unfolding selection_valid_def by blast
 have tt: "t\<in>real_time"
  using sel t unfolding selection_valid_def by blast
 have belongs: "(order_inverse t,snd(side_value obs Oidx Ridx s t)r)\<in>
   joint_relation(rel_carrier r)(source_relation r)"
  using joint_relation_component_valid[OF obs sel t r] unfolding real_relation_def by simp
 have v: "snd(side_value obs Oidx Ridx s t)r\<in>rel_carrier r"
  using belongs unfolding joint_relation_def relation_pullback_def by simp
 show ?thesis
  using joint_source_membership[OF dom source_typed[OF rr] sat inverse_typed[OF tt] x same v] belongs by blast
qed
lemma side_value_typed:
 assumes obs: "observation_valid obs" and sel: "selection_valid Oidx Ridx H" and t: "t\<in>H"
 shows "side_value obs Oidx Ridx s t\<in>side_space Oidx Ridx s"
proof -
 have tt: "t\<in>real_time"
  using sel t unfolding selection_valid_def by blast
 have oo: "Oidx s\<subseteq>Sigma J obs_indices"
  using sel unfolding selection_valid_def by blast
 have q: "order_inverse t\<in>common_domain" by (rule inverse_typed[OF tt])
 have state: "\<And>i. i\<in>J \<Longrightarrow>
   joint_curve(order_inverse t)i\<in>observer_seed.State C D B (R i)(Bind i)"
  using joint_curve_typed[OF q] by (auto simp: PiE_iff)
 have ot: "\<And>p. p\<in>Oidx s \<Longrightarrow>
   observable p(joint_curve(order_inverse t)(fst p))\<in>obs_carrier p"
  using oo state observable_typed by (auto split: prod.splits)
 have rt: "\<And>r. r\<in>Ridx s \<Longrightarrow> obs r t\<in>rel_carrier r"
  using joint_relation_component_valid[OF obs sel t]
  unfolding real_relation_def joint_relation_def relation_pullback_def side_value_def by auto
 show ?thesis using ot rt unfolding side_space_def side_value_def by (auto simp: PiE_iff)
qed
definition joint_component where
 "joint_component obs Oidx Ridx H E S=
  \<lparr>eval_times=H,input_value=side_value obs Oidx Ridx False,output_value=side_value obs Oidx Ridx True,
   eval_domain=E,law_relation=S\<rparr>"
definition joint_tuple where
 "joint_tuple obs Oidx Ridx H E S t=
  ((t,input_value(joint_component obs Oidx Ridx H E S)t),
   output_value(joint_component obs Oidx Ridx H E S)t)"
lemma tuple_components:
 "joint_tuple obs Oidx Ridx H E S t=
  ((t,side_value obs Oidx Ridx False t),side_value obs Oidx Ridx True t)"
 by (simp add: joint_tuple_def joint_component_def)
definition joint_family where
 "joint_family obs A Oidx Ridx H E S allowed faithful=
  \<lparr>time_carrier=real_time,law_indices=A,
   input_carrier=(\<lambda>a. side_space(Oidx a)(Ridx a)False),
   output_carrier=(\<lambda>a. side_space(Oidx a)(Ridx a)True),
   components=(\<lambda>a. joint_component obs (Oidx a)(Ridx a)(H a)(E a)(S a)),
   admissible_common=allowed,faithful_family=faithful\<rparr>"
lemma joint_family_typed:
 assumes obs: "observation_valid obs" and ne: "A\<noteq>{}"
 and sel: "\<And>a. a\<in>A \<Longrightarrow> selection_valid(Oidx a)(Ridx a)(H a)"
 and et: "\<And>a. a\<in>A \<Longrightarrow> E a\<subseteq>real_time\<times>side_space(Oidx a)(Ridx a)False"
 and st: "\<And>a. a\<in>A \<Longrightarrow> S a\<subseteq>E a\<times>side_space(Oidx a)(Ridx a)True"
 and ext: "\<And>f g. typed_reindex_family(joint_family obs A Oidx Ridx H E S allowed faithful)f \<Longrightarrow>
  typed_reindex_family(joint_family obs A Oidx Ridx H E S allowed faithful)g \<Longrightarrow>
  same_reindex_family(joint_family obs A Oidx Ridx H E S allowed faithful)f g \<Longrightarrow>
  (faithful f \<longleftrightarrow> faithful g)"
 shows "well_typed_family(joint_family obs A Oidx Ridx H E S allowed faithful)"
proof -
 have hv: "\<And>a. a\<in>A \<Longrightarrow> H a\<subseteq>real_time"
  using sel unfolding selection_valid_def by blast
 have iv: "\<And>a t. a\<in>A \<Longrightarrow> t\<in>H a \<Longrightarrow>
  side_value obs (Oidx a)(Ridx a)False t\<in>side_space(Oidx a)(Ridx a)False"
  by (rule side_value_typed[OF obs sel]; assumption)
 have ov: "\<And>a t. a\<in>A \<Longrightarrow> t\<in>H a \<Longrightarrow>
  side_value obs (Oidx a)(Ridx a)True t\<in>side_space(Oidx a)(Ridx a)True"
  by (rule side_value_typed[OF obs sel]; assumption)
 show ?thesis
  using ne hv iv ov et st ext unfolding well_typed_family_def joint_family_def joint_component_def
  by (simp only: law_family.select_convs law_component.select_convs; blast)
qed
lemma five_condition_connection:
 "condition(joint_family obs A Oidx Ridx H E S allowed faithful)Law1=K1(joint_family obs A Oidx Ridx H E S allowed faithful) \<and>
  condition(joint_family obs A Oidx Ridx H E S allowed faithful)Law2=K2(joint_family obs A Oidx Ridx H E S allowed faithful) \<and>
  condition(joint_family obs A Oidx Ridx H E S allowed faithful)Law3=K3(joint_family obs A Oidx Ridx H E S allowed faithful) \<and>
  condition(joint_family obs A Oidx Ridx H E S allowed faithful)Law4=K4(joint_family obs A Oidx Ridx H E S allowed faithful) \<and>
  condition(joint_family obs A Oidx Ridx H E S allowed faithful)Law5=K5(joint_family obs A Oidx Ridx H E S allowed faithful)"
 by (rule condition_vector_exact)
lemma common_valid_joint_tuples:
 assumes all: "all_conditions(joint_family obs A Oidx Ridx H E S allowed faithful)"
 shows "common_times(joint_family obs A Oidx Ridx H E S allowed faithful)\<noteq>{} \<and>
  allowed(common_times(joint_family obs A Oidx Ridx H E S allowed faithful)) \<and>
  (\<forall>t\<in>common_times(joint_family obs A Oidx Ridx H E S allowed faithful). \<forall>a\<in>A.
   t\<in>H a \<and> joint_tuple obs (Oidx a)(Ridx a)(H a)(E a)(S a)t\<in>S a)"
 using all unfolding all_conditions_def K5_def common_times_def valid_times_def
 joint_family_def joint_component_def joint_tuple_def by auto
lemma joint_failure_exact:
 "selected_law_family.failure {()}(\<lambda>_. joint_family obs A Oidx Ridx H E S allowed faithful)() \<longleftrightarrow>
  \<not>all_conditions(joint_family obs A Oidx Ridx H E S allowed faithful)"
 by (rule selected_law_family.failure_on_selected_datum) simp
lemma joint_minimal_failure_cover:
 "\<not>all_conditions(joint_family obs A Oidx Ridx H E S allowed faithful) \<longleftrightarrow>
  (\<exists>i. selected_law_family.minimal_class {()}(\<lambda>_. joint_family obs A Oidx Ridx H E S allowed faithful)()i)"
 using joint_failure_exact[of obs A Oidx Ridx H E S allowed faithful]
  selected_law_family.failure_covered_by_minimal_classes[of "{()}" "\<lambda>_. joint_family obs A Oidx Ridx H E S allowed faithful" "()"]
 by blast
end
ML \<open>
val roots = @{thms native_joint_law.real_value_injective native_joint_law.real_projection_bijective
 native_joint_law.inverse_on_projection native_joint_law.individual_observable_component
 native_joint_law.joint_relation_component_valid native_joint_law.joint_relation_source_valid
 native_joint_law.tuple_components native_joint_law.five_condition_connection
 native_joint_law.common_valid_joint_tuples native_joint_law.joint_failure_exact native_joint_law.joint_minimal_failure_cover};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = if null (Thm_Deps.all_oracles @{thms native_joint_law.joint_family_typed native_joint_law.side_value_typed}) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
