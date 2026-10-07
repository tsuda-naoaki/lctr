theory Core_Three_Layer_Synthesis
 imports "LCTR_Core_Dynamic_Master.Core_Dynamic_Master"
 "LCTR_Core_Stage_Boundaries.Core_Stage_Boundaries"
 "LCTR_Core_Law_Differential_Bundle.Core_Law_Differential_Bundle"
 "LCTR_Core_Native_Law_Failure.Core_Native_Law_Failure"
 "LCTR_Core_Differential_Failure.Core_Differential_Failure"
begin
locale native_three_layers =
 stage_boundaries exactInput K lawDomain diffDomain lawDatum diffDatum all_conditions
 "\<lambda>d. \<forall>i. Core_Differential_Failure.condition d i"
 for exactInput :: "'e\<Rightarrow>bool" and K :: "'e\<Rightarrow>dynamics_index\<Rightarrow>bool"
 and lawDomain diffDomain :: "'e set"
 and lawDatum :: "'e\<Rightarrow>('t,'a,'x,'y)law_family" and diffDatum :: "'e\<Rightarrow>'o native"
begin
sublocale law: selected_law_family lawDomain lawDatum .
sublocale diff: selected_differential diffDomain lawDatum diffDatum all_conditions .
lemma dynamics_equivalence:
 "dynOperative ev \<longleftrightarrow> exactInput ev \<and> (\<forall>i. K ev i)"
 by (simp add: dynOperative_def)
lemma law_equivalence:
 assumes dom: "\<And>ev. ev\<in>lawDomain \<longleftrightarrow> dynOperative ev"
 shows "lawOperative ev \<longleftrightarrow> dynOperative ev \<and> (\<forall>i. law.total_condition ev i)"
 using dom[of ev]
 by (auto simp: lawOperative_def law.total_condition_def all_conditions_exact)
lemma differential_equivalence:
 "diffOperative ev \<longleftrightarrow> lawOperative ev \<and> (\<forall>i. diff.selectedCondition ev i)"
 using subdomain
 by (auto simp: diffOperative_def lawOperative_def diff.selectedCondition_def)
lemma cumulative_same_input:
 "(\<And>ev. ev\<in>lawDomain \<longleftrightarrow> dynOperative ev) \<Longrightarrow>
 diffOperative ev \<Longrightarrow> lawOperative ev \<and> dynOperative ev \<and> exactInput ev"
 using differential_requires_same_law by (auto simp: lawOperative_def dynOperative_def)
end

context native_dynamics_bundle
begin
sublocale master: native_dynamic_master C D B R Bind source_order U L Q A idx record_map
 local_values local_obs compare val_range window field sequence
 by unfold_locales (rule fiber)
lemma dynamics_every_embedding:
 "(\<exists>sigma. master.admitted_embedding sigma) \<and>
 (\<forall>sigma. master.admitted_embedding sigma \<longrightarrow>
 (\<exists>!x. master.description_spec_at sigma x) \<and> (\<exists>!x. master.witness_spec_at sigma x))"
proof (rule master.dynamic_master)
 have "master.admitted_embedding rho" by (simp add: master.admitted_embedding_def order_iff)
 then show "\<exists>sigma. master.admitted_embedding sigma" by (rule exI[where x=rho])
qed

definition transported_for where
 "transported_for sigma Jlaw a allowed faithful=
 native_time_transport.transported C D B R Bind source_order rho sigma real_domain
 (candidates Jlaw a allowed faithful)"
definition transported_spec where
 "transported_spec sigma Jlaw a allowed faithful x \<longleftrightarrow>
 master.description_spec_at sigma (fst x) \<and>
 snd x=transported_for sigma Jlaw a allowed faithful"
lemma transported_core_exists_unique:
 assumes sigma: "master.admitted_embedding sigma"
 shows "\<exists>!x. transported_spec sigma Jlaw a allowed faithful x"
proof -
 obtain d where d: "master.description_spec_at sigma d"
 and uniq: "\<And>x. master.description_spec_at sigma x \<Longrightarrow> x=d"
  using dynamics_every_embedding sigma by blast
 show ?thesis
 proof (rule ex1I[where a="(d,transported_for sigma Jlaw a allowed faithful)"])
  show "transported_spec sigma Jlaw a allowed faithful(d,transported_for sigma Jlaw a allowed faithful)"
   using d by (simp add: transported_spec_def)
 next
  fix x assume x: "transported_spec sigma Jlaw a allowed faithful x"
  have one: "fst x=d" by (rule uniq) (use x in \<open>simp add: transported_spec_def\<close>)
  show "x=(d,transported_for sigma Jlaw a allowed faithful)"
   using one x unfolding transported_spec_def by (cases x) simp
 qed
qed
lemma same_law_all_embeddings:
 assumes wf: "well_typed_family(candidates Jlaw a allowed faithful)"
 and all: "all_conditions(candidates Jlaw a allowed faithful)"
 shows "\<forall>sigma. master.admitted_embedding sigma \<longrightarrow>
 all_conditions(transported_for sigma Jlaw a allowed faithful) \<and>
 common_times(transported_for sigma Jlaw a allowed faithful)\<noteq>{} \<and>
 (\<forall>t\<in>common_times(transported_for sigma Jlaw a allowed faithful).
 t\<in>observer_real.real_domain C D B R Bind source_order sigma)"
proof (intro allI impI)
 fix sigma assume sigma: "master.admitted_embedding sigma"
 interpret tr: native_law_generation_transport C D B R Bind source_order rho sigma
  Q obs.canonical_range obs.canonical
  by (unfold_locales; use single fiber canonical_value_typed sigma[unfolded master.admitted_embedding_def] in blast)
 have wf': "well_typed_family(law.native_family Jlaw a allowed faithful)"
  using wf by (simp add: candidates_def)
 have all': "all_conditions(law.native_family Jlaw a allowed faithful)"
  using all by (simp add: candidates_def)
 show "all_conditions(transported_for sigma Jlaw a allowed faithful) \<and>
 common_times(transported_for sigma Jlaw a allowed faithful)\<noteq>{} \<and>
 (\<forall>t\<in>common_times(transported_for sigma Jlaw a allowed faithful).
 t\<in>observer_real.real_domain C D B R Bind source_order sigma)"
  using tr.transported_law_generation[OF wf' all']
  unfolding transported_for_def candidates_def by blast
qed
lemma law_cores_all_embeddings:
 assumes wf: "well_typed_family(candidates Jlaw a allowed faithful)"
 and all: "all_conditions(candidates Jlaw a allowed faithful)"
 shows "\<forall>sigma. master.admitted_embedding sigma \<longrightarrow>
 (\<exists>!x. transported_spec sigma Jlaw a allowed faithful x \<and> all_conditions(snd x))"
proof (intro allI impI)
 fix sigma assume sigma: "master.admitted_embedding sigma"
 obtain x where x: "transported_spec sigma Jlaw a allowed faithful x"
 and uniq: "\<And>y. transported_spec sigma Jlaw a allowed faithful y \<Longrightarrow> y=x"
  using transported_core_exists_unique[OF sigma] by blast
 have all': "all_conditions(transported_for sigma Jlaw a allowed faithful)"
  using same_law_all_embeddings[OF wf all] sigma by blast
 have valid: "all_conditions(snd x)" using x all' by (simp add: transported_spec_def)
 show "\<exists>!x. transported_spec sigma Jlaw a allowed faithful x \<and> all_conditions(snd x)"
  by (rule ex1I[where a=x]) (use x valid uniq in blast)+
qed
lemma same_reference_differential_objects:
 "all_conditions(candidates Jlaw a allowed faithful) \<Longrightarrow>
 (\<exists>!x. differential_specification Jlaw a allowed faithful x \<and> all_conditions(df_candidate x)) \<and>
 df_embedding(differential Jlaw a allowed faithful)=td_embedding(fst(snd description)) \<and>
 df_representation(differential Jlaw a allowed faithful)=td_representation(fst(snd description)) \<and>
 df_scalar(differential Jlaw a allowed faithful)=tr_scalar(snd(snd description)) \<and>
 df_curves(differential Jlaw a allowed faithful)=tr_real_curve(snd(snd description))"
 using differential_with_law_conditions differential_same_dynamics by blast
end
lemma differential_conditions_keep_native_domains:
 "(\<forall>i. Core_Differential_Failure.condition d i) \<Longrightarrow>
 Core_Differential_Failure.condition d N1 \<and> Core_Differential_Failure.condition d N2 \<and>
 Core_Differential_Failure.condition d N3 \<and> Core_Differential_Failure.condition d N4 \<and>
 Core_Differential_Failure.condition d N5"
 by (simp add: Core_Differential_Failure.all_conditions_complete)

ML \<open>
val roots = @{thms native_three_layers.dynamics_equivalence native_three_layers.law_equivalence
 native_three_layers.differential_equivalence native_three_layers.cumulative_same_input
 native_dynamics_bundle.dynamics_every_embedding native_dynamics_bundle.transported_core_exists_unique
 native_dynamics_bundle.same_law_all_embeddings native_dynamics_bundle.law_cores_all_embeddings
 native_dynamics_bundle.same_reference_differential_objects differential_conditions_keep_native_domains};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
