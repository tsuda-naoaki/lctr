theory Core_Selected_Generated_Law
 imports "LCTR_Native_Law_Datum_Semantics.Native_Law_Datum_Semantics"
   "LCTR_Core_Law_Datum_Assembly.Core_Law_Datum_Assembly"
begin

definition generated where
 "generated dyn joint Omega domains rho d \<longleftrightarrow>
 eval_spec d\<in>ready_set dyn joint \<and> rho\<in>Omega(eval_spec d) \<and>
 time_carrier(family d)\<subseteq>rho ` domains(eval_spec d)"
definition time_admissible where
 "time_admissible dyn joint Omega domains rho d \<longleftrightarrow>
 generated dyn joint Omega domains rho d \<and> Core_Native_Law_Family.all_conditions(family d)"
definition forgotten where "forgotten pairs e=map_option snd (pairs e)"

lemma generated_exact:
 "generated dyn joint Omega domains rho d \<longleftrightarrow>
 eval_spec d\<in>ready_set dyn joint \<and> rho\<in>Omega(eval_spec d) \<and>
 time_carrier(family d)\<subseteq>rho ` domains(eval_spec d)"
 by (rule generated_def)

locale generated_selection =
 fixes pairs :: "'e \<Rightarrow> (('p \<Rightarrow> real) \<times> ('e,'j,(real,'a,'x,'y) law_family) law_datum) option"
   and dyn :: "'e \<Rightarrow> bool" and joint :: "'j \<Rightarrow> bool"
   and Omega :: "'e+'j \<Rightarrow> ('p \<Rightarrow> real) set"
   and domains :: "'e+'j \<Rightarrow> 'p set"
 assumes same_spec: "\<And>e rho d. pairs e=Some(rho,d) \<Longrightarrow> eval_spec d=Inl e"
   and compatible: "\<And>e rho d. pairs e=Some(rho,d) \<Longrightarrow> generated dyn joint Omega domains rho d"
begin

lemma selected_generation_components:
 assumes sel: "pairs e=Some(rho,d)"
 shows "eval_spec d\<in>ready_set dyn joint \<and> rho\<in>Omega(eval_spec d) \<and>
 time_carrier(family d)\<subseteq>rho ` domains(eval_spec d)"
 using compatible[OF sel] unfolding generated_def .

lemma selected_domain_ready:
 assumes sel: "pairs e=Some(rho,d)"
 shows "dyn e"
 using selected_generation_components[OF sel] same_spec[OF sel]
 by (simp add: single_ready_exact)

lemma forget_retains_specification:
 assumes sel: "pairs e=Some(rho,d)"
 shows "forgotten pairs e=Some d \<and> eval_spec d=Inl e"
 using same_spec[OF sel] by (simp add: forgotten_def sel)

sublocale ready: ready_native_selection "forgotten pairs" dyn
proof
 fix e d
 assume h: "forgotten pairs e=Some d"
 then obtain rho where sel: "pairs e=Some(rho,d)"
   unfolding forgotten_def by (cases "pairs e") auto
 show "dyn e" by (rule selected_domain_ready[OF sel])
next
 fix e d
 assume h: "forgotten pairs e=Some d"
 then obtain rho where sel: "pairs e=Some(rho,d)"
   unfolding forgotten_def by (cases "pairs e") auto
 show "eval_spec d=Inl e" by (rule same_spec[OF sel])
qed

lemma selected_condition_exact:
 assumes sel: "pairs e=Some(rho,d)"
 shows "native_total_condition (forgotten pairs) e i \<longleftrightarrow>
 Core_Native_Law_Family.condition (family d) i"
 using forget_retains_specification[OF sel]
 by (simp add: Native_Law_Datum_Semantics.selected_condition_exact)

lemma selected_failure_operative:
 assumes sel: "pairs e=Some(rho,d)"
 shows "native_selected_failure (forgotten pairs) e \<longleftrightarrow>
 dyn e \<and> \<not>native_law_operative dyn joint d"
 by (rule ready.native_failure_vs_operative[OF forget_retains_specification[OF sel, THEN conjunct1]])

lemma selected_time_admissibility:
 assumes sel: "pairs e=Some(rho,d)"
 shows "time_admissible dyn joint Omega domains rho d \<longleftrightarrow>
 native_law_operative dyn joint d"
 using compatible[OF sel] selected_generation_components[OF sel]
 by (simp add: time_admissible_def native_law_operative_def)

lemma outside_selection_not_failure:
 assumes "pairs e=None"
 shows "(\<forall>i. \<not>native_total_condition (forgotten pairs) e i) \<and>
 \<not>native_selected_failure (forgotten pairs) e"
 by (rule native_outside_selection) (simp add: forgotten_def assms)
end

lemma generated_common_representability:
 assumes g: "generated dyn joint Omega domains rho d"
 and all: "Core_Native_Law_Family.all_conditions(family d)"
 shows "common_times(family d)\<noteq>{} \<and>
 (\<forall>t\<in>common_times(family d). t\<in>rho ` domains(eval_spec d) \<and>
 (\<forall>a\<in>law_indices(family d). t\<in>eval_times(components(family d)a) \<and>
 evaluation_tuple d a t\<in>law_relation(components(family d)a)))"
proof -
 have k: "K5(family d)" using all unfolding Core_Native_Law_Family.all_conditions_def by blast
 note c = common_valid_contract[OF k]
 have sub: "common_times(family d)\<subseteq>rho ` domains(eval_spec d)"
   using g unfolding generated_def common_times_def by blast
 show ?thesis using c sub by blast
qed

lemma proper_generated_subdomain_possible:
 "{0::real} \<subset> (\<lambda>x::real. x) ` {0,1}"
 by auto

ML \<open>
val roots = @{thms generated_exact generated_selection.selected_generation_components
 generated_selection.selected_domain_ready generated_selection.forget_retains_specification
 generated_selection.selected_condition_exact generated_selection.selected_failure_operative
 generated_selection.selected_time_admissibility generated_selection.outside_selection_not_failure
 generated_common_representability proper_generated_subdomain_possible};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
