theory Core_Dynamic_Master
 imports "LCTR_Core_Dynamics_Bundle.Core_Dynamics_Bundle"
begin
locale native_dynamic_master =
 native_law_bundle C D B R Bind source_order U L Q A idx record_map local_values local_obs compare val_range window field sequence +
 observer_linear C D B R Bind source_order
 for C :: "'c set" and D :: "'d set" and B :: "'b set"
 and R :: "('c\<times>'d\<times>'b)set"
 and Bind :: "(('c\<times>'d\<times>'b)\<times>('c\<times>'d\<times>'b))set"
 and source_order :: "('c\<times>'c)set"
 and U :: "'u set" and L :: "'l set" and Q :: "'i set"
 and A :: "'u\<Rightarrow>'a set" and idx :: "'l\<Rightarrow>'i"
 and record_map :: "'u\<Rightarrow>'a\<Rightarrow>'b"
 and local_values :: "'u\<Rightarrow>'l\<Rightarrow>'w set"
 and local_obs :: "'u\<Rightarrow>'l\<Rightarrow>'a\<Rightarrow>'w"
 and compare :: "'u\<Rightarrow>'l\<Rightarrow>'w\<Rightarrow>'v"
 and val_range :: "'l\<Rightarrow>'v set"
 and window :: "'d\<Rightarrow>'win" and field :: "'d\<Rightarrow>'fld" and sequence :: "'d\<Rightarrow>'seq" +
 assumes fiber: fiber_condition
begin
definition admitted_embedding where
 "admitted_embedding (rho::'c set set\<Rightarrow>real) \<longleftrightarrow>
  (\<forall>x\<in>OrderTime. \<forall>y\<in>OrderTime. (order_lt x y \<longleftrightarrow> rho x<rho y))"
abbreviation description_at where
 "description_at \<equiv> native_dynamics_bundle.description C D B R Bind source_order U L Q A idx record_map local_obs compare val_range window field sequence"
abbreviation description_spec_at where
 "description_spec_at \<equiv> native_dynamics_bundle.description_specification C D B R Bind source_order U L Q A idx record_map local_obs compare val_range window field sequence"
abbreviation witness_spec_at where
 "witness_spec_at \<equiv> native_dynamics_bundle.witness_specification C D B R Bind source_order U L Q A idx record_map local_obs compare val_range window field sequence"
lemma dynamic_master:
 assumes embeddings: "\<exists>rho. admitted_embedding rho"
 shows "(\<exists>rho. admitted_embedding rho) \<and> (\<forall>rho. admitted_embedding rho \<longrightarrow>
   (\<exists>!x. description_spec_at rho x) \<and> (\<exists>!x. witness_spec_at rho x))"
proof (rule conjI)
 show "\<exists>rho. admitted_embedding rho" by (rule embeddings)
 show "\<forall>rho. admitted_embedding rho \<longrightarrow>
   (\<exists>!x. description_spec_at rho x) \<and> (\<exists>!x. witness_spec_at rho x)"
 proof (intro allI impI)
  fix rho assume rho: "admitted_embedding rho"
  interpret dyn: native_dynamics_bundle C D B R Bind source_order U L Q A idx record_map local_values local_obs compare val_range window field sequence rho
   by (unfold_locales; use fiber rho[unfolded admitted_embedding_def] in blast)
  show "(\<exists>!x. description_spec_at rho x) \<and> (\<exists>!x. witness_spec_at rho x)"
   using dyn.description_exists_unique dyn.witness_exists_unique by blast
 qed
qed
lemma same_pre_real_input:
 assumes r: "admitted_embedding rho" and s: "admitted_embedding sigma"
 shows "fst(description_at rho)=fst(description_at sigma)"
proof -
 interpret first: native_dynamics_bundle C D B R Bind source_order U L Q A idx record_map local_values local_obs compare val_range window field sequence rho
  by (unfold_locales; use fiber r[unfolded admitted_embedding_def] in blast)
 interpret second: native_dynamics_bundle C D B R Bind source_order U L Q A idx record_map local_values local_obs compare val_range window field sequence sigma
  by (unfold_locales; use fiber s[unfolded admitted_embedding_def] in blast)
 show ?thesis by (simp add: first.description_def second.description_def)
qed
end
ML \<open>
val roots = @{thms native_dynamic_master.dynamic_master native_dynamic_master.same_pre_real_input};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
