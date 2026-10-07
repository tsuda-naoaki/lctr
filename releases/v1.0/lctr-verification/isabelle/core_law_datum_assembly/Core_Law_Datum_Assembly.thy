theory Core_Law_Datum_Assembly
 imports "LCTR_Core_Native_Law_Components.Core_Native_Law_Components"
   "LCTR_Core_Law_Readiness.Core_Law_Readiness"
begin

definition assemble where "assemble e f=\<lparr>eval_spec=e,family=f\<rparr>"
definition coupling where "coupling s j d=case_sum s j (eval_spec d)"
definition evaluation_tuple where
 "evaluation_tuple d a t=((t,input_value(components(family d)a)t),output_value(components(family d)a)t)"

lemma outer_projections: "eval_spec(assemble e f)=e \<and> family(assemble e f)=f"
 by (simp add: assemble_def)
lemma coupling_single: "coupling s j (assemble (Inl e) f)=s e"
 by (simp add: assemble_def coupling_def)
lemma coupling_joint: "coupling s j (assemble (Inr e) f)=j e"
 by (simp add: assemble_def coupling_def)
lemma component_projection: "components(family(assemble e f))a=components f a"
 by (simp add: assemble_def)
lemma family_projections:
 "admissible_common(family(assemble e f))=admissible_common f \<and>
 faithful_family(family(assemble e f))=faithful_family f"
 by (simp add: assemble_def)

lemma individual_input_typed:
 assumes wf: "well_typed_family(family d)" and a: "a\<in>law_indices(family d)"
 and t: "t\<in>eval_times(components(family d)a)"
 shows "(t,input_value(components(family d)a)t)\<in>
 time_carrier(family d)\<times>input_carrier(family d)a"
proof -
 have types: "eval_times(components(family d)a)\<subseteq>time_carrier(family d) \<and>
 input_value(components(family d)a) ` eval_times(components(family d)a)\<subseteq>input_carrier(family d)a"
  using wf a unfolding well_typed_family_def by blast
 show ?thesis using types t by blast
qed

lemma evaluation_tuple_domain_typed:
 assumes wf: "well_typed_family(family d)" and k: "K1(family d)"
 and a: "a\<in>law_indices(family d)" and t: "t\<in>eval_times(components(family d)a)"
 shows "evaluation_tuple d a t\<in>eval_domain(components(family d)a)\<times>output_carrier(family d)a"
proof -
 have out_typed: "output_value(components(family d)a) ` eval_times(components(family d)a)\<subseteq>output_carrier(family d)a"
  using wf a unfolding well_typed_family_def by blast
 have in_domain: "(t,input_value(components(family d)a)t)\<in>eval_domain(components(family d)a)"
  using k a t unfolding K1_def individual_admissible_def by blast
 show ?thesis using in_domain out_typed t unfolding evaluation_tuple_def by blast
qed

lemma common_valid_contract:
 assumes k: "K5(family d)"
 shows "common_times(family d)\<noteq>{} \<and>
 admissible_common(family d)(common_times(family d)) \<and>
 (\<forall>t\<in>common_times(family d). \<forall>a\<in>law_indices(family d).
 t\<in>eval_times(components(family d)a) \<and> evaluation_tuple d a t\<in>law_relation(components(family d)a))"
 using k unfolding K5_def common_times_def valid_times_def evaluation_tuple_def by blast

lemma evaluation_tuple_projections:
 "fst(fst(evaluation_tuple d a t))=t \<and>
 snd(fst(evaluation_tuple d a t))=input_value(components(family d)a)t \<and>
 snd(evaluation_tuple d a t)=output_value(components(family d)a)t"
 by (simp add: evaluation_tuple_def)

context native_law_context
begin
lemma native_component_projection:
 "components(family(assemble e (native_family A a allowed faithful)))i=generated(a i)"
 by (simp add: assemble_def native_family_def)
end

ML \<open>
val roots = @{thms outer_projections coupling_single coupling_joint component_projection family_projections
 individual_input_typed evaluation_tuple_domain_typed common_valid_contract evaluation_tuple_projections
 native_law_context.native_component_projection};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
