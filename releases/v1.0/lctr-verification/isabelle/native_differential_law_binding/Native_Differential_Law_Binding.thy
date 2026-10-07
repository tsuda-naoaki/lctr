theory Native_Differential_Law_Binding
  imports "LCTR_Core_Three_Layer_Synthesis.Core_Three_Layer_Synthesis"
    "LCTR_Native_Differential_Consequences.Native_Differential_Consequences"
begin

context native_dynamics_bundle
begin
context
  fixes Jlaw a allowed faithful
  assumes wf: "well_typed_family (candidates Jlaw a allowed faithful)"
begin

lemma actual_generated_family_instance:
  "generated_law_representations C D B R Bind source_order rho
    (candidates Jlaw a allowed faithful)"
proof -
  have times: "time_carrier (candidates Jlaw a allowed faithful) \<subseteq> real_domain"
    by (simp add: candidates_def law.native_family_def)
  show ?thesis
    unfolding generated_law_representations_def generated_law_representations_axioms_def
    using observer_real_axioms wf times by blast
qed

interpretation fam: generated_law_representations C D B R Bind source_order rho
  "candidates Jlaw a allowed faithful"
  by (rule actual_generated_family_instance)

lemma actual_representations_are_admitted:
  "other \<in> fam.Reps \<longleftrightarrow> master.admitted_embedding other"
  unfolding fam.Reps_def observer_real_def observer_real_axioms_def master.admitted_embedding_def
  using observer_linear_axioms by simp

lemma actual_component_is_core_component:
  assumes rep: "other \<in> fam.Reps"
  shows "fam.component_at other j = Core_Native_Law_Family.components (transported_for other Jlaw a allowed faithful) j"
proof -
  have obs: "observer_real C D B R Bind source_order other" using rep by (simp add: fam.Reps_def)
  interpret tr: native_time_transport C D B R Bind source_order rho other real_domain
    unfolding native_time_transport_def native_time_transport_axioms_def
    using observer_real_axioms obs by blast
  have times: "time_carrier (candidates Jlaw a allowed faithful) = real_domain"
    by (simp add: candidates_def law.native_family_def)
  interpret lt: law_transport real_domain tr.new_time tr.change tr.change_inverse
    "candidates Jlaw a allowed faithful" by (rule tr.law_transport_ready[OF times wf])
  have forward: "fam.to_rep other=tr.change"
    by (simp only: fam.to_rep_def fam.source_part_def tr.change_def tr.part_def times)
  have inverse: "fam.from_rep other=tr.change_inverse"
    by (simp only: fam.from_rep_def fam.source_part_def tr.change_inverse_def tr.part_def times)
  have target: "Core_Native_Law_Family.components (transported_for other Jlaw a allowed faithful) j =
    component_transport tr.change tr.change_inverse (Core_Native_Law_Family.components (candidates Jlaw a allowed faithful) j)"
    by (simp only: transported_for_def tr.transported_def lt.selectors)
  show ?thesis by (simp only: fam.component_at_def target forward inverse)
qed

lemma same_law_core_and_components:
  assumes op: "all_conditions (candidates Jlaw a allowed faithful)"
    and rep: "other \<in> fam.Reps"
  shows "\<exists>!x. transported_spec other Jlaw a allowed faithful x \<and> all_conditions (snd x) \<and>
    (\<forall>j. Core_Native_Law_Family.components (snd x) j = fam.component_at other j)"
proof -
  have admitted: "master.admitted_embedding other"
    using rep actual_representations_are_admitted by simp
  obtain x where x: "transported_spec other Jlaw a allowed faithful x \<and> all_conditions (snd x)"
    and uniq: "\<And>y. transported_spec other Jlaw a allowed faithful y \<and> all_conditions (snd y) \<Longrightarrow> y=x"
    using law_cores_all_embeddings[OF wf op] admitted by blast
  have component_eq: "\<forall>j. Core_Native_Law_Family.components (snd x) j = fam.component_at other j"
    using x unfolding transported_spec_def by (simp add: actual_component_is_core_component[OF rep])
  show ?thesis
    by (rule ex1I[where a=x]) (use x component_eq uniq in blast)+
qed
end
end

context generated_law_representations
begin
lemma full_time_image_order_isomorphism:
  assumes r: "rho \<in> Reps" and s: "other \<in> Reps"
  shows "\<exists>F. bij_betw F (image rho base.OrderTime) (image other base.OrderTime) \<and>
    (\<forall>u\<in>image rho base.OrderTime. \<forall>v\<in>image rho base.OrderTime. (F u<F v)=(u<v)) \<and>
    (\<forall>x\<in>base.OrderTime. F (rho x) = other x) \<and>
    (\<forall>G. (\<forall>x\<in>base.OrderTime. G (rho x) = other x) \<longrightarrow>
      (\<forall>y\<in>image rho base.OrderTime. G y=F y))"
proof -
  interpret rr: observer_real C D B R Bind source_order rho using r by (simp add: Reps_def)
  interpret ss: observer_real C D B R Bind source_order other using s by (simp add: Reps_def)
  interpret images: representation_images base.OrderTime rho other
  proof
    fix x y assume x: "x\<in>base.OrderTime" and y: "y\<in>base.OrderTime"
    show "(rho x = rho y) = (other x = other y)"
      using inj_on_eq_iff[OF rr.embedding_injective x y]
        inj_on_eq_iff[OF ss.embedding_injective x y] by simp
    show "(rho x<rho y)=(other x<other y)"
      using rr.order_iff ss.order_iff x y by blast
  qed
  show ?thesis by (rule images.image_order_iso_exists_unique_on)
qed
end

ML \<open>
val roots = @{thms native_dynamics_bundle.actual_generated_family_instance
  native_dynamics_bundle.actual_representations_are_admitted
  native_dynamics_bundle.actual_component_is_core_component
  native_dynamics_bundle.same_law_core_and_components
  generated_law_representations.full_time_image_order_isomorphism};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
