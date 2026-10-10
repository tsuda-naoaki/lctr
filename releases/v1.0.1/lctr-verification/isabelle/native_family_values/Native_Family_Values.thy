theory Native_Family_Values
  imports "LCTR_Core_Native_Law_Transport.Core_Native_Law_Transport"
    "LCTR_Core_Native_Law_Components.Core_Native_Law_Components"
begin

locale generated_law_representations =
  base: observer_real C D B R Bind source_order rho0
  for C :: "'c set" and D :: "'d set" and B :: "'b set"
    and R :: "('c \<times> 'd \<times> 'b) set"
    and Bind :: "(('c \<times> 'd \<times> 'b) \<times> ('c \<times> 'd \<times> 'b)) set"
    and source_order :: "('c \<times> 'c) set" and rho0 :: "'c set set \<Rightarrow> real" +
  fixes d :: "(real,'a,'x,'y) law_family"
  assumes family_typed: "well_typed_family d"
    and within: "time_carrier d \<subseteq> base.real_domain"
begin

definition Reps where
  "Reps = {rho. observer_real C D B R Bind source_order rho}"
definition source_part where
  "source_part = {q\<in>base.order_domain. rho0 q\<in>time_carrier d}"
definition rep_times where "rep_times rho = image rho source_part"
definition to_rep where "to_rep rho = rho \<circ> inv_into source_part rho0"
definition from_rep where "from_rep rho = rho0 \<circ> inv_into source_part rho"
definition component_at where
  "component_at rho a = component_transport (to_rep rho) (from_rep rho) (components d a)"
definition eval_at where "eval_at rho a = image (to_rep rho) (eval_times (components d a))"
definition between where "between rho sigma = to_rep sigma \<circ> from_rep rho"
definition input_at where "input_at rho a = input_value (components d a) \<circ> from_rep rho"
definition output_at where "output_at rho a = output_value (components d a) \<circ> from_rep rho"

lemma all_representations_exact:
  "rho\<in>Reps \<longleftrightarrow> observer_real C D B R Bind source_order rho"
  by (simp add: Reps_def)
lemma base_representation: "rho0\<in>Reps"
  using base.observer_real_axioms by (simp add: Reps_def)

lemma actual_time_bijection:
  assumes rep: "rho\<in>Reps"
  shows "carrier_bijection (time_carrier d) (rep_times rho) (to_rep rho) (from_rep rho)"
proof -
  have other: "observer_real C D B R Bind source_order rho"
    using rep unfolding Reps_def by simp
  interpret tr: native_time_transport C D B R Bind source_order rho0 rho "time_carrier d"
    unfolding native_time_transport_def native_time_transport_axioms_def
    using base.observer_real_axioms other within by blast
  show ?thesis
    using tr.time.carrier_bijection_axioms
    unfolding rep_times_def to_rep_def from_rep_def source_part_def
      tr.new_time_def tr.change_def tr.change_inverse_def tr.part_def .
qed

lemma evaluation_bounds:
  "a\<in>law_indices d \<Longrightarrow> eval_times (components d a)\<subseteq>time_carrier d"
  using family_typed unfolding well_typed_family_def by blast
lemma evaluation_at_exact:
  "eval_times (component_at rho a)=eval_at rho a"
  by (simp add: component_at_def eval_at_def component_transport_def)
lemma same_transported_input_value:
  "input_at rho a t=input_value (component_at rho a) t"
  by (simp add: input_at_def component_at_def component_transport_def)
lemma same_transported_output_value:
  "output_at rho a t=output_value (component_at rho a) t"
  by (simp add: output_at_def component_at_def component_transport_def)
lemma evaluation_at_typed:
  assumes rep: "rho\<in>Reps" and a: "a\<in>law_indices d" and t: "t\<in>eval_at rho a"
  shows "t\<in>rep_times rho" and "from_rep rho t\<in>eval_times (components d a)"
proof -
  interpret tr: carrier_bijection "time_carrier d" "rep_times rho" "to_rep rho" "from_rep rho"
    by (rule actual_time_bijection[OF rep])
  obtain u where u: "u\<in>eval_times (components d a)" and tu: "t=to_rep rho u"
    using t unfolding eval_at_def by blast
  have ut: "u\<in>time_carrier d" using evaluation_bounds[OF a] u by blast
  show "t\<in>rep_times rho" using tr.forward_typed ut tu by blast
  show "from_rep rho t\<in>eval_times (components d a)"
    using tr.left_inverse[OF ut] tu u by simp
qed

lemma between_evaluation_bijection:
  assumes r: "rho\<in>Reps" and s: "sigma\<in>Reps" and a: "a\<in>law_indices d"
  shows "carrier_bijection (eval_at rho a) (eval_at sigma a)
    (between rho sigma) (between sigma rho)"
proof -
  interpret rr: carrier_bijection "time_carrier d" "rep_times rho" "to_rep rho" "from_rep rho"
    by (rule actual_time_bijection[OF r])
  interpret ss: carrier_bijection "time_carrier d" "rep_times sigma" "to_rep sigma" "from_rep sigma"
    by (rule actual_time_bijection[OF s])
  have rho_source: "\<And>t. t\<in>eval_at rho a \<Longrightarrow> from_rep rho t\<in>time_carrier d"
    using evaluation_at_typed(2)[OF r a] evaluation_bounds[OF a] by blast
  have sigma_source: "\<And>t. t\<in>eval_at sigma a \<Longrightarrow> from_rep sigma t\<in>time_carrier d"
    using evaluation_at_typed(2)[OF s a] evaluation_bounds[OF a] by blast
  show ?thesis
  proof
    show "image (between rho sigma) (eval_at rho a)\<subseteq>eval_at sigma a"
      using evaluation_at_typed(2)[OF r a] by (auto simp: between_def eval_at_def)
    show "image (between sigma rho) (eval_at sigma a)\<subseteq>eval_at rho a"
      using evaluation_at_typed(2)[OF s a] by (auto simp: between_def eval_at_def)
    show "\<And>t. t\<in>eval_at rho a \<Longrightarrow> between sigma rho (between rho sigma t)=t"
      using ss.left_inverse[OF rho_source] rr.right_inverse[OF evaluation_at_typed(1)[OF r a]]
      by (simp add: between_def)
    show "\<And>t. t\<in>eval_at sigma a \<Longrightarrow> between rho sigma (between sigma rho t)=t"
      using rr.left_inverse[OF sigma_source] ss.right_inverse[OF evaluation_at_typed(1)[OF s a]]
      by (simp add: between_def)
  qed
qed

lemma between_preserves_native_values:
  assumes r: "rho\<in>Reps" and s: "sigma\<in>Reps" and a: "a\<in>law_indices d"
    and t: "t\<in>eval_at rho a"
  shows "input_at sigma a (between rho sigma t)=input_at rho a t \<and>
    output_at sigma a (between rho sigma t)=output_at rho a t"
proof -
  interpret ss: carrier_bijection "time_carrier d" "rep_times sigma" "to_rep sigma" "from_rep sigma"
    by (rule actual_time_bijection[OF s])
  have src: "from_rep rho t\<in>time_carrier d"
    using evaluation_at_typed(2)[OF r a t] evaluation_bounds[OF a] by blast
  have eq: "from_rep sigma (to_rep sigma (from_rep rho t))=from_rep rho t"
    by (rule ss.left_inverse[OF src])
  show ?thesis by (simp add: input_at_def output_at_def between_def eq)
qed

lemma same_law_data_all_representations:
  "input_at rho a t=input_value (component_at rho a) t \<and>
    output_at rho a t=output_value (component_at rho a) t"
  by (simp add: input_at_def output_at_def component_at_def component_transport_def)
end

context native_law_context
begin
lemma generated_family_representation_instance:
  assumes ne: "A\<noteq>{}"
    and typed: "\<And>j. j\<in>A \<Longrightarrow> component_input_typed (a j)"
    and ext: "\<And>f g. typed_reindex_family (native_family A a allowed faithful) f \<Longrightarrow>
      typed_reindex_family (native_family A a allowed faithful) g \<Longrightarrow>
      same_reindex_family (native_family A a allowed faithful) f g \<Longrightarrow> (faithful f \<longleftrightarrow> faithful g)"
  shows "generated_law_representations C D B R Bind source_order rho
    (native_family A a allowed faithful)"
proof -
  have wf: "well_typed_family (native_family A a allowed faithful)"
    by (rule native_family_typed[OF ne typed ext])
  have times: "time_carrier (native_family A a allowed faithful)\<subseteq>real_domain"
    by (simp add: native_family_def)
  show ?thesis
    unfolding generated_law_representations_def generated_law_representations_axioms_def
    using observer_real_axioms wf times by blast
qed
end

ML \<open>
val roots = @{thms generated_law_representations.all_representations_exact
  generated_law_representations.same_transported_input_value
  generated_law_representations.same_transported_output_value
  generated_law_representations.between_evaluation_bijection
  generated_law_representations.between_preserves_native_values
  generated_law_representations.same_law_data_all_representations
  native_law_context.generated_family_representation_instance};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
