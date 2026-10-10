theory Core_Native_Law_Generation
  imports "LCTR_Core_Native_Law_Components.Core_Native_Law_Components"
    "LCTR_Core_Native_Law_Transport.Core_Native_Law_Transport"
begin
context native_law_context
begin
lemma common_generated_representability:
  assumes all: "all_conditions (native_family A a allowed faithful)"
  shows "common_times(native_family A a allowed faithful)\<noteq>{} \<and>
    allowed(common_times(native_family A a allowed faithful)) \<and>
    (\<forall>t\<in>common_times(native_family A a allowed faithful).
      t\<in>real_domain \<and> (\<forall>j\<in>A. t\<in>evaluation_times(a j) \<and>
        evaluation_tuple(a j)t\<in>candidate_relation(a j)))"
  using native_common_valid_contract all
  unfolding all_conditions_def common_times_def native_family_def by auto

lemma generated_preimage_unique:
  assumes t: "t\<in>real_domain"
  shows "\<exists>!q. q\<in>order_domain \<and> rho q=t"
proof -
  obtain q where q: "q\<in>order_domain" and eq: "rho q=t"
    using t unfolding real_domain_def by blast
  have uniq: "\<And>r. r\<in>order_domain \<Longrightarrow> rho r=t \<Longrightarrow> r=q"
    using restricted_embedding_injective q eq unfolding inj_on_def by blast
  show ?thesis using q eq uniq by blast
qed

lemma actual_trajectory_representative:
  "t\<in>real_domain \<Longrightarrow> \<exists>x\<in>trajectory_domain. rho(restricted_projection x)=t"
  unfolding real_domain_def order_domain_def by blast

lemma common_evaluation_source_values:
  assumes valid: "t\<in>common_times(native_family A a allowed faithful)"
  shows "\<exists>x\<in>trajectory_domain. rho(restricted_projection x)=t \<and>
    (\<forall>j\<in>A. t\<in>evaluation_times(a j) \<and>
      evaluation_tuple(a j)t =
        ((t,restrict (\<lambda>i. observable i(canonical_trajectory x)) (in_indices(a j))),
         restrict (\<lambda>i. observable i(canonical_trajectory x)) (out_indices(a j))) \<and>
      evaluation_tuple(a j)t\<in>candidate_relation(a j))"
proof -
  have t: "t\<in>real_domain"
    using valid unfolding common_times_def native_family_def by simp
  obtain x where x: "x\<in>trajectory_domain" and tx: "rho(restricted_projection x)=t"
    using actual_trajectory_representative[OF t] by blast
  have curve_values: "\<And>i. curve i t=observable i(canonical_trajectory x)"
  proof -
    fix i
    have eq: "observable i(canonical_trajectory x)=order_curve(observable i)(restricted_projection x) \<and>
      order_curve(observable i)(restricted_projection x)=real_curve(observable i)(rho(restricted_projection x))"
      by (rule bspec[OF conjunct1[OF observable_factorization[OF fiber, of "observable i"]] x])
    show "curve i t=observable i(canonical_trajectory x)" using eq tx unfolding curve_def by simp
  qed
  have mem: "\<forall>j\<in>A. t\<in>evaluation_times(a j) \<and>
    evaluation_tuple(a j)t\<in>candidate_relation(a j)"
    using valid unfolding common_times_def native_family_def valid_times_def
      generated_def evaluation_tuple_def by auto
  show ?thesis
    using x tx mem by (intro bexI[of _ x]; simp add: evaluation_tuple_components curve_values)
qed

lemma empty_trajectory_rejects_law_conditions:
  "trajectory_domain={} \<Longrightarrow> \<not>all_conditions(native_family A a allowed faithful)"
proof
  assume empty: "trajectory_domain={}"
    and all: "all_conditions(native_family A a allowed faithful)"
  obtain t where t: "t\<in>real_domain"
    using common_generated_representability[OF all] by blast
  show False using actual_trajectory_representative[OF t] empty by simp
qed
end

locale native_law_generation_transport =
  old: native_law_context C D B R Bind source_order rho indices val_carriers observable +
  newer: observer_real C D B R Bind source_order rho'
  for C :: "'c set" and D :: "'d set" and B :: "'b set"
    and R :: "('c\<times>'d\<times>'b) set"
    and Bind :: "(('c\<times>'d\<times>'b)\<times>('c\<times>'d\<times>'b)) set"
    and source_order :: "('c\<times>'c) set" and rho rho' :: "'c set set\<Rightarrow>real"
    and indices :: "'i set" and val_carriers :: "'i\<Rightarrow>'v set"
    and observable :: "'i\<Rightarrow>'b set\<Rightarrow>'v"
begin
sublocale tr: native_time_transport C D B R Bind source_order rho rho' old.real_domain
  by unfold_locales (fact old.anti | fact old.inc_trans | fact old.order_iff |
    fact newer.order_iff | simp)+

lemma transported_law_generation:
  assumes wf: "well_typed_family(old.native_family A a allowed faithful)"
    and all: "all_conditions(old.native_family A a allowed faithful)"
  shows "all_conditions(tr.transported(old.native_family A a allowed faithful)) \<and>
    common_times(tr.transported(old.native_family A a allowed faithful))\<noteq>{} \<and>
    (\<forall>t\<in>common_times(tr.transported(old.native_family A a allowed faithful)).
      t\<in>newer.real_domain \<and>
      (\<forall>j\<in>A. t\<in>eval_times(components(tr.transported(old.native_family A a allowed faithful))j) \<and>
        ((t,input_value(components(tr.transported(old.native_family A a allowed faithful))j)t),
          output_value(components(tr.transported(old.native_family A a allowed faithful))j)t)
          \<in>law_relation(components(tr.transported(old.native_family A a allowed faithful))j)))"
proof -
  let ?d = "old.native_family A a allowed faithful"
  let ?e = "tr.transported ?d"
  have td: "time_carrier ?d=old.real_domain" by (simp add: old.native_family_def)
  have conditions: "all_conditions ?e"
    using tr.native_five_conditions[OF td wf] all unfolding all_conditions_def by blast
  have ne: "common_times ?e\<noteq>{}" using conditions unfolding all_conditions_def K5_def by blast
  interpret transport: law_transport old.real_domain tr.new_time tr.change tr.change_inverse ?d
    by (rule tr.law_transport_ready[OF td wf])
  have selectors: "time_carrier ?e=tr.new_time" "law_indices ?e=A"
    using transport.selectors(1,2) unfolding tr.transported_def
    by (simp_all only: old.native_family_def law_family.select_convs)
  have members: "\<forall>t\<in>common_times ?e. t\<in>newer.real_domain \<and>
      (\<forall>j\<in>A. t\<in>eval_times(components ?e j) \<and>
        ((t,input_value(components ?e j)t),output_value(components ?e j)t)
          \<in>law_relation(components ?e j))"
    using tr.changed_domain_contained selectors unfolding common_times_def valid_times_def by blast
  show ?thesis using conditions ne members by blast
qed
end
ML \<open>
val roots = @{thms native_law_context.common_generated_representability
 native_law_context.generated_preimage_unique native_law_context.actual_trajectory_representative
 native_law_context.common_evaluation_source_values native_law_generation_transport.transported_law_generation
 native_law_context.empty_trajectory_rejects_law_conditions};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
