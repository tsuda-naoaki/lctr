theory Core_Native_Law_Transport
  imports "LCTR_Core_Native_Curves.Core_Native_Curves"
    "LCTR_Core_Law_Transport.Core_Law_Family_Transport"
begin
locale native_time_transport =
  base: observer_real C D B R Bind source_order rho0 +
  newer: observer_real C D B R Bind source_order rho
  for C :: "'c set" and D :: "'d set" and B :: "'b set"
    and R :: "('c\<times>'d\<times>'b) set"
    and Bind :: "(('c\<times>'d\<times>'b)\<times>('c\<times>'d\<times>'b)) set"
    and source_order :: "('c\<times>'c) set" and rho0 rho :: "'c set set\<Rightarrow>real" +
  fixes L :: "real set"
  assumes within: "L\<subseteq>base.real_domain"
begin
definition part where "part={q\<in>base.order_domain. rho0 q\<in>L}"
definition new_time where "new_time=image rho part"
definition change where "change=rho \<circ> inv_into part rho0"
definition change_inverse where "change_inverse=rho0 \<circ> inv_into part rho"
lemma part_typed: "part\<subseteq>base.order_domain" by (auto simp: part_def)
lemma base_value_bijective: "inj_on rho0 part \<and> image rho0 part=L"
proof -
  have inj: "inj_on rho0 part" by (rule inj_on_subset[OF base.restricted_embedding_injective part_typed])
  have onto: "image rho0 part=L" using within unfolding base.real_domain_def part_def by auto
  show ?thesis using inj onto by blast
qed
lemma new_value_injective: "inj_on rho part"
  by (rule inj_on_subset[OF newer.restricted_embedding_injective part_typed])
lemma change_commutes:
  "q\<in>part \<Longrightarrow> change(rho0 q)=rho q"
  unfolding change_def comp_def by (simp only: inv_into_f_f[OF conjunct1[OF base_value_bijective]])
lemma change_identity_values:
  "t\<in>L \<Longrightarrow> rho0(inv_into part rho0 t)=t"
  using conjunct2[OF base_value_bijective] f_inv_into_f[of _ rho0 part] by auto
lemma changed_domain_contained: "new_time\<subseteq>newer.real_domain"
  unfolding new_time_def newer.real_domain_def by (rule image_mono[OF part_typed])
lemma base_inverse_typed:
  "t\<in>L \<Longrightarrow> inv_into part rho0 t\<in>part"
  using conjunct2[OF base_value_bijective] inv_into_into[of _ rho0 part] by auto
lemma new_inverse_typed:
  "t\<in>new_time \<Longrightarrow> inv_into part rho t\<in>part"
  unfolding new_time_def by (rule inv_into_into)
sublocale time: carrier_bijection L new_time change change_inverse
proof
  show "image change L\<subseteq>new_time"
    using base_inverse_typed unfolding change_def new_time_def by auto
  show "image change_inverse new_time\<subseteq>L"
    using new_inverse_typed unfolding change_inverse_def part_def by auto
  show "\<And>t. t\<in>L \<Longrightarrow> change_inverse(change t)=t"
  proof -
    fix t assume t: "t\<in>L"
    have p: "inv_into part rho0 t\<in>part" by (rule base_inverse_typed[OF t])
    show "change_inverse(change t)=t"
      unfolding change_def change_inverse_def comp_def
      using inv_into_f_f[OF new_value_injective p] change_identity_values[OF t] by simp
  qed
  show "\<And>t. t\<in>new_time \<Longrightarrow> change(change_inverse t)=t"
  proof -
    fix t assume t: "t\<in>new_time"
    have p: "inv_into part rho t\<in>part" by (rule new_inverse_typed[OF t])
    have eq: "rho(inv_into part rho t)=t" using t unfolding new_time_def by (rule f_inv_into_f)
    show "change(change_inverse t)=t"
      unfolding change_def change_inverse_def comp_def
      using inv_into_f_f[OF conjunct1[OF base_value_bijective] p] eq by simp
  qed
qed
definition transported where "transported d=law_transport.target L new_time change change_inverse d"
lemma law_transport_ready:
  "time_carrier d=L \<Longrightarrow> well_typed_family d \<Longrightarrow>
    law_transport L new_time change change_inverse d"
  by unfold_locales (fact time.forward_typed | fact time.inverse_typed |
    rule time.left_inverse | rule time.right_inverse | assumption)+
lemma native_five_conditions:
  assumes td: "time_carrier d=L" and wf: "well_typed_family d"
  shows "(K1(transported d)\<longleftrightarrow>K1 d) \<and> (K2(transported d)\<longleftrightarrow>K2 d) \<and>
    (K3(transported d)\<longleftrightarrow>K3 d) \<and> (K4(transported d)\<longleftrightarrow>K4 d) \<and>
    (K5(transported d)\<longleftrightarrow>K5 d)"
proof -
  interpret tr: law_transport L new_time change change_inverse d by (rule law_transport_ready[OF td wf])
  show ?thesis unfolding transported_def by (rule tr.five_conditions)
qed
lemma native_common_domain_image:
  assumes td: "time_carrier d=L" and wf: "well_typed_family d"
  shows "common_times(transported d)=image change(common_times d)"
proof -
  interpret tr: law_transport L new_time change change_inverse d by (rule law_transport_ready[OF td wf])
  show ?thesis unfolding transported_def by (rule tr.common_domain_image)
qed
lemma native_admissible_family_image:
  assumes td: "time_carrier d=L" and wf: "well_typed_family d"
  shows "admissible_common(transported d)Q \<longleftrightarrow>
    (\<exists>P. P\<subseteq>L \<and> admissible_common d P \<and> Q=image change P)"
proof -
  interpret tr: law_transport L new_time change change_inverse d by (rule law_transport_ready[OF td wf])
  show ?thesis unfolding transported_def by (rule tr.admissible_family_image)
qed
lemma native_evaluation_tuple:
  assumes td: "time_carrier d=L" and wf: "well_typed_family d"
    and a: "a\<in>law_indices d" and t: "t\<in>eval_times(components d a)"
  shows "((change t,input_value(components(transported d)a)(change t)),
    output_value(components(transported d)a)(change t))=
    tuple_change change((t,input_value(components d a)t),output_value(components d a)t)"
proof -
  interpret tr: law_transport L new_time change change_inverse d by (rule law_transport_ready[OF td wf])
  show ?thesis using tr.evaluation_tuple[OF a t] unfolding transported_def by simp
qed
end
definition reverse_reindex where "reverse_reindex p=\<lparr>forward_map=inverse_map p,inverse_map=forward_map p\<rparr>"
lemma inverse_image_invariance:
  assumes p: "reindex_on T p" and sub: "P\<subseteq>T"
    and inv: "image(forward_map p)P=P"
  shows "image(forward_map(reverse_reindex p))P=P \<and> (\<forall>z\<in>T. (z\<in>P\<longleftrightarrow>inverse_map p z\<in>P))"
proof -
  interpret e: carrier_bijection T T "forward_map p" "inverse_map p"
    using p unfolding carrier_bijection_def reindex_on_def by blast
  have rev: "image(inverse_map p)P=P" using e.inverse_image[OF sub] inv by simp
  have pt: "P={z\<in>T. inverse_map p z\<in>P}" using e.image_as_inverse[OF sub] inv by simp
  show ?thesis using rev pt unfolding reverse_reindex_def by auto
qed
lemma faithful_candidate_inverse:
  assumes wf: "well_typed_family d" and k4: "K4 d" and phi: "typed_reindex_family d phi"
    and allowed: "faithful_family d phi" and a: "a\<in>law_indices d"
  shows "image_invariant(components d a)(reverse_reindex(phi a)) \<and>
    (\<forall>z\<in>tuple_carrier d a. (z\<in>law_relation(components d a)\<longleftrightarrow>
      inverse_map(phi a)z\<in>law_relation(components d a)))"
proof -
  have typed: "reindex_on(tuple_carrier d a)(phi a)" using phi a unfolding typed_reindex_family_def by blast
  have sub: "law_relation(components d a)\<subseteq>tuple_carrier d a" by (rule relation_subset_tuple[OF wf a])
  have inv: "image(forward_map(phi a))(law_relation(components d a))=law_relation(components d a)"
    using k4 phi allowed a unfolding K4_def image_invariant_def by blast
  show ?thesis using inverse_image_invariance[OF typed sub inv] unfolding image_invariant_def .
qed
ML \<open>
val roots = @{thms native_time_transport.base_value_bijective native_time_transport.new_value_injective
 native_time_transport.change_commutes native_time_transport.change_identity_values native_time_transport.changed_domain_contained
 native_time_transport.native_five_conditions native_time_transport.native_common_domain_image
 native_time_transport.native_admissible_family_image native_time_transport.native_evaluation_tuple
 inverse_image_invariance faithful_candidate_inverse};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
