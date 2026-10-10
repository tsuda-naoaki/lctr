theory Core_Law_Family_Transport
  imports Core_Law_Transport
begin
context carrier_bijection
begin
lemma tuple_bijection:
  "carrier_bijection ((T\<times>X)\<times>Y) ((U\<times>X)\<times>Y) (tuple_change f) (tuple_change g)"
  using forward_typed inverse_typed left_inverse right_inverse
  unfolding carrier_bijection_def tuple_change_def by auto
end
context law_transport
begin
definition conjugated where "conjugated phi a=conjugate_reindex (tuple_change f) (tuple_change g) (phi a)"
definition conjugates where
  "conjugates phi psi \<longleftrightarrow> (\<forall>a\<in>law_indices d. \<forall>z\<in>(U\<times>input_carrier d a)\<times>output_carrier d a.
    forward_map(psi a)z=forward_map(conjugated phi a)z \<and>
    inverse_map(psi a)z=inverse_map(conjugated phi a)z)"
definition target where
  "target=\<lparr>time_carrier=U, law_indices=law_indices d, input_carrier=input_carrier d,
    output_carrier=output_carrier d, components=(\<lambda>a. component_transport f g (old a)),
    admissible_common=(\<lambda>Q. \<exists>P. P\<subseteq>T \<and> admissible_common d P \<and> Q=image f P),
    faithful_family=(\<lambda>psi. \<exists>phi. typed_reindex_family d phi \<and> faithful_family d phi \<and> conjugates phi psi)\<rparr>"
lemma selectors [simp]:
  "time_carrier target=U" "law_indices target=law_indices d"
  "input_carrier target=input_carrier d" "output_carrier target=output_carrier d"
  "components target a=moved a"
  by (simp_all add: target_def)
lemma target_relation_typed:
  assumes a: "a\<in>law_indices d"
  shows "law_relation(moved a)\<subseteq>(U\<times>input_carrier d a)\<times>output_carrier d a"
  using component_bounds(3)[OF a] forward_typed
  by (auto simp: component_transport_def tuple_change_def; blast)
lemma conjugated_family_typed:
  assumes phi: "typed_reindex_family d phi"
  shows "typed_reindex_family target (conjugated phi)"
  unfolding typed_reindex_family_def
proof (simp only: selectors; intro ballI)
  fix a assume a: "a\<in>law_indices d"
  interpret ev: carrier_bijection "((T\<times>input_carrier d a)\<times>output_carrier d a)"
    "((U\<times>input_carrier d a)\<times>output_carrier d a)" "tuple_change f" "tuple_change g"
    by (rule tuple_bijection)
  have old: "reindex_on ((T\<times>input_carrier d a)\<times>output_carrier d a) (phi a)"
    using phi a unfolding typed_reindex_family_def tuple_carrier_def source_time by blast
  show "reindex_on (tuple_carrier target a) (conjugated phi a)"
    using ev.conjugate_typed[OF old] unfolding tuple_carrier_def conjugated_def by simp
qed
lemma conjugated_invariance:
  assumes a: "a\<in>law_indices d" and phi: "typed_reindex_family d phi"
  shows "image_invariant(moved a)(conjugated phi a)\<longleftrightarrow>image_invariant(old a)(phi a)"
proof -
  interpret ev: carrier_bijection "((T\<times>input_carrier d a)\<times>output_carrier d a)"
    "((U\<times>input_carrier d a)\<times>output_carrier d a)" "tuple_change f" "tuple_change g"
    by (rule tuple_bijection)
  have old: "reindex_on ((T\<times>input_carrier d a)\<times>output_carrier d a) (phi a)"
    using phi a unfolding typed_reindex_family_def tuple_carrier_def source_time by blast
  show ?thesis
    using ev.conjugate_invariance[OF old component_bounds(3)[OF a]]
    unfolding image_invariant_def component_transport_def conjugated_def by simp
qed
lemma conjugates_invariance:
  assumes a: "a\<in>law_indices d" and eq: "conjugates phi psi"
  shows "image_invariant(moved a)(psi a)=image_invariant(moved a)(conjugated phi a)"
proof -
  have maps: "\<And>z. z\<in>law_relation(moved a) \<Longrightarrow> forward_map(psi a)z=forward_map(conjugated phi a)z"
    using eq a target_relation_typed[OF a] unfolding conjugates_def by blast
  have "image(forward_map(psi a))(law_relation(moved a))=
    image(forward_map(conjugated phi a))(law_relation(moved a))"
    by (rule image_cong[OF refl maps])
  then show ?thesis unfolding image_invariant_def by simp
qed
lemma condition1: "K1 target\<longleftrightarrow>K1 d"
  unfolding K1_def using condition1_component by auto
lemma condition2: "K2 target\<longleftrightarrow>K2 d"
  unfolding K2_def using condition2_component by auto
lemma condition3: "K3 target\<longleftrightarrow>K3 d"
  unfolding K3_def using condition1 generated_component by auto
lemma condition4: "K4 target\<longleftrightarrow>K4 d"
proof
  assume h: "K4 target"
  show "K4 d" unfolding K4_def
  proof (intro allI impI ballI)
    fix phi a
    assume phi: "typed_reindex_family d phi" and permitted: "faithful_family d phi"
      and a: "a\<in>law_indices d"
    have ct: "typed_reindex_family target(conjugated phi)" by (rule conjugated_family_typed[OF phi])
    have allowed: "faithful_family target(conjugated phi)"
      using phi permitted unfolding target_def conjugates_def by auto
    have inv: "image_invariant(moved a)(conjugated phi a)"
      using h ct allowed a unfolding K4_def by auto
    show "image_invariant(old a)(phi a)" using conjugated_invariance[OF a phi] inv by simp
  qed
next
  assume h: "K4 d"
  show "K4 target" unfolding K4_def
  proof (intro allI impI ballI)
    fix psi a
    assume psi: "typed_reindex_family target psi" and permitted: "faithful_family target psi"
      and a: "a\<in>law_indices target"
    have ai: "a\<in>law_indices d" using a by simp
    obtain phi where phi: "typed_reindex_family d phi" and old: "faithful_family d phi"
      and eq: "conjugates phi psi" using permitted unfolding target_def by auto
    have inv: "image_invariant(old a)(phi a)" using h phi old ai unfolding K4_def by blast
    show "image_invariant(components target a)(psi a)"
      using conjugates_invariance[OF ai eq] conjugated_invariance[OF ai phi] inv by simp
  qed
qed
lemma common_domain_image: "common_times target=image f(common_times d)"
proof -
  have valid: "\<And>a. a\<in>law_indices d \<Longrightarrow>
    valid_times(moved a)={u\<in>U. g u\<in>valid_times(old a)}"
  proof -
    fix a assume a: "a\<in>law_indices d"
    have sub: "valid_times(old a)\<subseteq>T"
      using component_bounds(1)[OF a] unfolding valid_times_def by auto
    show "valid_times(moved a)={u\<in>U. g u\<in>valid_times(old a)}"
      unfolding valid_times_image[OF a] by (rule image_as_inverse[OF sub])
  qed
  have source: "common_times d\<subseteq>T" unfolding common_times_def source_time by auto
  show ?thesis unfolding image_as_inverse[OF source]
    using valid inverse_typed unfolding common_times_def source_time by auto
qed
lemma admissible_family_image:
  "admissible_common target Q \<longleftrightarrow> (\<exists>P. P\<subseteq>T \<and> admissible_common d P \<and> Q=image f P)"
  by (simp add: target_def)
lemma condition5: "K5 target\<longleftrightarrow>K5 d"
proof -
  have source: "common_times d\<subseteq>T" unfolding common_times_def source_time by auto
  have allowed: "admissible_common target(common_times target)=admissible_common d(common_times d)"
    unfolding admissible_family_image common_domain_image
    using image_injective source by blast
  show ?thesis by (simp only: K5_def condition3 allowed; simp only: common_domain_image image_is_empty)
qed
lemma five_conditions:
  "(K1 target\<longleftrightarrow>K1 d) \<and> (K2 target\<longleftrightarrow>K2 d) \<and>
   (K3 target\<longleftrightarrow>K3 d) \<and> (K4 target\<longleftrightarrow>K4 d) \<and> (K5 target\<longleftrightarrow>K5 d)"
  using condition1 condition2 condition3 condition4 condition5 by blast
end
ML \<open>
val roots = @{thms law_transport.conjugated_family_typed law_transport.conjugated_invariance
 law_transport.condition1 law_transport.condition2 law_transport.condition3 law_transport.condition4
 law_transport.common_domain_image law_transport.admissible_family_image law_transport.condition5 law_transport.five_conditions};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
