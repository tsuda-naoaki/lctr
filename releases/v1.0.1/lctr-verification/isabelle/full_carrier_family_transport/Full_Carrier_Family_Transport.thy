theory Full_Carrier_Family_Transport
  imports "LCTR_Full_Carrier_Component_Transport.Full_Carrier_Component_Transport"
begin

locale full_family_encoding = tm: carrier_bijection T U ft gt
  for T :: "'t set" and U :: "'u set" and ft :: "'t\<Rightarrow>'u" and gt :: "'u\<Rightarrow>'t" +
  fixes d :: "('t,'a,'x,'y) law_family"
    and V :: "'a\<Rightarrow>'v set" and W :: "'a\<Rightarrow>'w set"
    and fx :: "'a\<Rightarrow>'x\<Rightarrow>'v" and gx :: "'a\<Rightarrow>'v\<Rightarrow>'x"
    and fy :: "'a\<Rightarrow>'y\<Rightarrow>'w" and gy :: "'a\<Rightarrow>'w\<Rightarrow>'y"
  assumes source_time: "time_carrier d=T" and wf: "well_typed_family d"
    and input_encoding: "\<And>a. a\<in>law_indices d \<Longrightarrow>
      carrier_bijection (input_carrier d a) (V a) (fx a) (gx a)"
    and output_encoding: "\<And>a. a\<in>law_indices d \<Longrightarrow>
      carrier_bijection (output_carrier d a) (W a) (fy a) (gy a)"
begin

abbreviation old where "old a \<equiv> components d a"
abbreviation moved where "moved a \<equiv> full_component_transport ft gt (fx a) (fy a) (old a)"
abbreviation tuple_forward where "tuple_forward a \<equiv> map_prod (map_prod ft (fx a)) (fy a)"
abbreviation tuple_backward where "tuple_backward a \<equiv> map_prod (map_prod gt (gx a)) (gy a)"

lemma component_encoding:
  assumes a: "a\<in>law_indices d"
  shows "full_component_encoding T U ft gt (input_carrier d a) (V a) (fx a) (gx a)
    (output_carrier d a) (W a) (fy a) (gy a) (old a)"
  using tm.carrier_bijection_axioms input_encoding[OF a] output_encoding[OF a] wf a
  unfolding full_component_encoding_def full_component_encoding_axioms_def
    well_typed_family_def source_time by auto

definition conjugated where
  "conjugated phi a=conjugate_reindex (tuple_forward a) (tuple_backward a) (phi a)"
definition conjugates where
  "conjugates phi psi \<longleftrightarrow> (\<forall>a\<in>law_indices d. \<forall>z\<in>(U\<times>V a)\<times>W a.
    forward_map(psi a)z=forward_map(conjugated phi a)z \<and>
    inverse_map(psi a)z=inverse_map(conjugated phi a)z)"
definition encoded where
  "encoded=\<lparr>time_carrier=U, law_indices=law_indices d, input_carrier=V, output_carrier=W,
    components=moved,
    admissible_common=(\<lambda>Q. \<exists>P. P\<subseteq>T \<and> admissible_common d P \<and> Q=ft ` P),
    faithful_family=(\<lambda>psi. \<exists>phi. typed_reindex_family d phi \<and>
      faithful_family d phi \<and> conjugates phi psi)\<rparr>"

lemma selectors [simp]:
  "time_carrier encoded=U" "law_indices encoded=law_indices d"
  "input_carrier encoded=V" "output_carrier encoded=W"
  "components encoded a=moved a"
  by (simp_all add: encoded_def)

lemma component_results:
  assumes a: "a\<in>law_indices d"
  shows "individual_admissible(moved a)\<longleftrightarrow>individual_admissible(old a)"
    and "right_unique(moved a)\<longleftrightarrow>right_unique(old a)"
    and "generated_member(moved a)\<longleftrightarrow>generated_member(old a)"
    and "valid_times(moved a)=ft ` valid_times(old a)"
proof -
  interpret c: full_component_encoding T U ft gt "input_carrier d a" "V a" "fx a" "gx a"
    "output_carrier d a" "W a" "fy a" "gy a" "old a"
    by (rule component_encoding[OF a])
  show "individual_admissible(moved a)\<longleftrightarrow>individual_admissible(old a)" by (rule c.individual_admissibility)
  show "right_unique(moved a)\<longleftrightarrow>right_unique(old a)" by (rule c.right_uniqueness)
  show "generated_member(moved a)\<longleftrightarrow>generated_member(old a)" by (rule c.generated_membership)
  show "valid_times(moved a)=ft ` valid_times(old a)" by (rule c.valid_times_image)
qed

lemma conjugated_family_typed:
  assumes phi: "typed_reindex_family d phi"
  shows "typed_reindex_family encoded (conjugated phi)"
  unfolding typed_reindex_family_def
proof (simp only: selectors; intro ballI)
  fix a assume a: "a\<in>law_indices d"
  interpret c: full_component_encoding T U ft gt "input_carrier d a" "V a" "fx a" "gx a"
    "output_carrier d a" "W a" "fy a" "gy a" "old a"
    by (rule component_encoding[OF a])
  have p: "reindex_on ((T\<times>input_carrier d a)\<times>output_carrier d a) (phi a)"
    using phi a unfolding typed_reindex_family_def tuple_carrier_def source_time by blast
  show "reindex_on (tuple_carrier encoded a) (conjugated phi a)"
    using c.reindex_transport[OF p] by (simp add: tuple_carrier_def conjugated_def)
qed

lemma conjugated_invariance:
  assumes a: "a\<in>law_indices d" and phi: "typed_reindex_family d phi"
  shows "image_invariant(moved a)(conjugated phi a)\<longleftrightarrow>image_invariant(old a)(phi a)"
proof -
  interpret c: full_component_encoding T U ft gt "input_carrier d a" "V a" "fx a" "gx a"
    "output_carrier d a" "W a" "fy a" "gy a" "old a"
    by (rule component_encoding[OF a])
  have p: "reindex_on ((T\<times>input_carrier d a)\<times>output_carrier d a) (phi a)"
    using phi a unfolding typed_reindex_family_def tuple_carrier_def source_time by blast
  show ?thesis using c.invariant_transport[OF p] by (simp only: conjugated_def)
qed

lemma conjugates_invariance:
  assumes a: "a\<in>law_indices d" and eq: "conjugates phi psi"
  shows "image_invariant(moved a)(psi a)=image_invariant(moved a)(conjugated phi a)"
proof -
  interpret c: full_component_encoding T U ft gt "input_carrier d a" "V a" "fx a" "gx a"
    "output_carrier d a" "W a" "fy a" "gy a" "old a"
    by (rule component_encoding[OF a])
  have typed: "law_relation(moved a)\<subseteq>(U\<times>V a)\<times>W a"
    using c.moved_bounds(4,5) by auto
  have same: "\<And>z. z\<in>law_relation(moved a) \<Longrightarrow>
      forward_map(psi a)z=forward_map(conjugated phi a)z"
    using eq a typed unfolding conjugates_def by blast
  have "forward_map(psi a) ` law_relation(moved a)=forward_map(conjugated phi a) ` law_relation(moved a)"
    by (rule image_cong[OF refl same])
  then show ?thesis unfolding image_invariant_def by simp
qed

lemma condition1: "K1 encoded\<longleftrightarrow>K1 d"
  unfolding K1_def using component_results(1) by auto
lemma condition2: "K2 encoded\<longleftrightarrow>K2 d"
  unfolding K2_def using component_results(2) by auto
lemma condition3: "K3 encoded\<longleftrightarrow>K3 d"
  unfolding K3_def using condition1 component_results(3) by auto

lemma condition4: "K4 encoded\<longleftrightarrow>K4 d"
proof
  assume h: "K4 encoded"
  show "K4 d" unfolding K4_def
  proof (intro allI impI ballI)
    fix phi a
    assume phi: "typed_reindex_family d phi" and faithful: "faithful_family d phi" and a: "a\<in>law_indices d"
    have ct: "typed_reindex_family encoded(conjugated phi)" by (rule conjugated_family_typed[OF phi])
    have cf: "faithful_family encoded(conjugated phi)"
      using phi faithful unfolding encoded_def conjugates_def by auto
    have inv: "image_invariant(moved a)(conjugated phi a)"
      using h ct cf a unfolding K4_def by auto
    show "image_invariant(old a)(phi a)" using inv conjugated_invariance[OF a phi] by simp
  qed
next
  assume h: "K4 d"
  show "K4 encoded" unfolding K4_def
  proof (intro allI impI ballI)
    fix psi a
    assume psi: "typed_reindex_family encoded psi" and faithful: "faithful_family encoded psi"
      and a: "a\<in>law_indices encoded"
    have ai: "a\<in>law_indices d" using a by simp
    obtain phi where phi: "typed_reindex_family d phi" and pf: "faithful_family d phi"
      and eq: "conjugates phi psi" using faithful unfolding encoded_def by auto
    have inv: "image_invariant(old a)(phi a)" using h phi pf ai unfolding K4_def by blast
    show "image_invariant(components encoded a)(psi a)"
      using inv conjugates_invariance[OF ai eq] conjugated_invariance[OF ai phi] by simp
  qed
qed

lemma common_times_image: "common_times encoded=ft ` common_times d"
proof -
  have valid: "\<And>a. a\<in>law_indices d \<Longrightarrow>
      valid_times(moved a)={u\<in>U. gt u\<in>valid_times(old a)}"
  proof -
    fix a assume a: "a\<in>law_indices d"
    have sub: "valid_times(old a)\<subseteq>T"
      using wf a unfolding valid_times_def well_typed_family_def source_time by auto
    show "valid_times(moved a)={u\<in>U. gt u\<in>valid_times(old a)}"
      unfolding component_results(4)[OF a] by (rule tm.image_as_inverse[OF sub])
  qed
  have sub: "common_times d\<subseteq>T" unfolding common_times_def source_time by auto
  show ?thesis unfolding tm.image_as_inverse[OF sub]
    using valid tm.inverse_typed unfolding common_times_def source_time by auto
qed

lemma admissible_image:
  "admissible_common encoded Q \<longleftrightarrow>
    (\<exists>P. P\<subseteq>T \<and> admissible_common d P \<and> Q=ft ` P)"
  by (simp add: encoded_def)

lemma condition5: "K5 encoded\<longleftrightarrow>K5 d"
proof -
  have sub: "common_times d\<subseteq>T" unfolding common_times_def source_time by auto
  have allowed: "admissible_common encoded(common_times encoded)=admissible_common d(common_times d)"
  proof
    assume h: "admissible_common encoded(common_times encoded)"
    obtain P where P: "P\<subseteq>T" "admissible_common d P" "ft ` common_times d=ft ` P"
      using h by (simp only: admissible_image common_times_image; blast)
    have eq: "common_times d=P" using tm.image_injective[OF sub P(1)] P(3) by simp
    show "admissible_common d(common_times d)" using P(2) by (simp only: eq)
  next
    assume h: "admissible_common d(common_times d)"
    show "admissible_common encoded(common_times encoded)"
      unfolding admissible_image common_times_image
      by (rule exI[where x="common_times d"]; simp only: sub h; simp)
  qed
  show ?thesis by (simp only: K5_def condition3 allowed; simp only: common_times_image image_is_empty)
qed

lemma five_conditions:
  "(K1 encoded\<longleftrightarrow>K1 d) \<and> (K2 encoded\<longleftrightarrow>K2 d) \<and>
   (K3 encoded\<longleftrightarrow>K3 d) \<and> (K4 encoded\<longleftrightarrow>K4 d) \<and>
   (K5 encoded\<longleftrightarrow>K5 d)"
  using condition1 condition2 condition3 condition4 condition5 by blast

lemma all_conditions_preserved: "all_conditions encoded\<longleftrightarrow>all_conditions d"
  by (simp only: all_conditions_def condition1 condition2 condition3 condition4 condition5)

lemma encoded_well_typed: "well_typed_family encoded"
proof -
  have ne: "law_indices encoded\<noteq>{}" using wf unfolding well_typed_family_def by simp
  have bounds: "\<And>a. a\<in>law_indices d \<Longrightarrow>
    eval_times(moved a)\<subseteq>U \<and>
    input_value(moved a) ` eval_times(moved a)\<subseteq>V a \<and>
    output_value(moved a) ` eval_times(moved a)\<subseteq>W a \<and>
    eval_domain(moved a)\<subseteq>U\<times>V a \<and>
    law_relation(moved a)\<subseteq>eval_domain(moved a)\<times>W a"
  proof -
    fix a assume a: "a\<in>law_indices d"
    interpret c: full_component_encoding T U ft gt "input_carrier d a" "V a" "fx a" "gx a"
      "output_carrier d a" "W a" "fy a" "gy a" "old a"
      by (rule component_encoding[OF a])
    show "eval_times(moved a)\<subseteq>U \<and>
      input_value(moved a) ` eval_times(moved a)\<subseteq>V a \<and>
      output_value(moved a) ` eval_times(moved a)\<subseteq>W a \<and>
      eval_domain(moved a)\<subseteq>U\<times>V a \<and>
      law_relation(moved a)\<subseteq>eval_domain(moved a)\<times>W a"
      using c.moved_bounds by blast
  qed
  have ext: "\<And>f g. same_reindex_family encoded f g \<Longrightarrow>
    faithful_family encoded f \<longleftrightarrow> faithful_family encoded g"
  proof -
    fix f g :: "'a\<Rightarrow>(('u\<times>'v)\<times>'w) carrier_reindex"
    assume same: "same_reindex_family encoded f g"
    have eq: "\<And>phi. conjugates phi f \<longleftrightarrow> conjugates phi g"
      using same unfolding same_reindex_family_def tuple_carrier_def conjugates_def by auto
    show "faithful_family encoded f \<longleftrightarrow> faithful_family encoded g"
      by (simp only: encoded_def law_family.select_convs eq)
  qed
  show ?thesis unfolding well_typed_family_def using ne bounds ext by auto
qed

end

ML \<open>
val roots = @{thms full_family_encoding.component_encoding full_family_encoding.component_results
 full_family_encoding.conjugated_family_typed full_family_encoding.conjugated_invariance
 full_family_encoding.condition1 full_family_encoding.condition2 full_family_encoding.condition3
 full_family_encoding.condition4 full_family_encoding.common_times_image full_family_encoding.condition5
 full_family_encoding.five_conditions full_family_encoding.all_conditions_preserved
 full_family_encoding.encoded_well_typed};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
