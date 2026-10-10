theory Generic_Value_Change
  imports "LCTR_Generic_Value_Jet_Lifts.Generic_Value_Jet_Lifts"
    "LCTR_Native_Value_Change.Native_Value_Change"
begin

lemma generic_value_map_bijective:
  assumes valid: "value_change_valid k U V W f g J K"
  shows "bij_betw (value_jet_map J) (U\<times>jet_domain k V) (U\<times>jet_domain k W)"
proof -
  have fibers: "bij_betw (J a) (jet_domain k V) (jet_domain k W)" if "a\<in>U" for a
    by (rule generic_lift_bijective[where f=f and g=g and K="K a"])
      (use valid that in \<open>auto simp: value_change_valid_def\<close>)
  have base: "bij_betw id U U" by simp
  show ?thesis using base_and_fiber_bijective[OF base, of J "jet_domain k V" "jet_domain k W"]
    fibers by (simp add: value_jet_map_def)
qed

lemma generic_value_relation_image:
  assumes valid: "value_change_valid k U V W f g J K"
    and src: "Rel\<subseteq>U\<times>jet_domain k V" and dst: "Target\<subseteq>U\<times>jet_domain k W"
    and cov: "\<forall>p\<in>U\<times>jet_domain k V. p\<in>Rel \<longleftrightarrow> value_jet_map J p\<in>Target"
  shows "image (value_jet_map J) Rel=Target"
  by (rule value_relation_image_from_bijection[OF generic_value_map_bijective[OF valid] src dst cov])

definition bound_value_change where
  "bound_value_change k U C D c d f g J K \<longleftrightarrow>
    value_change_valid k U (actual_overlap_image C D c) (actual_overlap_image D C d) f g J K \<and>
    (\<forall>x\<in>actual_overlap_image C D c. f x=actual_chart_change C D c d x) \<and>
    (\<forall>x\<in>actual_overlap_image D C d. g x=actual_chart_change D C d c x)"

lemma bound_value_relation_image:
  assumes bound: "bound_value_change k U C D c d f g J K"
    and src: "Rel\<subseteq>U\<times>jet_domain k (actual_overlap_image C D c)"
    and dst: "Target\<subseteq>U\<times>jet_domain k (actual_overlap_image D C d)"
    and cov: "\<forall>p\<in>U\<times>jet_domain k (actual_overlap_image C D c).
      p\<in>Rel \<longleftrightarrow> value_jet_map J p\<in>Target"
  shows "image (value_jet_map J) Rel=Target"
proof -
  have valid: "value_change_valid k U (actual_overlap_image C D c) (actual_overlap_image D C d) f g J K"
    using bound by (simp add: bound_value_change_def)
  show ?thesis by (rule generic_value_relation_image[OF valid src dst cov])
qed

ML \<open>
val roots = @{thms generic_value_map_bijective generic_value_relation_image bound_value_relation_image};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
