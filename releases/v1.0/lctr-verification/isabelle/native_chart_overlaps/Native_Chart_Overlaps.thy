theory Native_Chart_Overlaps
  imports "LCTR_Native_Time_Change.Native_Time_Change"
begin

definition actual_overlap_image where "actual_overlap_image C D c = c ` (C \<inter> D)"
definition actual_chart_change where
  "actual_chart_change C D c d = d \<circ> inv_into (C \<inter> D) c"

locale actual_chart_overlaps =
  fixes C D :: "'x set" and V :: "'e set" and W :: "'f set"
    and c :: "'x \<Rightarrow> 'e" and d :: "'x \<Rightarrow> 'f"
  assumes cb: "bij_betw c C V" and db: "bij_betw d D W"
begin

lemma overlap_value_injective: "inj_on c (C \<inter> D)"
  using cb by (auto simp: bij_betw_def intro: inj_on_subset)

lemma overlap_image_formula:
  "actual_overlap_image C D c = {v. \<exists>x\<in>C. x\<in>D \<and> c x=v}"
  by (auto simp: actual_overlap_image_def)

lemma overlap_image_in_target: "actual_overlap_image C D c \<subseteq> V"
  using cb by (auto simp: actual_overlap_image_def bij_betw_def)

lemma chart_change_formula:
  "x\<in>C\<inter>D \<Longrightarrow> actual_chart_change C D c d (c x)=d x"
  by (simp add: actual_chart_change_def inv_into_f_f[OF overlap_value_injective])

lemma chart_change_inverse:
  assumes v: "v\<in>actual_overlap_image C D c"
  shows "actual_chart_change D C d c (actual_chart_change C D c d v)=v"
proof -
  obtain x where x: "x\<in>C\<inter>D" "v=c x"
    using v by (auto simp: actual_overlap_image_def)
  have di: "inj_on d (D\<inter>C)"
    using db by (auto simp: bij_betw_def intro: inj_on_subset)
  have dx: "x\<in>D\<inter>C" using x by blast
  show ?thesis using chart_change_formula[OF x(1)] x(2)
    by (simp add: actual_chart_change_def inv_into_f_f[OF di dx])
qed

lemma chart_change_bijective:
  "bij_betw (actual_chart_change C D c d)
    (actual_overlap_image C D c) (actual_overlap_image D C d)"
proof -
  interpret other: actual_chart_overlaps D C W V d c
    by (unfold_locales; use db cb in auto)
  have maps: "actual_chart_change C D c d ` actual_overlap_image C D c
      \<subseteq>actual_overlap_image D C d"
    using chart_change_formula by (auto simp: actual_overlap_image_def)
  have backward_maps: "actual_chart_change D C d c ` actual_overlap_image D C d
      \<subseteq>actual_overlap_image C D c"
    using other.chart_change_formula by (auto simp: actual_overlap_image_def)
  show ?thesis
    by (rule bij_betw_byWitness[where f'="actual_chart_change D C d c"])
      (use chart_change_inverse other.chart_change_inverse maps backward_maps in auto)
qed

lemma value_change_from_actual_charts:
  assumes exact: "\<forall>v\<in>actual_overlap_image C D c. f v=actual_chart_change C D c d v"
    and x: "x\<in>C\<inter>D"
  shows "f (c x)=d x"
  using exact chart_change_formula[OF x] x by (auto simp: actual_overlap_image_def)

lemmas time_change_from_actual_charts = value_change_from_actual_charts
end

definition bound_time_change where
  "bound_time_change k V C D c d f g J K \<longleftrightarrow>
    time_change_valid k V (actual_overlap_image C D c) (actual_overlap_image D C d) f g J K \<and>
    (\<forall>x\<in>actual_overlap_image C D c. f x=actual_chart_change C D c d x) \<and>
    (\<forall>x\<in>actual_overlap_image D C d. g x=actual_chart_change D C d c x)"

lemma bound_time_relation_image:
  assumes bound: "bound_time_change k V C D c d f g J K"
    and src: "Rel\<subseteq>actual_overlap_image C D c\<times>jet_domain k V"
    and dst: "Target\<subseteq>actual_overlap_image D C d\<times>jet_domain k V"
    and cov: "\<forall>p\<in>actual_overlap_image C D c\<times>jet_domain k V.
      p\<in>Rel \<longleftrightarrow> time_jet_map f J p\<in>Target"
  shows "time_jet_map f J ` Rel=Target"
proof -
  have valid: "time_change_valid k V (actual_overlap_image C D c) (actual_overlap_image D C d) f g J K"
    using bound by (simp add: bound_time_change_def)
  show ?thesis by (rule time_change_relation_image[OF valid src dst cov])
qed

definition product_chart_region where "product_chart_region V W = V\<times>W"

lemma product_chart_bijective:
  "bij_betw c C V \<Longrightarrow> bij_betw d D W \<Longrightarrow>
    bij_betw (map_prod c d) (C\<times>D) (product_chart_region V W)"
  unfolding product_chart_region_def by (rule bij_betw_map_prod)

lemma product_chart_region: "product_chart_region V W=V\<times>W"
  by (simp add: product_chart_region_def)

context coordinate_atlas
begin
lemma product_chart_at_generated_values:
  assumes i: "i\<in>Charts" and x: "x\<in>joint i"
  shows "map_prod (ic i) (oc i) (fin x,fout x)=curve i (tc i x)"
  using coordinate_curve_generated[OF i x] by (simp add: source_values_def)
end

ML \<open>
val roots = @{thms actual_chart_overlaps.overlap_value_injective
  actual_chart_overlaps.overlap_image_formula actual_chart_overlaps.overlap_image_in_target
  actual_chart_overlaps.chart_change_formula actual_chart_overlaps.chart_change_bijective
  actual_chart_overlaps.chart_change_inverse actual_chart_overlaps.value_change_from_actual_charts
  actual_chart_overlaps.time_change_from_actual_charts bound_time_relation_image
  product_chart_bijective product_chart_region coordinate_atlas.product_chart_at_generated_values};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
