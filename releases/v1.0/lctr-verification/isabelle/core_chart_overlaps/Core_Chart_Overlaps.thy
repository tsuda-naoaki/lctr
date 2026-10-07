theory Core_Chart_Overlaps
  imports "LCTR_Core_Time_Jet_Changes.Core_Time_Jet_Changes"
    "LCTR_Core_Representation_Images.Core_Representation_Images"
begin

locale coordinate_overlaps =
  fixes X :: "'a set" and Y :: "'b set" and h :: "'a\<Rightarrow>'b"
    and D :: "'a set" and E :: "'b set" and U V :: "real set"
    and c :: "'a\<Rightarrow>real" and d :: "'b\<Rightarrow>real"
  assumes hb: "bij_betw h X Y" and dx: "D\<subseteq>X" and ey: "E\<subseteq>Y"
    and cb: "bij_betw c D U" and db: "bij_betw d E V"
begin
abbreviation hinv where "hinv \<equiv> inv_into X h"
definition source_overlap where "source_overlap = {x\<in>D. h x\<in>E}"
definition target_overlap where "target_overlap = {y\<in>E. hinv y\<in>D}"
definition source_coordinate_domain where "source_coordinate_domain = c ` source_overlap"
definition target_coordinate_domain where "target_coordinate_domain = d ` target_overlap"
definition chart_map where "chart_map a = d (h (inv_into source_overlap c a))"
definition chart_inverse where "chart_inverse b = c (hinv (inv_into target_overlap d b))"

lemma coordinate_injective: "inj_on c D"
  using cb by (simp add: bij_betw_def)
lemma target_coordinate_injective: "inj_on d E"
  using db by (simp add: bij_betw_def)
lemma source_inj: "inj_on c source_overlap"
  by (rule inj_on_subset[OF coordinate_injective]) (auto simp: source_overlap_def)
lemma target_inj: "inj_on d target_overlap"
  by (rule inj_on_subset[OF target_coordinate_injective]) (auto simp: target_overlap_def)

lemma coordinate_domain_formula:
  "source_coordinate_domain = {a. \<exists>x\<in>D. h x\<in>E \<and> c x=a}"
  by (auto simp: source_coordinate_domain_def source_overlap_def)

lemma overlap_forward:
  assumes x: "x\<in>source_overlap"
  shows "h x\<in>target_overlap" "hinv (h x)=x"
proof -
  have xd: "x\<in>D" and he: "h x\<in>E" using x by (auto simp: source_overlap_def)
  have xx: "x\<in>X" using xd dx by blast
  show eq: "hinv (h x)=x" by (rule bij_betw_inv_into_left[OF hb xx])
  show "h x\<in>target_overlap" by (simp add: target_overlap_def he eq xd)
qed

lemma overlap_backward:
  assumes y: "y\<in>target_overlap"
  shows "hinv y\<in>source_overlap" "h (hinv y)=y"
proof -
  have ye: "y\<in>E" and gd: "hinv y\<in>D" using y by (auto simp: target_overlap_def)
  have yy: "y\<in>Y" using ye ey by blast
  show eq: "h (hinv y)=y" by (rule bij_betw_inv_into_right[OF hb yy])
  show "hinv y\<in>source_overlap" by (simp add: source_overlap_def gd eq ye)
qed

lemma source_back:
  "a\<in>source_coordinate_domain \<Longrightarrow> inv_into source_overlap c a\<in>source_overlap"
  unfolding source_coordinate_domain_def by (rule inv_into_into)
lemma target_back:
  "b\<in>target_coordinate_domain \<Longrightarrow> inv_into target_overlap d b\<in>target_overlap"
  unfolding target_coordinate_domain_def by (rule inv_into_into)

lemma chart_forward_formula:
  "x\<in>source_overlap \<Longrightarrow> chart_map (c x)=d (h x)"
  by (simp add: chart_map_def inv_into_f_f[OF source_inj])

lemma chart_commutes:
  assumes a: "a\<in>source_coordinate_domain"
  shows "h (inv_into source_overlap c a) = inv_into target_overlap d (chart_map a)"
proof -
  have x: "h (inv_into source_overlap c a)\<in>target_overlap"
    by (rule overlap_forward(1)[OF source_back[OF a]])
  show ?thesis by (simp add: chart_map_def inv_into_f_f[OF target_inj x])
qed

lemma chart_map_maps:
  "chart_map ` source_coordinate_domain\<subseteq>target_coordinate_domain"
  using overlap_forward(1) source_back
  by (auto simp: chart_map_def target_coordinate_domain_def)
lemma chart_inverse_maps:
  "chart_inverse ` target_coordinate_domain\<subseteq>source_coordinate_domain"
  using overlap_backward(1) target_back
  by (auto simp: chart_inverse_def source_coordinate_domain_def)

lemma chart_map_left_inverse:
  assumes a: "a\<in>source_coordinate_domain"
  shows "chart_inverse (chart_map a)=a"
proof -
  have x: "inv_into source_overlap c a\<in>source_overlap" by (rule source_back[OF a])
  have hc: "hinv (h (inv_into source_overlap c a))=inv_into source_overlap c a"
    by (rule overlap_forward(2)[OF x])
  have ca: "c (inv_into source_overlap c a)=a"
    using a by (simp add: source_coordinate_domain_def f_inv_into_f)
  show ?thesis using chart_commutes[OF a] hc ca unfolding chart_inverse_def by simp
qed

lemma chart_map_right_inverse:
  assumes b: "b\<in>target_coordinate_domain"
  shows "chart_map (chart_inverse b)=b"
proof -
  have y: "inv_into target_overlap d b\<in>target_overlap" by (rule target_back[OF b])
  have x: "hinv (inv_into target_overlap d b)\<in>source_overlap" by (rule overlap_backward(1)[OF y])
  have hy: "h (hinv (inv_into target_overlap d b))=inv_into target_overlap d b"
    by (rule overlap_backward(2)[OF y])
  have dbb: "d (inv_into target_overlap d b)=b"
    using b by (simp add: target_coordinate_domain_def f_inv_into_f)
  show ?thesis
    by (simp add: chart_inverse_def chart_forward_formula[OF x] hy dbb)
qed

lemma chart_bijection:
  "bij_betw chart_map source_coordinate_domain target_coordinate_domain"
  by (rule bij_betw_byWitness[where f'=chart_inverse])
    (auto intro: chart_map_left_inverse chart_map_right_inverse
      simp: chart_map_maps chart_inverse_maps)
end

definition real_extension :: "real set \<Rightarrow> (real\<Rightarrow>real) \<Rightarrow> real\<Rightarrow>real" where
  "real_extension U e a = (if a\<in>U then e a else 0)"

lemma realExtension_on_domain: "a\<in>U \<Longrightarrow> real_extension U e a=e a"
  by (simp add: real_extension_def)

lemma realExtension_maps:
  "bij_betw e U W \<Longrightarrow> real_extension U e ` U\<subseteq>W"
  by (auto simp: bij_betw_def real_extension_def)

lemma realExtension_inverse:
  assumes e: "bij_betw e U W" and a: "a\<in>U"
  shows "real_extension W (inv_into U e) (real_extension U e a)=a"
proof -
  have ea: "e a\<in>W" using e a by (auto simp: bij_betw_def)
  show ?thesis using bij_betw_inv_into_left[OF e a]
    by (simp add: real_extension_def a ea)
qed

lemma base_eq_coordinate_equiv:
  "forward=real_extension U e \<Longrightarrow> a\<in>U \<Longrightarrow> forward a=e a"
  by (simp add: real_extension_def)

lemma time_change_of_equiv:
  assumes e: "bij_betw e U W" and ou: "open U" and ow: "open W"
    and fs: "higher_differentiable_on U (real_extension U e) k"
    and gs: "higher_differentiable_on W (real_extension W (inv_into U e)) k"
    and j: "\<forall>a\<in>U. time_acts k a (real_extension U e a) V (real_extension W (inv_into U e)) (J a)"
    and h: "\<forall>a\<in>U. time_acts k (real_extension U e a) a V (real_extension U e) (K (real_extension U e a))"
  shows "bij_betw (\<lambda>(a,v). (real_extension U e a,J a v))
    (U\<times>jet_domain k V) (W\<times>jet_domain k V)"
proof -
  have fm: "real_extension U e ` U\<subseteq>W" by (rule realExtension_maps[OF e])
  have gm: "real_extension W (inv_into U e) ` W\<subseteq>U"
    by (rule realExtension_maps[OF bij_betw_inv_into[OF e]])
  have li: "\<forall>a\<in>U. real_extension W (inv_into U e) (real_extension U e a)=a"
    using realExtension_inverse[OF e] by blast
  have ri: "real_extension U e (real_extension W (inv_into U e) b)=b" if b: "b\<in>W" for b
  proof -
    have bi: "b\<in>e`U" using e b by (simp add: bij_betw_def)
    have bu: "inv_into U e b\<in>U" by (rule inv_into_into[OF bi])
    show ?thesis by (simp add: real_extension_def b bu f_inv_into_f[OF bi])
  qed
  show ?thesis
    by (rule time_jet_full_domain_bijective[OF ou ow fm gm fs gs li _ j h]) (use ri in blast)
qed

locale time_image_coordinate_overlaps = representation_images A f g
  for A :: "'a set" and f g :: "'a\<Rightarrow>real" +
  fixes D E U V :: "real set" and c d :: "real\<Rightarrow>real"
  assumes dx: "D\<subseteq>f`A" and ey: "E\<subseteq>g`A"
    and cb: "bij_betw c D U" and db: "bij_betw d E V"
begin
sublocale C: coordinate_overlaps "f`A" "g`A" F D E U V c d
  by standard (rule image_map_bijective, rule dx, rule ey, rule cb, rule db)

lemma chart_link_for_time_images:
  "a\<in>C.source_coordinate_domain \<Longrightarrow>
    F (inv_into C.source_overlap c a) = inv_into C.target_overlap d (C.chart_map a)"
  by (rule C.chart_commutes)
end

lemma restricted_relation_image:
  assumes e: "bij_betw e U V" and a: "A\<subseteq>U" and b: "B\<subseteq>V"
    and cov: "\<forall>x\<in>U. x\<in>A \<longleftrightarrow> e x\<in>B"
  shows "e ` A=B"
proof (rule set_eqI, rule iffI)
  fix y assume "y\<in>e`A"
  then obtain x where x: "x\<in>A" "e x=y" by blast
  have xu: "x\<in>U" using a x(1) by blast
  show "y\<in>B" using cov xu x by blast
next
  fix y assume y: "y\<in>B"
  have yv: "y\<in>V" using b y by blast
  have onto: "e`U=V" using e by (simp add: bij_betw_def)
  have yi: "y\<in>e`U" using yv by (simp only: onto)
  obtain x where x: "x\<in>U" "e x=y" using yi by (auto simp only: image_iff)
  have xa: "x\<in>A" using cov x y by blast
  show "y\<in>e`A" by (rule image_eqI[where x=x]) (use x(2) xa in auto)
qed

lemma ambient_restriction_image:
  assumes e: "bij_betw e U V" and cov: "\<forall>x\<in>U. x\<in>R \<longleftrightarrow> e x\<in>S"
  shows "e ` (R\<inter>U)=S\<inter>V"
proof -
  have maps: "e x\<in>V" if "x\<in>U" for x
    using e that by (auto simp: bij_betw_def)
  have c: "\<forall>x\<in>U. x\<in>R\<inter>U \<longleftrightarrow> e x\<in>S\<inter>V"
    using cov maps by auto
  show ?thesis by (rule restricted_relation_image[OF e _ _ c]) auto
qed

ML \<open>
val roots = @{thms coordinate_overlaps.coordinate_injective coordinate_overlaps.coordinate_domain_formula
  coordinate_overlaps.chart_commutes coordinate_overlaps.chart_forward_formula realExtension_on_domain
  realExtension_maps realExtension_inverse base_eq_coordinate_equiv
  time_image_coordinate_overlaps.chart_link_for_time_images restricted_relation_image ambient_restriction_image};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
