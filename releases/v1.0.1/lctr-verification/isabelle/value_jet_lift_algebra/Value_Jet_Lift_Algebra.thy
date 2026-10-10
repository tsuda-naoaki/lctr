theory Value_Jet_Lift_Algebra
  imports "LCTR_Zero_Completed_Jet_Germs.Zero_Completed_Jet_Germs"
begin

definition value_acts where
  "value_acts k a V W f J \<longleftrightarrow> f ` V \<subseteq> W \<and>
    J ` jet_domain k V \<subseteq> jet_domain k W \<and>
    (\<forall>c. curve_ck_at k a c \<longrightarrow> c a\<in>V \<longrightarrow>
      J (zjet k a c) = zjet k a (f \<circ> c))"

definition preserves_ck_curves where
  "preserves_ck_curves k a V f \<longleftrightarrow>
    (\<forall>c. curve_ck_at k a c \<longrightarrow> c a\<in>V \<longrightarrow> curve_ck_at k a (f \<circ> c))"

lemma value_acts_apply:
  "value_acts k a V W f J \<Longrightarrow> curve_ck_at k a c \<Longrightarrow> c a\<in>V \<Longrightarrow>
    J (zjet k a c) = zjet k a (f \<circ> c)"
  unfolding value_acts_def by blast

lemma lift_unique:
  assumes j: "value_acts k a V W f J" and h: "value_acts k a V W f K"
  shows "\<forall>v\<in>jet_domain k V. J v=K v"
proof (intro ballI)
  fix v assume v: "v\<in>jet_domain k V"
  obtain c where c: "curve_ck_at k a c" "c a\<in>V" "zjet k a c=v"
    by (rule zjet_domain_realization[OF v])
  show "J v=K v" using value_acts_apply[OF j c(1,2)] value_acts_apply[OF h c(1,2)] c(3) by simp
qed

lemma lift_identity:
  assumes j: "value_acts k a V V id J"
  shows "\<forall>v\<in>jet_domain k V. J v=v"
proof (intro ballI)
  fix v assume v: "v\<in>jet_domain k V"
  obtain c where c: "curve_ck_at k a c" "c a\<in>V" "zjet k a c=v"
    by (rule zjet_domain_realization[OF v])
  show "J v=v" using value_acts_apply[OF j c(1,2)] c(3) by simp
qed

lemma curve_eventually_in_value_chart:
  assumes ck: "curve_ck_at k a c" and V: "open V" "c a\<in>V"
  shows "eventually (\<lambda>x. c x\<in>V) (nhds a)"
proof -
  obtain S where S: "open S" "a\<in>S" "higher_differentiable_on S c k"
    using ck unfolding curve_ck_at_def by blast
  have cs: "continuous_on S c" by (rule higher_differentiable_on_imp_continuous_on[OF S(3)])
  have op: "open (S \<inter> c -` V)"
    using continuous_on_open_vimage[OF S(1), of c] cs V(1) by (simp add: Int_commute)
  have ain: "a\<in>S \<inter> c -` V" using S(2) V(2) by simp
  show ?thesis using eventually_nhds_in_open[OF op ain] by eventually_elim auto
qed

lemma lift_left_inverse_from_curve_preservation:
  assumes ov: "open V" and fs: "preserves_ck_curves k a V f"
    and inv: "\<forall>x\<in>V. g (f x)=x"
    and j: "value_acts k a V W f J" and h: "value_acts k a W V g K"
  shows "\<forall>v\<in>jet_domain k V. K (J v)=v"
proof (intro ballI)
  fix v assume v: "v\<in>jet_domain k V"
  obtain c where c: "curve_ck_at k a c" "c a\<in>V" "zjet k a c=v"
    by (rule zjet_domain_realization[OF v])
  have fcs: "curve_ck_at k a (f \<circ> c)" using fs c(1,2) unfolding preserves_ck_curves_def by blast
  have fcw: "(f \<circ> c) a\<in>W" using j c(2) unfolding value_acts_def by auto
  have ev: "eventually (\<lambda>x. (g \<circ> (f \<circ> c)) x=c x) (nhds a)"
    using curve_eventually_in_value_chart[OF c(1) ov c(2)]
    by eventually_elim (use inv in auto)
  have jet_eq: "zjet k a (g \<circ> (f \<circ> c))=zjet k a c" by (rule zjet_germ[OF ev])
  show "K (J v)=v" using value_acts_apply[OF j c(1,2)] value_acts_apply[OF h fcs fcw] jet_eq c(3) by (simp add: o_def)
qed

lemma lift_bijective_from_curve_preservation:
  assumes ov: "open V" and ow: "open W"
    and fs: "preserves_ck_curves k a V f" and gs: "preserves_ck_curves k a W g"
    and li: "\<forall>x\<in>V. g (f x)=x" and ri: "\<forall>y\<in>W. f (g y)=y"
    and j: "value_acts k a V W f J" and h: "value_acts k a W V g K"
  shows "bij_betw J (jet_domain k V) (jet_domain k W)"
proof -
  have l: "\<forall>v\<in>jet_domain k V. K (J v)=v"
    by (rule lift_left_inverse_from_curve_preservation[OF ov fs li j h])
  have r: "\<forall>w\<in>jet_domain k W. J (K w)=w"
    by (rule lift_left_inverse_from_curve_preservation[OF ow gs ri h j])
  show ?thesis by (rule bij_betw_byWitness[where f=J and f'=K, OF l r])
    (use j h in \<open>auto simp: value_acts_def\<close>)
qed

lemma lift_composition_from_curve_preservation:
  assumes fs: "preserves_ck_curves k a V f"
    and j: "value_acts k a V W f J" and kk: "value_acts k a W Z g K"
    and hh: "value_acts k a V Z (g \<circ> f) H"
  shows "\<forall>v\<in>jet_domain k V. (K \<circ> J) v=H v"
proof (intro ballI)
  fix v assume v: "v\<in>jet_domain k V"
  obtain c where c: "curve_ck_at k a c" "c a\<in>V" "zjet k a c=v"
    by (rule zjet_domain_realization[OF v])
  have fcs: "curve_ck_at k a (f \<circ> c)" using fs c(1,2) unfolding preserves_ck_curves_def by blast
  have fcw: "(f \<circ> c) a\<in>W" using j c(2) unfolding value_acts_def by auto
  show "(K \<circ> J) v=H v"
    using value_acts_apply[OF j c(1,2)] value_acts_apply[OF kk fcs fcw]
      value_acts_apply[OF hh c(1,2)] c(3) by (simp add: o_def)
qed

lemma relation_image:
  assumes onto: "J ` X=Y" and ax: "A\<subseteq>X" and by_: "B\<subseteq>Y"
    and cov: "\<forall>x\<in>X. x\<in>A \<longleftrightarrow> J x\<in>B"
  shows "J ` A=B"
proof (rule set_eqI, rule iffI)
  fix y assume "y\<in>J ` A"
  then obtain x where x: "x\<in>A" "J x=y" by blast
  have "x\<in>X" using ax x(1) by blast
  then show "y\<in>B" using cov x by blast
next
  fix y assume y: "y\<in>B"
  have "y\<in>Y" using by_ y by blast
  then obtain x where x: "x\<in>X" "J x=y" using onto by blast
  have "x\<in>A" using cov x y by blast
  then show "y\<in>J ` A" using x(2) by blast
qed

lemma euclidean_value_map_preserves_curves:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes V: "open V" and fs: "higher_differentiable_on V f k"
  shows "preserves_ck_curves k a V f"
  unfolding preserves_ck_curves_def
proof (intro allI impI)
  fix c assume ck: "curve_ck_at k a c" and cv: "c a\<in>V"
  obtain S where S: "open S" "a\<in>S" "higher_differentiable_on S c k"
    using ck unfolding curve_ck_at_def by blast
  have cs: "continuous_on S c" by (rule higher_differentiable_on_imp_continuous_on[OF S(3)])
  have op: "open (S \<inter> c -` V)"
    using continuous_on_open_vimage[OF S(1), of c] cs V by (simp add: Int_commute)
  have cr: "higher_differentiable_on (S \<inter> c -` V) c k"
    by (rule higher_differentiable_on_subset[OF S(3)]) auto
  have fc: "higher_differentiable_on (S \<inter> c -` V) (f \<circ> c) k"
    by (rule higher_differentiable_on_compose[OF fs cr _ op V]) auto
  show "curve_ck_at k a (f \<circ> c)" unfolding curve_ck_at_def
    by (intro exI[of _ "S \<inter> c -` V"] conjI op fc) (use S(2) cv in auto)
qed

ML \<open>
val roots = @{thms lift_unique lift_identity curve_eventually_in_value_chart
  lift_left_inverse_from_curve_preservation lift_bijective_from_curve_preservation
  lift_composition_from_curve_preservation relation_image euclidean_value_map_preserves_curves};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
