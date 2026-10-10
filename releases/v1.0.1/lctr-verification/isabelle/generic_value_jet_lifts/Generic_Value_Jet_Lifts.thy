theory Generic_Value_Jet_Lifts
  imports "LCTR_Polynomial_Value_Composition.Polynomial_Value_Composition"
begin

lemma native_polynomial_realizes:
  assumes v: "v\<in>jet_domain k V"
  shows "jet_curve k a v a\<in>V \<and> zjet k a (jet_curve k a v)=v"
proof -
  have vp: "v\<in>PiE {..k} (\<lambda>_. UNIV)" and v0: "v 0\<in>V"
    using v by (auto simp: jet_domain_def)
  have val0: "jet_curve k a v a = v 0"
    using zderiv_polynomial_jet[where n=0 and k=k and a=a and v=v] by simp
  have jet: "zjet k a (jet_curve k a v)=v"
    using vp by (auto simp: zjet_def restrict_def fun_eq_iff PiE_def extensional_def
      zderiv_polynomial_jet)
  show ?thesis using val0 v0 jet by simp
qed

lemma generic_lift_left_inverse:
  assumes ov: "open V" and fs: "higher_differentiable_on V f k"
    and inv: "\<forall>x\<in>V. g (f x)=x"
    and j: "value_acts k a V W f J" and h: "value_acts k a W V g K"
  shows "\<forall>v\<in>jet_domain k V. K (J v)=v"
proof (intro ballI)
  fix v assume v: "v\<in>jet_domain k V"
  let ?c = "jet_curve k a v"
  have cv: "?c a\<in>V" and cj: "zjet k a ?c=v"
    using native_polynomial_realizes[OF v] by auto
  have ck: "curve_ck_at k a ?c" by (rule jet_curve_ck)
  have fc: "curve_ck_at k a (f \<circ> ?c)"
    by (rule native_polynomial_composition_at[OF ov fs cv])
  have fw: "(f \<circ> ?c) a\<in>W" using j cv by (auto simp: value_acts_def)
  have ev: "eventually (\<lambda>x. (g \<circ> (f \<circ> ?c)) x=?c x) (nhds a)"
    using curve_eventually_in_value_chart[OF ck ov cv]
    by eventually_elim (use inv in auto)
  have je: "zjet k a (g \<circ> (f \<circ> ?c))=zjet k a ?c" by (rule zjet_germ[OF ev])
  show "K (J v)=v" using value_acts_apply[OF j ck cv] value_acts_apply[OF h fc fw] je cj
    by (simp add: o_def)
qed

lemma generic_lift_bijective:
  assumes ov: "open V" and ow: "open W"
    and fs: "higher_differentiable_on V f k" and gs: "higher_differentiable_on W g k"
    and li: "\<forall>x\<in>V. g (f x)=x" and ri: "\<forall>y\<in>W. f (g y)=y"
    and j: "value_acts k a V W f J" and h: "value_acts k a W V g K"
  shows "bij_betw J (jet_domain k V) (jet_domain k W)"
proof -
  have l: "\<forall>v\<in>jet_domain k V. K (J v)=v"
    by (rule generic_lift_left_inverse[OF ov fs li j h])
  have r: "\<forall>w\<in>jet_domain k W. J (K w)=w"
    by (rule generic_lift_left_inverse[OF ow gs ri h j])
  show ?thesis by (rule bij_betw_byWitness[where f=J and f'=K, OF l r])
    (use j h in \<open>auto simp: value_acts_def\<close>)
qed

lemma generic_lift_composition:
  assumes ov: "open V" and fs: "higher_differentiable_on V f k"
    and j: "value_acts k a V W f J" and kk: "value_acts k a W Z g K"
    and hh: "value_acts k a V Z (g \<circ> f) H"
  shows "\<forall>v\<in>jet_domain k V. (K \<circ> J) v=H v"
proof (intro ballI)
  fix v assume v: "v\<in>jet_domain k V"
  let ?c = "jet_curve k a v"
  have cv: "?c a\<in>V" and cj: "zjet k a ?c=v"
    using native_polynomial_realizes[OF v] by auto
  have ck: "curve_ck_at k a ?c" by (rule jet_curve_ck)
  have fc: "curve_ck_at k a (f \<circ> ?c)"
    by (rule native_polynomial_composition_at[OF ov fs cv])
  have fw: "(f \<circ> ?c) a\<in>W" using j cv by (auto simp: value_acts_def)
  show "(K \<circ> J) v=H v"
    using value_acts_apply[OF j ck cv] value_acts_apply[OF kk fc fw]
      value_acts_apply[OF hh ck cv] cj by (simp add: o_def)
qed

lemma generic_value_jet_relation_image:
  assumes ov: "open V" and ow: "open W"
    and fs: "higher_differentiable_on V f k" and gs: "higher_differentiable_on W g k"
    and li: "\<forall>x\<in>V. g (f x)=x" and ri: "\<forall>y\<in>W. f (g y)=y"
    and j: "value_acts k a V W f J" and h: "value_acts k a W V g K"
    and src: "Rel\<subseteq>jet_domain k V" and dst: "Target\<subseteq>jet_domain k W"
    and cov: "\<forall>v\<in>jet_domain k V. v\<in>Rel \<longleftrightarrow> J v\<in>Target"
  shows "image J Rel=Target"
proof -
  have onto: "image J (jet_domain k V)=jet_domain k W"
    using generic_lift_bijective[OF ov ow fs gs li ri j h] by (simp add: bij_betw_def)
  show ?thesis by (rule Value_Jet_Lift_Algebra.relation_image[OF onto src dst cov])
qed

ML \<open>
val roots = @{thms native_polynomial_realizes generic_lift_left_inverse generic_lift_bijective
  generic_lift_composition generic_value_jet_relation_image};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
