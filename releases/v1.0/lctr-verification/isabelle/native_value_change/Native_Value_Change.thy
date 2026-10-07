theory Native_Value_Change
  imports "LCTR_Native_Chart_Overlaps.Native_Chart_Overlaps"
    "LCTR_Finite_Directional_Value_Jets.Finite_Directional_Value_Jets"
begin

definition value_change_valid where
  "value_change_valid k U V W f g J K \<longleftrightarrow>
    open V \<and> open W \<and> f ` V\<subseteq>W \<and> g ` W\<subseteq>V \<and>
    higher_differentiable_on V f k \<and> higher_differentiable_on W g k \<and>
    (\<forall>x\<in>V. g (f x)=x) \<and> (\<forall>y\<in>W. f (g y)=y) \<and>
    (\<forall>a\<in>U. value_acts k a V W f (J a)) \<and>
    (\<forall>a\<in>U. value_acts k a W V g (K a))"

definition value_jet_map where "value_jet_map J = (\<lambda>(a,v). (a,J a v))"

lemma preserves_time_coordinate: "fst (value_jet_map J p)=fst p"
  by (cases p) (simp add: value_jet_map_def)

lemma finite_value_map_bijective:
  fixes f :: "'e::euclidean_space \<Rightarrow> 'f::euclidean_space"
  assumes valid: "value_change_valid k U V W f g J K"
  shows "bij_betw (value_jet_map J) (U\<times>jet_domain k V) (U\<times>jet_domain k W)"
proof -
  have fibers: "bij_betw (J a) (jet_domain k V) (jet_domain k W)" if "a\<in>U" for a
    by (rule finite_lift_bijective[where f=f and g=g and K="K a"])
      (use valid that in \<open>auto simp: value_change_valid_def\<close>)
  have base: "bij_betw id U U" by simp
  show ?thesis using base_and_fiber_bijective[OF base, of J "jet_domain k V" "jet_domain k W"]
    fibers by (simp add: value_jet_map_def)
qed

lemma trivial_value_map_bijective:
  fixes f :: "'e::real_normed_vector \<Rightarrow> 'f::real_normed_vector"
  assumes trivial: "(\<forall>x::'e. x=0) \<or> (\<forall>y::'f. y=0)"
    and valid: "value_change_valid k U V W f g J K"
  shows "bij_betw (value_jet_map J) (U\<times>jet_domain k V) (U\<times>jet_domain k W)"
proof -
  have fibers: "bij_betw (J a) (jet_domain k V) (jet_domain k W)" if "a\<in>U" for a
    by (rule trivial_endpoint_lift_bijective[where f=f and g=g and K="K a", OF trivial])
      (use valid that in \<open>auto simp: value_change_valid_def\<close>)
  have base: "bij_betw id U U" by simp
  show ?thesis using base_and_fiber_bijective[OF base, of J "jet_domain k V" "jet_domain k W"]
    fibers by (simp add: value_jet_map_def)
qed

lemma value_relation_image_from_bijection:
  assumes bij: "bij_betw (value_jet_map J) (U\<times>jet_domain k V) (U\<times>jet_domain k W)"
    and src: "Rel\<subseteq>U\<times>jet_domain k V" and dst: "Target\<subseteq>U\<times>jet_domain k W"
    and cov: "\<forall>p\<in>U\<times>jet_domain k V. p\<in>Rel \<longleftrightarrow> value_jet_map J p\<in>Target"
  shows "value_jet_map J ` Rel=Target"
proof -
  have onto: "value_jet_map J ` (U\<times>jet_domain k V)=U\<times>jet_domain k W"
    using bij by (simp add: bij_betw_def)
  show ?thesis by (rule Value_Jet_Lift_Algebra.relation_image[OF onto src dst cov])
qed

lemma finite_value_relation_image:
  fixes f :: "'e::euclidean_space \<Rightarrow> 'f::euclidean_space"
  assumes valid: "value_change_valid k U V W f g J K"
    and src: "Rel\<subseteq>U\<times>jet_domain k V" and dst: "Target\<subseteq>U\<times>jet_domain k W"
    and cov: "\<forall>p\<in>U\<times>jet_domain k V. p\<in>Rel \<longleftrightarrow> value_jet_map J p\<in>Target"
  shows "value_jet_map J ` Rel=Target"
  by (rule value_relation_image_from_bijection[OF finite_value_map_bijective[OF valid] src dst cov])

lemma trivial_value_relation_image:
  fixes f :: "'e::real_normed_vector \<Rightarrow> 'f::real_normed_vector"
  assumes trivial: "(\<forall>x::'e. x=0) \<or> (\<forall>y::'f. y=0)"
    and valid: "value_change_valid k U V W f g J K"
    and src: "Rel\<subseteq>U\<times>jet_domain k V" and dst: "Target\<subseteq>U\<times>jet_domain k W"
    and cov: "\<forall>p\<in>U\<times>jet_domain k V. p\<in>Rel \<longleftrightarrow> value_jet_map J p\<in>Target"
  shows "value_jet_map J ` Rel=Target"
  by (rule value_relation_image_from_bijection[OF trivial_value_map_bijective[OF trivial valid] src dst cov])

lemma value_action_same_on_chart:
  assumes ov: "open V" and eq: "\<forall>x\<in>V. f x=g x"
    and j: "value_acts k a V W f J" and h: "value_acts k a V W g K"
  shows "\<forall>v\<in>jet_domain k V. J v=K v"
proof (intro ballI)
  fix v assume v: "v\<in>jet_domain k V"
  obtain c where c: "curve_ck_at k a c" "c a\<in>V" "zjet k a c=v"
    by (rule zjet_domain_realization[OF v])
  have ev: "eventually (\<lambda>x. (f \<circ> c) x=(g \<circ> c) x) (nhds a)"
    using curve_eventually_in_value_chart[OF c(1) ov c(2)]
    by eventually_elim (use eq in auto)
  have jets: "zjet k a (f \<circ> c)=zjet k a (g \<circ> c)" by (rule zjet_germ[OF ev])
  show "J v=K v" using value_acts_apply[OF j c(1,2)] value_acts_apply[OF h c(1,2)] c(3) jets by simp
qed

lemma value_map_same_on_chart:
  assumes v: "value_change_valid k U V W f g J K"
    and w: "value_change_valid k U V W h l P Q"
    and eq: "\<forall>x\<in>V. f x=h x"
  shows "\<forall>p\<in>U\<times>jet_domain k V. value_jet_map J p=value_jet_map P p"
proof -
  have maps: "J a z=P a z" if a: "a\<in>U" and z: "z\<in>jet_domain k V" for a z
  proof -
    have op: "open V" and jf: "value_acts k a V W f (J a)" and ph: "value_acts k a V W h (P a)"
      using v w a by (auto simp: value_change_valid_def)
    show ?thesis using value_action_same_on_chart[OF op eq jf ph] z by blast
  qed
  show ?thesis using maps by (auto simp: value_jet_map_def)
qed

ML \<open>
val roots = @{thms preserves_time_coordinate finite_value_map_bijective trivial_value_map_bijective
  value_relation_image_from_bijection finite_value_relation_image trivial_value_relation_image
  value_action_same_on_chart value_map_same_on_chart};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
