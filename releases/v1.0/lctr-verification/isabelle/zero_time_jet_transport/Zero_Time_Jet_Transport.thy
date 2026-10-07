theory Zero_Time_Jet_Transport
  imports "LCTR_Value_Jet_Lift_Algebra.Value_Jet_Lift_Algebra"
    "LCTR_Core_Time_Jet_Changes.Core_Time_Jet_Changes"
begin

definition zero_time_acts where
  "zero_time_acts k a b V g J \<longleftrightarrow> g b=a \<and>
    J ` jet_domain k V \<subseteq> jet_domain k V \<and>
    (\<forall>c. curve_ck_at k a c \<longrightarrow> c a\<in>V \<longrightarrow>
      J (zjet k a c)=zjet k b (c \<circ> g))"

definition time_jet_map where
  "time_jet_map f J = (\<lambda>(a,v). (f a,J a v))"

lemma time_action_zero_completion_exact:
  assumes gb: "g b=a" and gs: "curve_ck_at k b g"
  shows "zero_time_acts k a b V g J \<longleftrightarrow> time_acts k a b V g J"
proof -
  have action: "(J (zjet k a c)=zjet k b (c \<circ> g)) \<longleftrightarrow>
      (J (jet k a c)=jet k b (c \<circ> g))" if ck: "curve_ck_at k a c" for c
  proof -
    have ck': "curve_ck_at k (g b) c" using ck gb by simp
    have cg: "curve_ck_at k b (c \<circ> g)" by (rule curve_ck_comp[OF ck' gs])
    show ?thesis by (simp only: curve_ck_zjet_agrees[OF ck] curve_ck_zjet_agrees[OF cg])
  qed
  show ?thesis unfolding zero_time_acts_def time_acts_def using action by blast
qed

lemma time_jet_zeroth_preserved:
  assumes act: "zero_time_acts k a b V g J" and v: "v\<in>jet_domain k V"
  shows "J v 0=v 0"
proof -
  obtain c where c: "curve_ck_at k a c" "c a\<in>V" "zjet k a c=v"
    by (rule zjet_domain_realization[OF v])
  have eq: "J (zjet k a c)=zjet k b (c \<circ> g)" and gb: "g b=a"
    using act c(1,2) unfolding zero_time_acts_def by blast+
  have v0: "c a=v 0" using fun_cong[OF c(3), of 0] by (simp only: zjet_zeroth)
  show ?thesis using eq c(3) by (simp add: zjet_zeroth gb v0)
qed

lemma time_jet_map_bijective:
  assumes ou: "open U" and ow: "open W"
    and fm: "f ` U\<subseteq>W" and gm: "g ` W\<subseteq>U"
    and fs: "higher_differentiable_on U f k" and gs: "higher_differentiable_on W g k"
    and li: "\<forall>x\<in>U. g (f x)=x" and ri: "\<forall>y\<in>W. f (g y)=y"
    and j: "\<forall>a\<in>U. zero_time_acts k a (f a) V g (J a)"
    and h: "\<forall>a\<in>U. zero_time_acts k (f a) a V f (K (f a))"
  shows "bij_betw (time_jet_map f J) (U\<times>jet_domain k V) (W\<times>jet_domain k V)"
proof -
  have oldj: "time_acts k a (f a) V g (J a)" if a: "a\<in>U" for a
  proof -
    have fa: "f a\<in>W" using fm a by blast
    have ga: "g (f a)=a" using li a by blast
    have gc: "curve_ck_at k (f a) g" by (rule curve_ck_on_at[OF ow fa gs])
    show ?thesis using time_action_zero_completion_exact[OF ga gc] j a by blast
  qed
  have oldh: "time_acts k (f a) a V f (K (f a))" if a: "a\<in>U" for a
  proof -
    have fc: "curve_ck_at k a f" by (rule curve_ck_on_at[OF ou a fs])
    show ?thesis using time_action_zero_completion_exact[OF refl fc] h a by blast
  qed
  show ?thesis unfolding time_jet_map_def
    by (rule time_jet_full_domain_bijective[where K=K and J=J, OF ou ow fm gm fs gs li ri])
      (use oldj oldh in blast)+
qed

lemma time_jet_relation_image:
  assumes bij: "bij_betw (time_jet_map f J) (U\<times>jet_domain k V) (W\<times>jet_domain k V)"
    and ax: "A\<subseteq>U\<times>jet_domain k V" and by_: "B\<subseteq>W\<times>jet_domain k V"
    and cov: "\<forall>p\<in>U\<times>jet_domain k V. p\<in>A \<longleftrightarrow> time_jet_map f J p\<in>B"
  shows "time_jet_map f J ` A=B"
proof -
  have onto: "time_jet_map f J ` (U\<times>jet_domain k V)=W\<times>jet_domain k V"
    using bij by (simp add: bij_betw_def)
  show ?thesis by (rule Value_Jet_Lift_Algebra.relation_image[OF onto ax by_ cov])
qed

lemma time_native_zeroth_preserved:
  assumes act: "zero_time_acts k a (f a) V g (J a)"
    and d: "atlas_curve a\<in>V" and agreement: "extension a=atlas_curve a"
  shows "snd (time_jet_map f J (a,zjet k a extension)) 0=atlas_curve a"
proof -
  have typed: "zjet k a extension\<in>jet_domain k V"
    by (rule zjet_in_domain) (simp only: agreement d)
  show ?thesis using time_jet_zeroth_preserved[OF act typed]
    by (simp add: time_jet_map_def zjet_zeroth agreement)
qed

lemma time_native_membership_preserved:
  assumes image: "time_jet_map f J ` A=B"
    and member: "\<forall>t\<in>N. (t,zjet k t extension)\<in>A"
  shows "time_jet_map f J ` A=B \<and>
    (\<forall>t\<in>N. time_jet_map f J (t,zjet k t extension)\<in>B)"
  using assms by blast

ML \<open>
val roots = @{thms time_action_zero_completion_exact time_jet_zeroth_preserved
  time_jet_map_bijective time_jet_relation_image time_native_zeroth_preserved time_native_membership_preserved};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
