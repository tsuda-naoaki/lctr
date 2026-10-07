theory Tagged_Lifts_Alignment
  imports "LCTR_Core_Tagged_Lifts.Core_Tagged_Lifts"
begin




lemma alignment_tagLift_value:
  "tag_lift v f p = (v, f (snd p))"
  by (simp add: tag_lift_def)
lemma alignment_tagLift_inverse:
  assumes inj: "inj_on f A"
  shows "\<forall>p\<in>{v}\<times>(f ` A).
    inv_into ({u}\<times>A) (tag_lift v f) p = tag_lift u (inv_into A f) p"
  using tag_lift_inverse[OF inj, where u=u and v=v] by auto
lemma alignment_tagLift_left_inverse:
  "inj_on f A \<Longrightarrow> p\<in>{u}\<times>A \<Longrightarrow>
    tag_lift u (inv_into A f) (tag_lift v f p)=p"
  by (rule tag_lift_left_identity)
lemma alignment_tagLift_right_inverse:
  "p\<in>{v}\<times>(f ` A) \<Longrightarrow>
    tag_lift v f (tag_lift u (inv_into A f) p)=p"
  by (rule tag_lift_right_identity)
lemma alignment_tagLift_injective:
  "inj_on f A \<Longrightarrow> inj_on (tag_lift v f) ({u}\<times>A)"
  by (rule tag_lift_injective)
lemma alignment_tagLift_composition:
  "tag_lift w g \<circ> tag_lift v f = tag_lift w (g \<circ> f)"
  by (rule ext) (simp add: tag_lift_composition)

lemma alignment_partialLift_value:
  "fst (tag_lift v f p)=v \<and> snd (tag_lift v f p)=f (snd p)"
  by (simp add: tag_lift_def)
lemma alignment_partialLift_inverse_value:
  assumes inj: "inj_on f A" and p: "p\<in>{v}\<times>(f ` A)"
  shows "inv_into ({u}\<times>A) (tag_lift v f) p = (u, inv_into A f (snd p))"
proof -
  have eq: "inv_into ({u}\<times>A) (tag_lift v f) p = tag_lift u (inv_into A f) p"
    using alignment_tagLift_inverse[OF inj, where u=u and v=v] p by blast
  show ?thesis by (simp only: eq tag_lift_def)
qed
lemma alignment_partialLift_inverse:
  "inj_on f A \<Longrightarrow>
   {(p,inv_into ({u}\<times>A) (tag_lift v f) p) |p. p\<in>{v}\<times>(f ` A)} =
   {(p,tag_lift u (inv_into A f) p) |p. p\<in>{v}\<times>(f ` A)}"
  by (rule inverse_graph_exact)
lemma alignment_partialLift_both_identities:
  assumes inj: "inj_on f A"
  shows "(\<forall>p\<in>{u}\<times>A. tag_lift u (inv_into A f) (tag_lift v f p)=p) \<and>
    (\<forall>p\<in>{v}\<times>(f ` A). tag_lift v f (tag_lift u (inv_into A f) p)=p)"
  using tag_lift_left_identity[OF inj, where u=u and v=v]
    tag_lift_right_identity[where u=u and v=v and f=f and A=A] by blast
lemma alignment_equal_value_different_tags:
  "u\<noteq>v \<Longrightarrow> (u,x)\<noteq>(v,x)"
  by (rule equal_value_distinct_tags)

lemma tagged_lift_exact_bijection:
  "inj_on f A \<Longrightarrow> bij_betw (tag_lift v f) ({u}\<times>A) ({v}\<times>(f ` A))"
  unfolding bij_betw_def
  by (intro conjI) (rule tag_lift_injective, assumption, rule tag_lift_image)
lemma inverse_typed:
  "p\<in>{v}\<times>(f ` A) \<Longrightarrow> tag_lift u (inv_into A f) p\<in>{u}\<times>A"
  by (auto simp: tag_lift_def inv_into_into)
lemma inverse_agrees_with_supplied:
  assumes left: "\<forall>x\<in>A. g (f x)=x" and y: "y\<in>f ` A"
  shows "g y=inv_into A f y"
proof -
  have inj: "inj_on f A" using left unfolding inj_on_def by metis
  obtain x where x: "x\<in>A" "y=f x" using y by blast
  show ?thesis using left x inv_into_f_f[OF inj x(1)] by simp
qed

ML \<open>
val roots = @{thms alignment_tagLift_value alignment_tagLift_inverse
  alignment_tagLift_left_inverse alignment_tagLift_right_inverse
  alignment_tagLift_injective alignment_tagLift_composition alignment_partialLift_value
  alignment_partialLift_inverse_value alignment_partialLift_inverse
  alignment_partialLift_both_identities alignment_equal_value_different_tags};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
