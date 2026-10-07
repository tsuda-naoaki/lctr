theory Core_Tagged_Lifts
  imports Main
begin

definition tag_lift where "tag_lift v f p = (v, f (snd p))"

lemma tag_lift_value: "tag_lift v f (u,x) = (v,f x)"
  by (simp add: tag_lift_def)

lemma tag_lift_image: "tag_lift v f ` ({u} \<times> A) = {v} \<times> (f ` A)"
  by (force simp: tag_lift_def)

lemma tag_lift_injective:
  "inj_on f A \<Longrightarrow> inj_on (tag_lift v f) ({u} \<times> A)"
  unfolding inj_on_def tag_lift_def by auto

lemma tag_lift_composition:
  "tag_lift w g (tag_lift v f p) = tag_lift w (g \<circ> f) p"
  by (simp add: tag_lift_def)

lemma tag_lift_inverse:
  assumes inj: "inj_on f A" and y: "y \<in> f ` A"
  shows "inv_into ({u} \<times> A) (tag_lift v f) (v,y) =
    tag_lift u (inv_into A f) (v,y)"
proof -
  obtain x where x: "x \<in> A" "y = f x" using y by blast
  have tagged_inj: "inj_on (tag_lift v f) ({u} \<times> A)"
    by (rule tag_lift_injective[OF inj])
  have member: "(u,x) \<in> {u} \<times> A" using x by simp
  have inverse: "inv_into ({u} \<times> A) (tag_lift v f) (tag_lift v f (u,x)) = (u,x)"
    by (rule inv_into_f_f[OF tagged_inj member])
  show ?thesis using inverse x inv_into_f_f[OF inj x(1)] by (simp add: tag_lift_def)
qed

lemma tag_lift_left_identity:
  "inj_on f A \<Longrightarrow> p \<in> {u} \<times> A \<Longrightarrow>
   tag_lift u (inv_into A f) (tag_lift v f p) = p"
  by (auto simp: tag_lift_def)

lemma tag_lift_right_identity:
  "p \<in> {v} \<times> (f ` A) \<Longrightarrow>
   tag_lift v f (tag_lift u (inv_into A f) p) = p"
  by (auto simp: tag_lift_def f_inv_into_f)

lemma inverse_graph_exact:
  assumes inj: "inj_on f A"
  shows "{(p,inv_into ({u} \<times> A) (tag_lift v f) p) |p. p \<in> {v} \<times> (f ` A)} =
    {(p,tag_lift u (inv_into A f) p) |p. p \<in> {v} \<times> (f ` A)}"
  using tag_lift_inverse[OF inj, where u=u and v=v] by auto

lemma equal_value_distinct_tags: "u \<noteq> v \<Longrightarrow> (u,x) \<noteq> (v,x)"
  by simp

ML \<open>
val roots = @{thms tag_lift_value tag_lift_image tag_lift_injective tag_lift_composition
  tag_lift_inverse tag_lift_left_identity tag_lift_right_identity inverse_graph_exact
  equal_value_distinct_tags};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int (length roots));
\<close>
end
