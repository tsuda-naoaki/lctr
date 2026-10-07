theory Presentation_Fiber_Admissibility
  imports LCTR_Dynamics_Refinement_Alignment.Dynamics_Refinement_Alignment
    LCTR_Presentation_Fiber_Transport.Presentation_Fiber_Transport
begin

lemma fiber_constancy_iff:
  assumes typed: "E\<subseteq>C\<times>C"
  shows "(\<forall>x y. (x,y)\<in>E \<longrightarrow> q x=q y) \<longleftrightarrow>
    (\<forall>x y. (x,y)\<in>E \<longrightarrow> fiber_encode C q (q x)=fiber_encode C q (q y))"
proof
  assume "\<forall>x y. (x,y)\<in>E \<longrightarrow> q x=q y"
  then show "\<forall>x y. (x,y)\<in>E \<longrightarrow> fiber_encode C q (q x)=fiber_encode C q (q y)"
    by metis
next
  assume a: "\<forall>x y. (x,y)\<in>E \<longrightarrow> fiber_encode C q (q x)=fiber_encode C q (q y)"
  show "\<forall>x y. (x,y)\<in>E \<longrightarrow> q x=q y"
  proof (intro allI impI)
    fix x y assume e: "(x,y)\<in>E"
    have x: "x\<in>C" and y: "y\<in>C" using typed e by auto
    have qx: "q x\<in>q`C" and qy: "q y\<in>q`C" using x y by blast+
    have eq: "fiber_encode C q (q x)=fiber_encode C q (q y)" by (rule a[rule_format, OF e])
    show "q x=q y" by (rule inj_onD[OF fiber_encode_injective eq qx qy])
  qed
qed

lemma fiber_source_monotonicity_iff:
  assumes typed: "L\<subseteq>(q`C)\<times>(q`C)"
  shows "(\<forall>x\<in>C. \<forall>y\<in>C. (x,y)\<in>ord \<longrightarrow> (q x,q y)\<in>L)
    \<longleftrightarrow>
    (\<forall>x\<in>C. \<forall>y\<in>C. (x,y)\<in>ord \<longrightarrow>
      (fiber_encode C q (q x),fiber_encode C q (q y))\<in>fiber_relation C q C q L)"
proof -
  have eq: "\<And>x y. x\<in>C \<Longrightarrow> y\<in>C \<Longrightarrow>
    ((fiber_encode C q (q x),fiber_encode C q (q y))\<in>fiber_relation C q C q L
       \<longleftrightarrow> (q x,q y)\<in>L)"
  proof -
    fix x y assume x: "x\<in>C" and y: "y\<in>C"
    have qx: "q x\<in>q`C" and qy: "q y\<in>q`C" using x y by blast+
    show "(fiber_encode C q (q x),fiber_encode C q (q y))\<in>fiber_relation C q C q L
       \<longleftrightarrow> (q x,q y)\<in>L"
      unfolding fiber_relation_def by (rule fiber_trajectory_reflection[OF typed qx qy])
  qed
  show ?thesis using eq by blast
qed

lemma fiber_trajectory_image_iff:
  assumes source: "R\<subseteq>C\<times>B" and target: "trj\<subseteq>(qc`C)\<times>(qb`B)"
  shows "(trj=(\<lambda>(c,b). (qc c,qb b))`R) \<longleftrightarrow>
    (fiber_relation C qc B qb trj =
       (\<lambda>(c,b). (fiber_encode C qc (qc c),fiber_encode B qb (qb b)))`R)"
proof -
  have img: "(\<lambda>(c,b). (qc c,qb b))`R\<subseteq>(qc`C)\<times>(qb`B)"
    using source by auto
  have eq: "fiber_relation C qc B qb trj =
      fiber_relation C qc B qb ((\<lambda>(c,b). (qc c,qb b))`R)
    \<longleftrightarrow> trj=(\<lambda>(c,b). (qc c,qb b))`R"
    by (rule fiber_relation_equality_iff[OF target img])
  show ?thesis using eq by (simp only: fiber_relation_source_image)
qed

lemma fiber_admissibility_iff:
  assumes ec: "EC\<subseteq>C\<times>C" and eb: "EB\<subseteq>B\<times>B"
    and source: "R\<subseteq>C\<times>B"
    and order: "L\<subseteq>(qc`C)\<times>(qc`C)"
    and target: "trj\<subseteq>(qc`C)\<times>(qb`B)"
  shows "native_admissible C B EC EB ord R qc qb L trj \<longleftrightarrow>
    native_admissible C B EC EB ord R
      (fiber_encode C qc \<circ> qc) (fiber_encode B qb \<circ> qb)
      (fiber_relation C qc C qc L) (fiber_relation C qc B qb trj)"
  unfolding native_admissible_def comp_def
  using fiber_constancy_iff[OF ec, of qc]
    fiber_constancy_iff[OF eb, of qb]
    fiber_source_monotonicity_iff[OF order, of ord]
    fiber_trajectory_image_iff[OF source target]
  by iprover

ML \<open>
val roots = @{thms fiber_constancy_iff fiber_source_monotonicity_iff
  fiber_trajectory_image_iff fiber_admissibility_iff};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
