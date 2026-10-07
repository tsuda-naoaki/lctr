theory Core_Native_Joint_Relation
 imports "LCTR_Core_Joint_Time.Core_Joint_Time"
 "LCTR_Core_Joint_Descent_Alignment.Core_Joint_Descent_Alignment"
begin
context native_joint_curves
begin
definition state_equivalence where
 "state_equivalence i=observer_seed.EB C D B (R i)(Bind i)"
definition source_product where "source_product=PiE J (\<lambda>i. B)"
definition state_product where "state_product=PiE J (\<lambda>i. B//state_equivalence i)"
definition source_projection where "source_projection=prod_proj J state_equivalence"
definition source_same where "source_same x y \<longleftrightarrow> (\<forall>i\<in>J. (x i,y i)\<in>state_equivalence i)"
definition source_saturated where
 "source_saturated A V S \<longleftrightarrow> (\<forall>x\<in>source_product. \<forall>y\<in>source_product.
  source_same x y \<longrightarrow> (x\<in>A \<longleftrightarrow> y\<in>A) \<and>
   (\<forall>v\<in>V. ((x,v)\<in>S \<longleftrightarrow> (y,v)\<in>S)))"
lemma state_equivalence_typed: "equiv B (state_equivalence i)"
 unfolding state_equivalence_def observer_seed.EB_def
 by (rule least_equiv_equivalence[OF source_generator_carriers(3)])
lemma state_product_exact:
 "state_product=PiE J (\<lambda>i. observer_seed.State C D B (R i)(Bind i))"
 by (simp add: state_product_def state_equivalence_def observer_seed.State_def)
lemma source_projection_components:
 "i\<in>J \<Longrightarrow> source_projection x i=Image (state_equivalence i){x i}"
 by (simp add: source_projection_def prod_proj_def)
lemma source_projection_surjective:
 "y\<in>state_product \<Longrightarrow> \<exists>x\<in>source_product. source_projection x=y"
 unfolding source_product_def state_product_def source_projection_def
 by (rule product_projection_surjective)
lemma source_projection_kernel:
 "x\<in>source_product \<Longrightarrow> y\<in>source_product \<Longrightarrow>
  (source_same x y \<longleftrightarrow> source_projection x=source_projection y)"
 unfolding source_product_def source_same_def source_projection_def
 by (rule product_projection_kernel; (rule state_equivalence_typed | assumption))
lemma native_source_descent:
 assumes dom: "A\<subseteq>source_product" and typed: "S\<subseteq>source_product\<times>V"
 and sat: "source_saturated A V S"
 shows "(\<forall>x\<in>source_product. (source_projection x\<in>image source_projection A \<longleftrightarrow> x\<in>A)) \<and>
  (\<forall>x\<in>source_product. \<forall>v\<in>V.
   ((source_projection x,v)\<in>rel_image source_projection S \<longleftrightarrow> (x,v)\<in>S)) \<and>
  (\<forall>A'\<subseteq>state_product. \<forall>S'\<subseteq>state_product\<times>V.
   (\<forall>x\<in>source_product. (source_projection x\<in>A' \<longleftrightarrow> x\<in>A)) \<longrightarrow>
   (\<forall>x\<in>source_product. \<forall>v\<in>V. ((source_projection x,v)\<in>S' \<longleftrightarrow> (x,v)\<in>S)) \<longrightarrow>
   A'=image source_projection A \<and> S'=rel_image source_projection S)"
 unfolding source_product_def state_product_def source_projection_def
 proof (rule Core_Joint_Descent_Alignment.native_joint_descent)
  show "\<And>i. i\<in>J \<Longrightarrow> equiv B (state_equivalence i)" by (rule state_equivalence_typed)
  show "A\<subseteq>PiE J (\<lambda>i. B)" using dom unfolding source_product_def .
  show "S\<subseteq>PiE J (\<lambda>i. B)\<times>V" using typed unfolding source_product_def .
  show "\<And>x y. x\<in>PiE J (\<lambda>i. B) \<Longrightarrow> y\<in>PiE J (\<lambda>i. B) \<Longrightarrow>
   (\<forall>i\<in>J. (x i,y i)\<in>state_equivalence i) \<Longrightarrow>
   (x\<in>A \<longleftrightarrow> y\<in>A) \<and> (\<forall>v\<in>V. ((x,v)\<in>S \<longleftrightarrow> (y,v)\<in>S))"
   using sat unfolding source_saturated_def source_same_def source_product_def by blast
 qed
lemma native_relation_typed:
 "(\<And>p. p\<in>S \<Longrightarrow> fst p\<in>A) \<Longrightarrow>
  \<forall>p\<in>rel_image source_projection S. fst p\<in>image source_projection A"
 by (rule Core_Joint_Descent_Alignment.quotient_relation_typed)
lemma trajectory_has_source_representative:
 "q\<in>common_domain \<Longrightarrow> \<exists>x\<in>source_product. source_projection x=joint_curve q"
 by (rule source_projection_surjective) (simp add: state_product_exact joint_curve_typed)
definition joint_relation where
 "joint_relation V S=relation_pullback V (rel_image source_projection S)"
lemma joint_source_membership:
 assumes dom: "A\<subseteq>source_product" and typed: "S\<subseteq>source_product\<times>V"
 and sat: "source_saturated A V S"
 and q: "q\<in>common_domain" and x: "x\<in>source_product"
 and same: "source_projection x=joint_curve q" and v: "v\<in>V"
 shows "(q,v)\<in>joint_relation V S \<longleftrightarrow> (x,v)\<in>S"
proof -
 have criteria: "\<forall>x\<in>source_product. \<forall>v\<in>V.
  ((source_projection x,v)\<in>rel_image source_projection S \<longleftrightarrow> (x,v)\<in>S)"
  using conjunct1[OF conjunct2[OF native_source_descent[OF dom typed sat]]] .
 have crit: "(source_projection x,v)\<in>rel_image source_projection S \<longleftrightarrow> (x,v)\<in>S"
  by (rule bspec[OF bspec[OF criteria x] v])
 show ?thesis using crit q v same
  unfolding joint_relation_def relation_pullback_def by simp
qed
lemma every_trajectory_representative_agrees:
 assumes dom: "A\<subseteq>source_product" and typed: "S\<subseteq>source_product\<times>V"
 and sat: "source_saturated A V S" and q: "q\<in>common_domain"
 shows "(\<exists>x\<in>source_product. source_projection x=joint_curve q) \<and>
  (\<forall>x\<in>source_product. source_projection x=joint_curve q \<longrightarrow>
   (\<forall>v\<in>V. ((q,v)\<in>joint_relation V S \<longleftrightarrow> (x,v)\<in>S)))"
 using trajectory_has_source_representative[OF q] joint_source_membership[OF dom typed sat q] by blast
lemma joint_relation_unique:
 assumes typed: "candidate\<subseteq>common_domain\<times>V"
 and membership: "\<And>q v. q\<in>common_domain \<Longrightarrow> v\<in>V \<Longrightarrow>
  ((q,v)\<in>candidate \<longleftrightarrow> (joint_curve q,v)\<in>rel_image source_projection S)"
 shows "candidate=joint_relation V S"
 using typed membership unfolding joint_relation_def relation_pullback_def by auto
end
ML \<open>
val roots = @{thms native_joint_curves.source_projection_components native_joint_curves.source_projection_surjective
 native_joint_curves.source_projection_kernel native_joint_curves.native_source_descent
 native_joint_curves.native_relation_typed native_joint_curves.trajectory_has_source_representative
 native_joint_curves.joint_source_membership native_joint_curves.every_trajectory_representative_agrees
 native_joint_curves.joint_relation_unique};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
