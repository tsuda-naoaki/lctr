theory Core_Joint_Real_Image
 imports "LCTR_Core_Joint_Law_Evaluation.Core_Joint_Law_Evaluation"
begin
context native_joint_law
begin
lemma domain_image: "real_time = rho`{q. \<forall>i\<in>J. q\<in>individual_domain i}"
 unfolding real_time_def common_domain_def by (rule refl)
lemma projection_inverse: "t\<in>real_time \<Longrightarrow> rho(order_inverse t)=t"
 unfolding real_time_def order_inverse_def by (rule f_inv_into_f)
lemma relation_image:
 "real_relation r = (\<lambda>(q,v). (rho q,v))`joint_relation(rel_carrier r)(source_relation r)"
proof (rule set_eqI)
 fix p :: "real \<times> 'w"
 obtain t v where p: "p=(t,v)" by (cases p) simp
 show "p\<in>real_relation r \<longleftrightarrow>
   p\<in>(\<lambda>(q,v). (rho q,v))`joint_relation(rel_carrier r)(source_relation r)"
 proof
  assume mem: "p\<in>real_relation r"
  have t: "t\<in>real_time" and qv: "(order_inverse t,v)\<in>joint_relation(rel_carrier r)(source_relation r)"
    using mem unfolding real_relation_def p by auto
  show "p\<in>(\<lambda>(q,v). (rho q,v))`joint_relation(rel_carrier r)(source_relation r)"
    using imageI[OF qv, of "\<lambda>(q,v). (rho q,v)"] projection_inverse[OF t] p by simp
 next
  assume mem: "p\<in>(\<lambda>(q,v). (rho q,v))`joint_relation(rel_carrier r)(source_relation r)"
  then obtain q w where qw: "(q,w)\<in>joint_relation(rel_carrier r)(source_relation r)"
    and eq: "p=(rho q,w)" by auto
  have q: "q\<in>common_domain" using qw unfolding joint_relation_def relation_pullback_def by simp
  have tt: "rho q\<in>real_time" unfolding real_time_def by (rule imageI[OF q])
  show "p\<in>real_relation r" using qw tt inverse_on_projection[OF q] unfolding eq real_relation_def by simp
 qed
qed
lemma ambient_relation_image:
 "t\<in>real_time \<Longrightarrow> v\<in>rel_carrier r \<Longrightarrow>
  ((t,v)\<in>real_relation r \<longleftrightarrow>
   (t,v)\<in>(\<lambda>(q,v). (rho q,v))`joint_relation(rel_carrier r)(source_relation r))"
 by (simp only: relation_image)
end
ML \<open>
val roots = @{thms native_joint_law.domain_image native_joint_law.projection_inverse
 native_joint_law.relation_image native_joint_law.ambient_relation_image};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
