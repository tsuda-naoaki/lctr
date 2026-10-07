theory Presentation_Fiber_Encoding
  imports Main
begin

definition fiber_encode where
  "fiber_encode C q t = {c\<in>C. q c=t}"
definition fiber_carrier where
  "fiber_carrier C q = fiber_encode C q ` (q`C)"
definition fiber_decode where
  "fiber_decode C q = inv_into (q`C) (fiber_encode C q)"
definition fiber_map where
  "fiber_map C q r f = fiber_encode C r \<circ> f \<circ> fiber_decode C q"

lemma fiber_encode_injective: "inj_on (fiber_encode C q) (q`C)"
proof (rule inj_onI)
  fix x y assume x: "x\<in>q`C" and y: "y\<in>q`C"
    and eq: "fiber_encode C q x=fiber_encode C q y"
  obtain c where c: "c\<in>C" "q c=x" using x by blast
  have "c\<in>fiber_encode C q x" using c unfolding fiber_encode_def by simp
  then have "c\<in>fiber_encode C q y" using eq by simp
  then show "x=y" using c unfolding fiber_encode_def by simp
qed

lemma fiber_encode_bijective:
  "bij_betw (fiber_encode C q) (q`C) (fiber_carrier C q)"
  unfolding fiber_carrier_def
  by (rule inj_on_imp_bij_betw[OF fiber_encode_injective])

lemma fiber_decode_encode:
  "t\<in>q`C \<Longrightarrow> fiber_decode C q (fiber_encode C q t)=t"
  unfolding fiber_decode_def by (rule inv_into_f_f[OF fiber_encode_injective])

lemma fiber_encode_decode:
  "X\<in>fiber_carrier C q \<Longrightarrow> fiber_encode C q (fiber_decode C q X)=X"
  unfolding fiber_carrier_def fiber_decode_def by (rule f_inv_into_f)

lemma fiber_decode_carrier:
  "X\<in>fiber_carrier C q \<Longrightarrow> fiber_decode C q X\<in>q`C"
  unfolding fiber_carrier_def fiber_decode_def by (rule inv_into_into)

lemma fiber_decode_image:
  "fiber_decode C q ` fiber_carrier C q = q`C"
  unfolding fiber_decode_def fiber_carrier_def
  by (rule inv_into_image_cancel[OF fiber_encode_injective]) simp

lemma fiber_encode_quantifiers:
  "(\<forall>t\<in>q`C. P t) \<longleftrightarrow>
   (\<forall>X\<in>fiber_carrier C q. P (fiber_decode C q X))"
proof
  assume "\<forall>t\<in>q`C. P t"
  then show "\<forall>X\<in>fiber_carrier C q. P (fiber_decode C q X)"
    using fiber_decode_carrier by blast
next
  assume a: "\<forall>X\<in>fiber_carrier C q. P (fiber_decode C q X)"
  show "\<forall>t\<in>q`C. P t"
  proof
    fix t assume t: "t\<in>q`C"
    have e: "fiber_encode C q t\<in>fiber_carrier C q"
      using t unfolding fiber_carrier_def by blast
    have "P (fiber_decode C q (fiber_encode C q t))" using a e by blast
    then show "P t" using fiber_decode_encode[OF t] by simp
  qed
qed

lemma fiber_map_source_commutes:
  assumes c: "c\<in>C" and f: "\<And>x. x\<in>C \<Longrightarrow> f(q x)=r x"
  shows "fiber_map C q r f (fiber_encode C q (q c))=fiber_encode C r (r c)"
proof -
  have qc: "q c\<in>q`C" using c by blast
  show ?thesis unfolding fiber_map_def comp_def
    by (simp only: fiber_decode_encode[OF qc] f[OF c])
qed

lemma fiber_map_onto:
  assumes onto: "f`(q`C)=r`C"
  shows "fiber_map C q r f ` fiber_carrier C q = fiber_carrier C r"
  unfolding fiber_map_def
  by (simp only: image_comp[symmetric] fiber_decode_image onto)
     (simp only: fiber_carrier_def)

lemma fiber_map_decodes:
  assumes t: "t\<in>q`C" and f: "f`(q`C)\<subseteq>r`C"
  shows "fiber_decode C r (fiber_map C q r f (fiber_encode C q t))=f t"
proof -
  have ft: "f t\<in>r`C" using f t by blast
  show ?thesis unfolding fiber_map_def comp_def
    by (simp only: fiber_decode_encode[OF t] fiber_decode_encode[OF ft])
qed

lemma fiber_map_composition:
  assumes X: "X\<in>fiber_carrier C q" and f: "f`(q`C)\<subseteq>r`C"
  shows "fiber_map C r s g (fiber_map C q r f X)=fiber_map C q s (g\<circ>f) X"
proof -
  have t: "fiber_decode C q X\<in>q`C" by (rule fiber_decode_carrier[OF X])
  have ft: "f(fiber_decode C q X)\<in>r`C" using f t by blast
  show ?thesis unfolding fiber_map_def comp_def
    by (simp only: fiber_decode_encode[OF ft])
qed

lemma fiber_order_reflection:
  assumes x: "x\<in>q`C" and y: "y\<in>q`C"
  shows "L (fiber_decode C q (fiber_encode C q x))
           (fiber_decode C q (fiber_encode C q y)) \<longleftrightarrow> L x y"
  by (simp only: fiber_decode_encode[OF x] fiber_decode_encode[OF y])

lemma fiber_trajectory_reflection:
  assumes typed: "R\<subseteq>(q`C)\<times>(r`B)"
    and x: "x\<in>q`C" and y: "y\<in>r`B"
  shows "(fiber_encode C q x,fiber_encode B r y)\<in>
      (\<lambda>(t,s). (fiber_encode C q t,fiber_encode B r s))`R
    \<longleftrightarrow> (x,y)\<in>R"
proof
  assume "(fiber_encode C q x,fiber_encode B r y)\<in>
      (\<lambda>(t,s). (fiber_encode C q t,fiber_encode B r s))`R"
  then obtain t s where ts: "(t,s)\<in>R"
    "fiber_encode C q t=fiber_encode C q x" "fiber_encode B r s=fiber_encode B r y"
    by auto
  have t: "t\<in>q`C" and s: "s\<in>r`B" using typed ts(1) by auto
  have tx: "t=x" by (rule inj_onD[OF fiber_encode_injective ts(2) t x])
  have sy: "s=y" by (rule inj_onD[OF fiber_encode_injective ts(3) s y])
  show "(x,y)\<in>R" using ts(1) tx sy by simp
next
  assume "(x,y)\<in>R"
  then show "(fiber_encode C q x,fiber_encode B r y)\<in>
      (\<lambda>(t,s). (fiber_encode C q t,fiber_encode B r s))`R"
    by force
qed

lemma fiber_empty_control:
  "fiber_carrier {} q={} \<and> bij_betw (fiber_encode {} q) {} {}"
  by (simp add: fiber_carrier_def bij_betw_def)

ML \<open>
val roots = @{thms fiber_encode_injective fiber_encode_bijective
  fiber_decode_encode fiber_encode_decode fiber_decode_carrier fiber_decode_image
  fiber_encode_quantifiers fiber_map_source_commutes fiber_map_onto
  fiber_map_decodes fiber_map_composition fiber_order_reflection
  fiber_trajectory_reflection fiber_empty_control};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
