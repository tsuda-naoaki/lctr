theory Core_Joint_Descent
  imports Main "HOL-Library.FuncSet"
begin
definition rel_image where "rel_image q S = (\<lambda>(x,v). (q x,v)) ` S"

locale relation_quotient =
  fixes X :: "'x set" and Q :: "'q set" and A :: "'x set" and V :: "'v set"
    and S :: "('x\<times>'v) set" and q :: "'x\<Rightarrow>'q" and E :: "('x\<times>'x) set"
  assumes onto: "q`X=Q" and dom: "A\<subseteq>X" and typed: "S\<subseteq>A\<times>V"
    and kernel: "\<And>x y. x\<in>X \<Longrightarrow> y\<in>X \<Longrightarrow> ((x,y)\<in>E) = (q x=q y)"
    and sat: "\<And>x y. x\<in>X \<Longrightarrow> y\<in>X \<Longrightarrow> (x,y)\<in>E \<Longrightarrow>
      (x\<in>A \<longleftrightarrow> y\<in>A) \<and> (\<forall>v\<in>V. ((x,v)\<in>S) = ((y,v)\<in>S))"
begin
lemma domain_criterion: "x\<in>X \<Longrightarrow> (q x\<in>q`A) = (x\<in>A)"
proof
  assume x: "x\<in>X" and h: "q x\<in>q`A"
  obtain y where y: "y\<in>A" "q y=q x" using h by (elim imageE) auto
  have yX: "y\<in>X" using dom y by blast
  have yx: "(y,x)\<in>E" using kernel[OF yX x] y by simp
  show "x\<in>A" using sat[OF yX x yx] y by blast
qed auto
lemma relation_criterion:
  assumes x: "x\<in>X" and v: "v\<in>V"
  shows "((q x,v)\<in>rel_image q S) = ((x,v)\<in>S)"
proof
  assume "(q x,v)\<in>rel_image q S"
  then obtain y where y: "(y,v)\<in>S" "q y=q x" unfolding rel_image_def by auto
  have yX: "y\<in>X" using typed dom y by blast
  have yx: "(y,x)\<in>E" using kernel[OF yX x] y by simp
  show "(x,v)\<in>S" using sat[OF yX x yx] v y by blast
next
  assume "(x,v)\<in>S"
  then show "(q x,v)\<in>rel_image q S" unfolding rel_image_def by force
qed
lemma quotient_typing: "q`A\<subseteq>Q" "rel_image q S\<subseteq>(q`A)\<times>V"
  using onto dom typed unfolding rel_image_def by auto
lemma quotient_pair_unique:
  assumes a': "A'\<subseteq>Q" and s': "S'\<subseteq>A'\<times>V"
    and da: "\<And>x. x\<in>X \<Longrightarrow> (q x\<in>A') = (x\<in>A)"
    and sr: "\<And>x v. x\<in>X \<Longrightarrow> v\<in>V \<Longrightarrow> ((q x,v)\<in>S') = ((x,v)\<in>S)"
  shows "A'=q`A \<and> S'=rel_image q S"
proof -
  have ae: "A'=q`A"
  proof (rule set_eqI)
    fix y
    show "y\<in>A' \<longleftrightarrow> y\<in>q`A"
    proof (cases "y\<in>Q")
      case True
      then obtain x where x: "x\<in>X" "q x=y" using onto by blast
      show ?thesis using da[OF x(1)] domain_criterion[OF x(1)] x by simp
    next
      case False
      show ?thesis using a' quotient_typing(1) False by blast
    qed
  qed
  have se: "S'=rel_image q S"
  proof (rule set_eqI)
    fix p :: "'q\<times>'v"
    obtain y v where p: "p=(y,v)" by (cases p) auto
    show "p\<in>S' \<longleftrightarrow> p\<in>rel_image q S"
    proof (cases "y\<in>Q \<and> v\<in>V")
      case True
      then obtain x where x: "x\<in>X" "q x=y" using onto by blast
      have v: "v\<in>V" using True by simp
      show ?thesis using sr[OF x(1) v] relation_criterion[OF x(1) v] x p by simp
    next
      case False
      show ?thesis using s' a' quotient_typing False p by blast
    qed
  qed
  show ?thesis using ae se by simp
qed
end

definition prod_proj where "prod_proj I E x = (\<lambda>i\<in>I. E i``{x i})"
lemma product_projection_typed:
  assumes "x\<in>Pi\<^sub>E I X"
  shows "prod_proj I E x\<in>Pi\<^sub>E I (\<lambda>i. X i // E i)"
  unfolding prod_proj_def using assms by (auto simp: PiE_iff intro: quotientI)
lemma product_projection_surjective:
  assumes y: "y\<in>Pi\<^sub>E I (\<lambda>i. X i // E i)"
  shows "\<exists>x\<in>Pi\<^sub>E I X. prod_proj I E x=y"
proof -
  have every: "\<forall>i\<in>I. \<exists>x. x\<in>X i \<and> E i``{x}=y i"
  proof (intro ballI)
    fix i
    assume i: "i\<in>I"
    have "y i\<in>X i // E i" by (rule PiE_mem[OF y i])
    then obtain x where "x\<in>X i" "y i=E i``{x}" by (elim quotientE)
    then show "\<exists>x. x\<in>X i \<and> E i``{x}=y i" by auto
  qed
  obtain f where f: "\<forall>i\<in>I. f i\<in>X i \<and> E i``{f i}=y i"
    using bchoice[OF every] by blast
  let ?x = "restrict f I"
  have x: "?x\<in>Pi\<^sub>E I X" using f by (simp add: PiE_iff)
  have eq: "prod_proj I E ?x=y"
  proof (rule ext)
    fix i
    show "prod_proj I E ?x i=y i"
      using f y unfolding prod_proj_def PiE_iff extensional_def by (cases "i\<in>I") auto
  qed
  show ?thesis using x eq by blast
qed
lemma product_projection_image:
 "prod_proj I E ` Pi\<^sub>E I X = Pi\<^sub>E I (\<lambda>i. X i // E i)"
  using product_projection_typed[where I=I and E=E and X=X]
    product_projection_surjective[where I=I and E=E and X=X] by blast
lemma product_projection_kernel:
  assumes eqv: "\<And>i. i\<in>I \<Longrightarrow> equiv (X i) (E i)"
    and x: "x\<in>Pi\<^sub>E I X" and y: "y\<in>Pi\<^sub>E I X"
  shows "(\<forall>i\<in>I. (x i,y i)\<in>E i) \<longleftrightarrow> prod_proj I E x=prod_proj I E y"
proof
  assume h: "\<forall>i\<in>I. (x i,y i)\<in>E i"
  show "prod_proj I E x=prod_proj I E y"
  proof (unfold prod_proj_def, rule restrict_ext)
    fix i
    assume i: "i\<in>I"
    show "E i``{x i}=E i``{y i}" by (rule equiv_class_eq[OF eqv[OF i]]) (use h i in blast)
  qed
next
  assume h: "prod_proj I E x=prod_proj I E y"
  show "\<forall>i\<in>I. (x i,y i)\<in>E i"
  proof (intro ballI)
    fix i
    assume i: "i\<in>I"
    have xi: "x i\<in>X i" using PiE_mem[OF x i] .
    have yi: "y i\<in>X i" using PiE_mem[OF y i] .
    have hi: "E i``{x i}=E i``{y i}" using fun_cong[OF h, of i] i unfolding prod_proj_def by simp
    show "(x i,y i)\<in>E i" using eq_equiv_class_iff[OF eqv[OF i] xi yi] hi by simp
  qed
qed

lemma native_joint_interface:
  assumes eqv: "\<And>i. i\<in>I \<Longrightarrow> equiv (X i) (E i)"
    and dom: "A\<subseteq>Pi\<^sub>E I X" and typed: "S\<subseteq>A\<times>V"
    and sat: "\<And>x y. x\<in>Pi\<^sub>E I X \<Longrightarrow> y\<in>Pi\<^sub>E I X \<Longrightarrow>
      (\<forall>i\<in>I. (x i,y i)\<in>E i) \<Longrightarrow>
      (x\<in>A \<longleftrightarrow> y\<in>A) \<and> (\<forall>v\<in>V. ((x,v)\<in>S) = ((y,v)\<in>S))"
  shows "relation_quotient (Pi\<^sub>E I X) (Pi\<^sub>E I (\<lambda>i. X i // E i)) A V S
    (prod_proj I E) {(x,y). \<forall>i\<in>I. (x i,y i)\<in>E i}"
proof
  show "prod_proj I E ` Pi\<^sub>E I X = Pi\<^sub>E I (\<lambda>i. X i // E i)" by (rule product_projection_image)
  show "A\<subseteq>Pi\<^sub>E I X" by (rule dom)
  show "S\<subseteq>A\<times>V" by (rule typed)
  show "\<And>x y. x\<in>Pi\<^sub>E I X \<Longrightarrow> y\<in>Pi\<^sub>E I X \<Longrightarrow>
    ((x,y)\<in>{(x,y). \<forall>i\<in>I. (x i,y i)\<in>E i}) = (prod_proj I E x=prod_proj I E y)"
    by (simp add: product_projection_kernel[OF eqv])
  show "\<And>x y. x\<in>Pi\<^sub>E I X \<Longrightarrow> y\<in>Pi\<^sub>E I X \<Longrightarrow>
    (x,y)\<in>{(x,y). \<forall>i\<in>I. (x i,y i)\<in>E i} \<Longrightarrow>
    (x\<in>A \<longleftrightarrow> y\<in>A) \<and> (\<forall>v\<in>V. ((x,v)\<in>S) = ((y,v)\<in>S))"
    using sat by auto
qed
lemma empty_product_control:
  "Pi\<^sub>E {} X = {\<lambda>i. undefined}" "prod_proj {} E x = (\<lambda>i. undefined)"
  unfolding prod_proj_def by (auto simp: PiE_iff extensional_def fun_eq_iff)
lemma missing_domain_saturation_control:
  "rel_image (\<lambda>_::bool. ()) {} = {} \<and> (\<lambda>_::bool. ()) False\<in>(\<lambda>_::bool. ())`{True} \<and> False\<notin>{True}"
  unfolding rel_image_def by simp
lemma missing_surjectivity_control:
  "(\<forall>x::unit. ((\<lambda>_::unit. False) x\<in>{}) = ((\<lambda>_::unit. False) x\<in>{True})) \<and> {}\<noteq>{True}"
  by simp

ML \<open>
val roots = @{thms relation_quotient.domain_criterion relation_quotient.relation_criterion
  relation_quotient.quotient_typing relation_quotient.quotient_pair_unique
  product_projection_typed product_projection_surjective product_projection_image product_projection_kernel native_joint_interface
  empty_product_control missing_domain_saturation_control missing_surjectivity_control};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
