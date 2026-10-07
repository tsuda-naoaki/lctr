theory Core_Joint_Descent_Alignment
  imports LCTR_Core_Joint_Descent.Core_Joint_Descent
begin

locale carrier_saturation =
  fixes X :: "'x set" and A :: "'x set" and V :: "'v set"
    and S :: "('x\<times>'v) set" and q :: "'x\<Rightarrow>'q" and E :: "('x\<times>'x) set"
  assumes dom: "A\<subseteq>X" and typed: "S\<subseteq>X\<times>V"
    and kernel: "\<And>x y. x\<in>X \<Longrightarrow> y\<in>X \<Longrightarrow>
      ((x,y)\<in>E) = (q x=q y)"
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
  have yX: "y\<in>X" using typed y by blast
  have yx: "(y,x)\<in>E" using kernel[OF yX x] y by simp
  show "(x,v)\<in>S" using sat[OF yX x yx] v y by blast
next
  assume "(x,v)\<in>S"
  then show "(q x,v)\<in>rel_image q S" unfolding rel_image_def by force
qed
end

lemma quotient_relation_typed:
  assumes typed: "\<And>p. p\<in>S \<Longrightarrow> fst p\<in>A"
  shows "\<forall>p\<in>rel_image q S. fst p\<in>q`A"
  using typed unfolding rel_image_def by force

lemma quotient_pair_unique:
  fixes X :: "'x set" and Q :: "'q set" and V :: "'v set"
    and S0 S1 :: "('q\<times>'v) set"
  assumes onto: "q`X=Q"
    and a0: "A0\<subseteq>Q" and a1: "A1\<subseteq>Q"
    and s0: "S0\<subseteq>Q\<times>V" and s1: "S1\<subseteq>Q\<times>V"
    and dom: "\<And>x. x\<in>X \<Longrightarrow> (q x\<in>A0) = (q x\<in>A1)"
    and rel: "\<And>x v. x\<in>X \<Longrightarrow> v\<in>V \<Longrightarrow>
      ((q x,v)\<in>S0) = ((q x,v)\<in>S1)"
  shows "A0=A1 \<and> S0=S1"
proof -
  have de: "A0=A1" using onto a0 a1 dom by blast
  have se: "S0=S1"
  proof (rule set_eqI)
    fix p :: "'q\<times>'v"
    obtain y v where p: "p=(y,v)" by (cases p) auto
    show "p\<in>S0 \<longleftrightarrow> p\<in>S1"
    proof (cases "y\<in>Q \<and> v\<in>V")
      case True
      obtain x where x: "x\<in>X" "q x=y" using onto True by blast
      have v: "v\<in>V" using True by simp
      show ?thesis using rel[OF x(1) v] x p by simp
    next
      case False
      show ?thesis using False s0 s1 p by blast
    qed
  qed
  show ?thesis using de se by simp
qed

lemmas prodPrj_surjective = Core_Joint_Descent.product_projection_surjective
lemmas prodPrj_kernel = Core_Joint_Descent.product_projection_kernel

lemma native_joint_descent:
  fixes I :: "'i set" and X :: "'i\<Rightarrow>'x set" and E :: "'i\<Rightarrow>('x\<times>'x) set"
    and A :: "('i\<Rightarrow>'x) set" and V :: "'v set" and S :: "(('i\<Rightarrow>'x)\<times>'v) set"
  assumes eqv: "\<And>i. i\<in>I \<Longrightarrow> equiv (X i) (E i)"
    and dom: "A\<subseteq>Pi\<^sub>E I X" and typed: "S\<subseteq>(Pi\<^sub>E I X)\<times>V"
    and sat: "\<And>x y. x\<in>Pi\<^sub>E I X \<Longrightarrow> y\<in>Pi\<^sub>E I X \<Longrightarrow>
      (\<forall>i\<in>I. (x i,y i)\<in>E i) \<Longrightarrow>
      (x\<in>A \<longleftrightarrow> y\<in>A) \<and> (\<forall>v\<in>V. ((x,v)\<in>S) = ((y,v)\<in>S))"
  shows
    "(\<forall>x\<in>Pi\<^sub>E I X. (prod_proj I E x\<in>prod_proj I E ` A) = (x\<in>A)) \<and>
     (\<forall>x\<in>Pi\<^sub>E I X. \<forall>v\<in>V.
       ((prod_proj I E x,v)\<in>rel_image (prod_proj I E) S) = ((x,v)\<in>S)) \<and>
     (\<forall>A'\<subseteq>Pi\<^sub>E I (\<lambda>i. X i // E i).
      \<forall>S'\<subseteq>(Pi\<^sub>E I (\<lambda>i. X i // E i))\<times>V.
       (\<forall>x\<in>Pi\<^sub>E I X. (prod_proj I E x\<in>A') = (x\<in>A)) \<longrightarrow>
       (\<forall>x\<in>Pi\<^sub>E I X. \<forall>v\<in>V. ((prod_proj I E x,v)\<in>S') = ((x,v)\<in>S)) \<longrightarrow>
       A'=prod_proj I E ` A \<and> S'=rel_image (prod_proj I E) S)"
proof -
  let ?P = "Pi\<^sub>E I X"
  let ?Q = "Pi\<^sub>E I (\<lambda>i. X i // E i)"
  let ?q = "prod_proj I E"
  interpret N: carrier_saturation ?P A V S ?q "{(x,y). \<forall>i\<in>I. (x i,y i)\<in>E i}"
  proof
    show "A\<subseteq>?P" by (rule dom)
    show "S\<subseteq>?P\<times>V" by (rule typed)
    show "\<And>x y. x\<in>?P \<Longrightarrow> y\<in>?P \<Longrightarrow>
      ((x,y)\<in>{(x,y). \<forall>i\<in>I. (x i,y i)\<in>E i}) = (?q x=?q y)"
      by (simp add: product_projection_kernel[OF eqv])
    show "\<And>x y. x\<in>?P \<Longrightarrow> y\<in>?P \<Longrightarrow>
      (x,y)\<in>{(x,y). \<forall>i\<in>I. (x i,y i)\<in>E i} \<Longrightarrow>
      (x\<in>A \<longleftrightarrow> y\<in>A) \<and> (\<forall>v\<in>V. ((x,v)\<in>S) = ((y,v)\<in>S))"
      using sat by auto
  qed
  have onto: "?q`?P=?Q" by (rule product_projection_image)
  have aQ: "?q`A\<subseteq>?Q"
    using image_mono[OF dom, where f="?q"] by (simp only: onto)
  have sQ: "rel_image ?q S\<subseteq>?Q\<times>V"
  proof
    fix p
    assume "p\<in>rel_image ?q S"
    then obtain x v where p: "(x,v)\<in>S" "p=(?q x,v)"
      unfolding rel_image_def by auto
    have x: "x\<in>?P" and v: "v\<in>V" using typed p(1) by blast+
    have qx: "?q x\<in>?Q" by (rule product_projection_typed[OF x])
    show "p\<in>?Q\<times>V" using qx v p(2) by simp
  qed
  have unique: "\<And>A' S'. A'\<subseteq>?Q \<Longrightarrow> S'\<subseteq>?Q\<times>V \<Longrightarrow>
      (\<forall>x\<in>?P. (?q x\<in>A') = (x\<in>A)) \<Longrightarrow>
      (\<forall>x\<in>?P. \<forall>v\<in>V. ((?q x,v)\<in>S') = ((x,v)\<in>S)) \<Longrightarrow>
      A'=?q`A \<and> S'=rel_image ?q S"
  proof -
    fix A' S'
    assume a': "A'\<subseteq>?Q" and s': "S'\<subseteq>?Q\<times>V"
      and da: "\<forall>x\<in>?P. (?q x\<in>A') = (x\<in>A)"
      and sr: "\<forall>x\<in>?P. \<forall>v\<in>V. ((?q x,v)\<in>S') = ((x,v)\<in>S)"
    have dd: "\<And>x. x\<in>?P \<Longrightarrow> (?q x\<in>A') = (?q x\<in>?q`A)"
      using da N.domain_criterion by blast
    have rr: "\<And>x v. x\<in>?P \<Longrightarrow> v\<in>V \<Longrightarrow>
       ((?q x,v)\<in>S') = ((?q x,v)\<in>rel_image ?q S)"
      using sr N.relation_criterion by blast
    show "A'=?q`A \<and> S'=rel_image ?q S"
      by (rule quotient_pair_unique[OF onto a' aQ s' sQ dd rr])
  qed
  show ?thesis
  proof (intro conjI)
    show "\<forall>x\<in>?P. (?q x\<in>?q ` A) = (x\<in>A)"
      by (intro ballI, rule N.domain_criterion)
    show "\<forall>x\<in>?P. \<forall>v\<in>V. ((?q x,v)\<in>rel_image ?q S) = ((x,v)\<in>S)"
      by (intro ballI, rule N.relation_criterion)
    show "\<forall>A'\<subseteq>?Q. \<forall>S'\<subseteq>?Q\<times>V.
      (\<forall>x\<in>?P. (?q x\<in>A') = (x\<in>A)) \<longrightarrow>
      (\<forall>x\<in>?P. \<forall>v\<in>V. ((?q x,v)\<in>S') = ((x,v)\<in>S)) \<longrightarrow>
      A'=?q ` A \<and> S'=rel_image ?q S"
      by (intro allI impI, rule unique) assumption+
  qed
qed

lemmas missing_domain_saturation_control = Core_Joint_Descent.missing_domain_saturation_control
lemmas missing_surjectivity_control = Core_Joint_Descent.missing_surjectivity_control
lemma empty_domain_control: "q ` {} = {} \<and> rel_image q {} = {}"
  unfolding rel_image_def by simp

ML \<open>
val roots = @{thms carrier_saturation.domain_criterion carrier_saturation.relation_criterion
  quotient_relation_typed quotient_pair_unique prodPrj_surjective prodPrj_kernel
  native_joint_descent missing_domain_saturation_control missing_surjectivity_control empty_domain_control};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
