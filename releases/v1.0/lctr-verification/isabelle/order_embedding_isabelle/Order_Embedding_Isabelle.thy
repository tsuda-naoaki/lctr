theory Order_Embedding_Isabelle
  imports "HOL.Real" "HOL.Hilbert_Choice"
begin

definition strict_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "strict_on X r \<longleftrightarrow>
    (\<forall>x\<in>X. \<not> r x x) \<and>
    (\<forall>x\<in>X. \<forall>y\<in>X. \<forall>z\<in>X. r x y \<longrightarrow> r y z \<longrightarrow> r x z)"

definition strict_linear_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "strict_linear_on X r \<longleftrightarrow>
    strict_on X r \<and>
    (\<forall>x\<in>X. \<forall>y\<in>X. x \<noteq> y \<longrightarrow> r x y \<or> r y x)"

definition inc_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "inc_on X r x y \<longleftrightarrow>
    x \<in> X \<and> y \<in> X \<and> \<not> r x y \<and> \<not> r y x"

definition inc_trans_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "inc_trans_on X r \<longleftrightarrow>
    (\<forall>x\<in>X. \<forall>y\<in>X. \<forall>z\<in>X.
      inc_on X r x y \<longrightarrow> inc_on X r y z \<longrightarrow> inc_on X r x z)"

definition qclass :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "qclass X r x = {y \<in> X. inc_on X r x y}"

definition qproj :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "qproj X r x = qclass X r x"

definition QuSet :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set set" where
  "QuSet X r = image (qproj X r) X"

definition qlt :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "qlt X r C D \<longleftrightarrow>
    (\<exists>x\<in>X. \<exists>y\<in>X.
      C = qproj X r x \<and> D = qproj X r y \<and> r x y)"

definition rgraph :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b) set" where
  "rgraph X f = {(x, f x) |x. x \<in> X}"

lemma inc_on_refl:
  assumes "strict_on X r" "x \<in> X"
  shows "inc_on X r x x"
  using assms unfolding strict_on_def inc_on_def by blast

lemma inc_on_sym:
  assumes "inc_on X r x y"
  shows "inc_on X r y x"
  using assms unfolding inc_on_def by blast

lemma inc_on_left_mem:
  assumes "inc_on X r x y"
  shows "x \<in> X"
  using assms unfolding inc_on_def by blast

lemma inc_on_right_mem:
  assumes "inc_on X r x y"
  shows "y \<in> X"
  using assms unfolding inc_on_def by blast

lemma qclass_eq_if_inc:
  assumes tr: "inc_trans_on X r"
    and xy: "inc_on X r x y"
  shows "qclass X r x = qclass X r y"
proof (rule set_eqI)
  fix z
  show "z \<in> qclass X r x \<longleftrightarrow> z \<in> qclass X r y"
  proof
    assume zx: "z \<in> qclass X r x"
    have xz: "inc_on X r x z"
      using zx unfolding qclass_def by simp
    have yx: "inc_on X r y x"
      using xy by (rule inc_on_sym)
    have yX: "y \<in> X"
      using yx by (rule inc_on_left_mem)
    have xX: "x \<in> X"
      using yx by (rule inc_on_right_mem)
    have zX: "z \<in> X"
      using xz by (rule inc_on_right_mem)
    have yz: "inc_on X r y z"
      using tr yX xX zX yx xz unfolding inc_trans_on_def by blast
    show "z \<in> qclass X r y"
      unfolding qclass_def using zX yz by simp
  next
    assume zy: "z \<in> qclass X r y"
    have yz: "inc_on X r y z"
      using zy unfolding qclass_def by simp
    have xX: "x \<in> X"
      using xy by (rule inc_on_left_mem)
    have yX: "y \<in> X"
      using xy by (rule inc_on_right_mem)
    have zX: "z \<in> X"
      using yz by (rule inc_on_right_mem)
    have xz: "inc_on X r x z"
      using tr xX yX zX xy yz unfolding inc_trans_on_def by blast
    show "z \<in> qclass X r x"
      unfolding qclass_def using zX xz by simp
  qed
qed

lemma qclass_eq_iff_inc:
  assumes strict: "strict_on X r"
    and tr: "inc_trans_on X r"
    and xX: "x \<in> X"
    and yX: "y \<in> X"
  shows "qclass X r x = qclass X r y \<longleftrightarrow> inc_on X r x y"
proof
  assume eq: "qclass X r x = qclass X r y"
  have ixx: "inc_on X r x x"
    using inc_on_refl[OF strict xX] .
  have xx: "x \<in> qclass X r x"
    unfolding qclass_def using xX ixx by simp
  have "x \<in> qclass X r y"
    using eq xx by simp
  then have "inc_on X r y x"
    unfolding qclass_def by simp
  then show "inc_on X r x y"
    by (rule inc_on_sym)
next
  assume xy: "inc_on X r x y"
  show "qclass X r x = qclass X r y"
    using qclass_eq_if_inc[OF tr xy] .
qed

lemma lt_transfer_left:
  assumes strict: "strict_on X r"
    and tr: "inc_trans_on X r"
    and xx': "inc_on X r x x'"
    and yX: "y \<in> X"
    and xy: "r x y"
  shows "r x' y"
  using assms unfolding strict_on_def inc_trans_on_def inc_on_def by blast

lemma lt_transfer_right:
  assumes strict: "strict_on X r"
    and tr: "inc_trans_on X r"
    and yy': "inc_on X r y y'"
    and xX: "x \<in> X"
    and xy: "r x y"
  shows "r x y'"
  using assms unfolding strict_on_def inc_trans_on_def inc_on_def by blast

lemma lt_invariant_under_inc:
  assumes strict: "strict_on X r"
    and tr: "inc_trans_on X r"
    and xx': "inc_on X r x x'"
    and yy': "inc_on X r y y'"
  shows "r x y \<longleftrightarrow> r x' y'"
proof
  assume xy: "r x y"
  have yX: "y \<in> X"
    using yy' unfolding inc_on_def by blast
  have x'X: "x' \<in> X"
    using xx' unfolding inc_on_def by blast
  have x'y: "r x' y"
    using lt_transfer_left[OF strict tr xx' yX xy] .
  show "r x' y'"
    using lt_transfer_right[OF strict tr yy' x'X x'y] .
next
  assume x'y': "r x' y'"
  have x'x: "inc_on X r x' x"
    using xx' by (rule inc_on_sym)
  have y'y: "inc_on X r y' y"
    using yy' by (rule inc_on_sym)
  have y'X: "y' \<in> X"
    using yy' unfolding inc_on_def by blast
  have xX: "x \<in> X"
    using xx' unfolding inc_on_def by blast
  have xy': "r x y'"
    using lt_transfer_left[OF strict tr x'x y'X x'y'] .
  show "r x y"
    using lt_transfer_right[OF strict tr y'y xX xy'] .
qed

lemma qproj_image:
  "image (qproj X r) X = QuSet X r"
  unfolding QuSet_def by simp

lemma qproj_class_iff:
  assumes "strict_on X r" "inc_trans_on X r" "x \<in> X" "y \<in> X"
  shows "qproj X r x = qproj X r y \<longleftrightarrow> inc_on X r x y"
  using qclass_eq_iff_inc[OF assms]
  unfolding qproj_def .

lemma qproj_order_iff:
  assumes strict: "strict_on X r"
    and tr: "inc_trans_on X r"
    and xX: "x \<in> X"
    and yX: "y \<in> X"
  shows "qlt X r (qproj X r x) (qproj X r y) \<longleftrightarrow> r x y"
proof
  assume qxy: "qlt X r (qproj X r x) (qproj X r y)"
  then obtain u v where
      uX: "u \<in> X" and vX: "v \<in> X"
      and xu: "qproj X r x = qproj X r u"
      and yv: "qproj X r y = qproj X r v"
      and uv: "r u v"
    unfolding qlt_def by blast
  have ixu: "inc_on X r x u"
    using qproj_class_iff[OF strict tr xX uX] xu by blast
  have ivy: "inc_on X r v y"
  proof -
    have iyv: "inc_on X r y v"
      using qproj_class_iff[OF strict tr yX vX] yv by blast
    then show ?thesis by (rule inc_on_sym)
  qed
  have iux: "inc_on X r u x"
    using ixu by (rule inc_on_sym)
  show "r x y"
    using lt_invariant_under_inc[OF strict tr iux ivy] uv by blast
next
  assume xy: "r x y"
  show "qlt X r (qproj X r x) (qproj X r y)"
    unfolding qlt_def using xX yX xy by blast
qed

theorem transitive_incomparability_quotient:
  assumes strict: "strict_on X r"
    and tr: "inc_trans_on X r"
  shows
    "image (qproj X r) X = QuSet X r \<and>
     (\<forall>x\<in>X. \<forall>y\<in>X.
       (qproj X r x = qproj X r y \<longleftrightarrow> inc_on X r x y)) \<and>
     (\<forall>x\<in>X. \<forall>y\<in>X.
       (qlt X r (qproj X r x) (qproj X r y) \<longleftrightarrow> r x y)) \<and>
     strict_linear_on (QuSet X r) (qlt X r)"
proof -
  have proj: "image (qproj X r) X = QuSet X r"
    by (rule qproj_image)
  have cls:
    "\<forall>x\<in>X. \<forall>y\<in>X.
      (qproj X r x = qproj X r y \<longleftrightarrow> inc_on X r x y)"
    using qproj_class_iff[OF strict tr] by blast
  have ord:
    "\<forall>x\<in>X. \<forall>y\<in>X.
      (qlt X r (qproj X r x) (qproj X r y) \<longleftrightarrow> r x y)"
    using qproj_order_iff[OF strict tr] by blast

  have irr: "\<forall>C\<in>QuSet X r. \<not> qlt X r C C"
  proof (intro ballI)
    fix C
    assume "C \<in> QuSet X r"
    then obtain x where xX: "x \<in> X" and C: "C = qproj X r x"
      unfolding QuSet_def by blast
    have nrxx: "\<not> r x x"
      using strict xX unfolding strict_on_def by blast
    show "\<not> qlt X r C C"
      using ord xX C nrxx by blast
  qed

  have qtrans:
    "\<forall>A\<in>QuSet X r. \<forall>B\<in>QuSet X r. \<forall>C\<in>QuSet X r.
      qlt X r A B \<longrightarrow> qlt X r B C \<longrightarrow> qlt X r A C"
  proof (intro ballI impI)
    fix A B C
    assume AQ: "A \<in> QuSet X r"
      and BQ: "B \<in> QuSet X r"
      and CQ: "C \<in> QuSet X r"
      and AB: "qlt X r A B"
      and BC: "qlt X r B C"
    obtain x where xX: "x \<in> X" and A: "A = qproj X r x"
      using AQ unfolding QuSet_def by blast
    obtain y where yX: "y \<in> X" and B: "B = qproj X r y"
      using BQ unfolding QuSet_def by blast
    obtain z where zX: "z \<in> X" and C: "C = qproj X r z"
      using CQ unfolding QuSet_def by blast
    have xy: "r x y"
      using ord xX yX A B AB by blast
    have yz: "r y z"
      using ord yX zX B C BC by blast
    have xz: "r x z"
      using strict xX yX zX xy yz unfolding strict_on_def by blast
    show "qlt X r A C"
      using ord xX zX A C xz by blast
  qed

  have total:
    "\<forall>A\<in>QuSet X r. \<forall>B\<in>QuSet X r.
      A \<noteq> B \<longrightarrow> qlt X r A B \<or> qlt X r B A"
  proof (intro ballI impI)
    fix A B
    assume AQ: "A \<in> QuSet X r"
      and BQ: "B \<in> QuSet X r"
      and neq: "A \<noteq> B"
    obtain x where xX: "x \<in> X" and A: "A = qproj X r x"
      using AQ unfolding QuSet_def by blast
    obtain y where yX: "y \<in> X" and B: "B = qproj X r y"
      using BQ unfolding QuSet_def by blast
    have ninc: "\<not> inc_on X r x y"
      using cls xX yX neq A B by blast
    have "r x y \<or> r y x"
      using ninc xX yX unfolding inc_on_def by blast
    then show "qlt X r A B \<or> qlt X r B A"
      using ord xX yX A B by blast
  qed

  have linear: "strict_linear_on (QuSet X r) (qlt X r)"
    unfolding strict_linear_on_def strict_on_def
    using irr qtrans total by blast

  show ?thesis
    using proj cls ord linear by blast
qed

theorem guarded_real_order_embedding_inj_on:
  assumes linear: "strict_linear_on Q ltQ"
    and emb:
      "\<forall>x\<in>Q. \<forall>y\<in>Q.
        (ltQ x y \<longleftrightarrow> rho x < (rho y :: real))"
  shows "inj_on rho Q"
proof (unfold inj_on_def, intro ballI impI)
  fix x y
  assume xQ: "x \<in> Q" and yQ: "y \<in> Q" and eq: "rho x = rho y"
  show "x = y"
  proof (rule ccontr)
    assume neq: "x \<noteq> y"
    have "ltQ x y \<or> ltQ y x"
      using linear xQ yQ neq unfolding strict_linear_on_def by blast
    then show False
      using emb xQ yQ eq by auto
  qed
qed

theorem real_time_order_embedding_injective:
  assumes strict: "strict_on X r"
    and inc_trans: "inc_trans_on X r"
    and real_embedding_exists:
      "\<exists>f::'a set \<Rightarrow> real.
        \<forall>C\<in>QuSet X r. \<forall>D\<in>QuSet X r.
          (qlt X r C D \<longleftrightarrow> f C < f D)"
    and rho_embedding:
      "\<forall>C\<in>QuSet X r. \<forall>D\<in>QuSet X r.
        (qlt X r C D \<longleftrightarrow> rho C < (rho D :: real))"
  shows "inj_on rho (QuSet X r)"
proof -
  have linear: "strict_linear_on (QuSet X r) (qlt X r)"
    using transitive_incomparability_quotient[OF strict inc_trans] by blast
  show ?thesis
    using guarded_real_order_embedding_inj_on[OF linear rho_embedding] .
qed

theorem nested_quotient_order_embedding:
  fixes A S :: "'s set"
    and QA :: "'qa set"
    and QS :: "'qs set"
    and piA :: "'s \<Rightarrow> 'qa"
    and piS :: "'s \<Rightarrow> 'qs"
    and ltA :: "'qa \<Rightarrow> 'qa \<Rightarrow> bool"
    and ltS :: "'qs \<Rightarrow> 'qs \<Rightarrow> bool"
  assumes sub: "A \<subseteq> S"
    and surjA: "image piA A = QA"
    and surjS: "image piS S = QS"
    and strictA: "strict_on QA ltA"
    and strictS: "strict_on QS ltS"
    and kernel:
      "\<And>x y. \<lbrakk>x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow>
        (piA x = piA y \<longleftrightarrow> piS x = piS y)"
    and order_eq:
      "\<And>x y. \<lbrakk>x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow>
        (ltA (piA x) (piA y) \<longleftrightarrow> ltS (piS x) (piS y))"
  shows
    "\<exists>iota::'qa \<Rightarrow> 'qs.
      image iota QA \<subseteq> QS \<and>
      inj_on iota QA \<and>
      (\<forall>x\<in>A. iota (piA x) = piS x) \<and>
      (\<forall>q\<in>QA. \<forall>q'\<in>QA.
        (ltA q q' \<longleftrightarrow> ltS (iota q) (iota q'))) \<and>
      rgraph A (iota \<circ> piA) = rgraph A piS"
proof -
  let ?rep = "\<lambda>q. SOME x. x \<in> A \<and> piA x = q"
  let ?iota = "\<lambda>q. piS (?rep q)"

  have rep:
    "\<And>q. q \<in> QA \<Longrightarrow> ?rep q \<in> A \<and> piA (?rep q) = q"
  proof -
    fix q
    assume qQ: "q \<in> QA"
    have "q \<in> image piA A"
      using qQ surjA by simp
    then have "\<exists>x. x \<in> A \<and> piA x = q"
      by blast
    then show "?rep q \<in> A \<and> piA (?rep q) = q"
      by (rule someI_ex)
  qed

  have maps: "image ?iota QA \<subseteq> QS"
  proof
    fix z
    assume "z \<in> image ?iota QA"
    then obtain q where qQ: "q \<in> QA" and z: "z = ?iota q"
      by blast
    have rA: "?rep q \<in> A"
      using rep[OF qQ] by blast
    have rS: "?rep q \<in> S"
      using sub rA by blast
    have "piS (?rep q) \<in> image piS S"
      using rS by blast
    then show "z \<in> QS"
      using surjS z by simp
  qed

  have commute:
    "\<And>x. x \<in> A \<Longrightarrow> ?iota (piA x) = piS x"
  proof -
    fix x
    assume xA: "x \<in> A"
    have pxQ: "piA x \<in> QA"
      using surjA xA by blast
    have rr: "?rep (piA x) \<in> A \<and> piA (?rep (piA x)) = piA x"
      using rep[OF pxQ] .
    show "?iota (piA x) = piS x"
      using kernel[OF conjunct1[OF rr] xA] rr by blast
  qed

  have inj: "inj_on ?iota QA"
  proof (unfold inj_on_def, intro ballI impI)
    fix q q'
    assume qQ: "q \<in> QA" and q'Q: "q' \<in> QA"
      and eq: "?iota q = ?iota q'"
    have rq: "?rep q \<in> A \<and> piA (?rep q) = q"
      using rep[OF qQ] .
    have rq': "?rep q' \<in> A \<and> piA (?rep q') = q'"
      using rep[OF q'Q] .
    have "piA (?rep q) = piA (?rep q')"
      using kernel[OF conjunct1[OF rq] conjunct1[OF rq']] eq by blast
    then show "q = q'"
      using rq rq' by simp
  qed

  have ord:
    "\<forall>q\<in>QA. \<forall>q'\<in>QA.
      (ltA q q' \<longleftrightarrow> ltS (?iota q) (?iota q'))"
  proof (intro ballI)
    fix q q'
    assume qQ: "q \<in> QA" and q'Q: "q' \<in> QA"
    have rq: "?rep q \<in> A \<and> piA (?rep q) = q"
      using rep[OF qQ] .
    have rq': "?rep q' \<in> A \<and> piA (?rep q') = q'"
      using rep[OF q'Q] .
    show "ltA q q' \<longleftrightarrow> ltS (?iota q) (?iota q')"
      using order_eq[OF conjunct1[OF rq] conjunct1[OF rq']] rq rq' by simp
  qed

  have graph: "rgraph A (?iota \<circ> piA) = rgraph A piS"
    using commute unfolding rgraph_def by auto

  show ?thesis
    using maps inj commute ord graph by blast
qed

lemma inv_into_left_on_source:
  assumes "inj_on rho S" "x \<in> S"
  shows "inv_into S rho (rho x) = x"
  using assms by (rule inv_into_f_f)

lemma inv_into_right_on_image:
  assumes "t \<in> image rho S"
  shows "rho (inv_into S rho t) = t"
  using assms by (rule f_inv_into_f)

lemma inverse_characterization_guarded:
  assumes inj: "inj_on rho S"
    and tI: "t \<in> image rho S"
    and xS: "x \<in> S"
  shows "inv_into S rho t = x \<longleftrightarrow> rho x = t"
proof
  assume eq: "inv_into S rho t = x"
  have "rho (inv_into S rho t) = t"
    using tI by (rule f_inv_into_f)
  then show "rho x = t"
    using eq by simp
next
  assume eq: "rho x = t"
  show "inv_into S rho t = x"
    using inj xS eq by (rule inv_into_f_eq)
qed

theorem restricted_inverse_graph_correspondence:
  fixes rho :: "'a \<Rightarrow> 'b"
    and S :: "'a set"
  assumes inj: "inj_on rho S"
  shows
    "rgraph (image rho S) (inv_into S rho) =
      {(t, x). t \<in> image rho S \<and> x \<in> S \<and> rho x = t}"
proof (rule set_eqI)
  fix p :: "'b \<times> 'a"
  obtain t x where p: "p = (t, x)"
    by (cases p)
  show "p \<in> rgraph (image rho S) (inv_into S rho) \<longleftrightarrow>
        p \<in> {(t, x). t \<in> image rho S \<and> x \<in> S \<and> rho x = t}"
  proof
    assume left: "p \<in> rgraph (image rho S) (inv_into S rho)"
    then have tI: "t \<in> image rho S" and xeq: "x = inv_into S rho t"
      unfolding p rgraph_def by auto
    have xS: "inv_into S rho t \<in> S"
      using tI by (rule inv_into_into)
    have rt: "rho (inv_into S rho t) = t"
      using tI by (rule f_inv_into_f)
    show "p \<in> {(t, x). t \<in> image rho S \<and> x \<in> S \<and> rho x = t}"
      using p tI xeq xS rt by simp
  next
    assume right:
      "p \<in> {(t, x). t \<in> image rho S \<and> x \<in> S \<and> rho x = t}"
    then have tI: "t \<in> image rho S" and xS: "x \<in> S" and eq: "rho x = t"
      using p by auto
    have invx: "inv_into S rho t = x"
      using inverse_characterization_guarded[OF inj tI xS] eq by blast
    show "p \<in> rgraph (image rho S) (inv_into S rho)"
      using p tI invx unfolding rgraph_def by auto
  qed
qed

theorem image_inverse_contract:
  assumes inj: "inj_on rho S"
  shows
    "(\<forall>x\<in>S. inv_into S rho (rho x) = x) \<and>
     (\<forall>t\<in>image rho S. rho (inv_into S rho t) = t) \<and>
     (\<forall>t\<in>image rho S. \<forall>x\<in>S.
       (inv_into S rho t = x \<longleftrightarrow> rho x = t)) \<and>
     rgraph (image rho S) (inv_into S rho) =
       {(t, x). t \<in> image rho S \<and> x \<in> S \<and> rho x = t}"
proof (intro conjI)
  show "\<forall>x\<in>S. inv_into S rho (rho x) = x"
  proof (intro ballI)
    fix x
    assume xS: "x \<in> S"
    show "inv_into S rho (rho x) = x"
      using inv_into_left_on_source[OF inj xS] .
  qed
  show "\<forall>t\<in>image rho S. rho (inv_into S rho t) = t"
  proof (intro ballI)
    fix t
    assume tI: "t \<in> image rho S"
    show "rho (inv_into S rho t) = t"
      using inv_into_right_on_image[OF tI] .
  qed
  show "\<forall>t\<in>image rho S. \<forall>x\<in>S.
      (inv_into S rho t = x \<longleftrightarrow> rho x = t)"
  proof (intro ballI)
    fix t x
    assume tI: "t \<in> image rho S"
      and xS: "x \<in> S"
    show "inv_into S rho t = x \<longleftrightarrow> rho x = t"
      using inverse_characterization_guarded[OF inj tI xS] .
  qed
  show "rgraph (image rho S) (inv_into S rho) =
      {(t, x). t \<in> image rho S \<and> x \<in> S \<and> rho x = t}"
    using restricted_inverse_graph_correspondence[OF inj] .
qed

theorem real_time_image_inverse_composition:
  assumes strict: "strict_on X r"
    and inc_trans: "inc_trans_on X r"
    and rho_embedding:
      "\<forall>C\<in>QuSet X r. \<forall>D\<in>QuSet X r.
        (qlt X r C D \<longleftrightarrow> rho C < (rho D :: real))"
  shows
    "(\<forall>C\<in>QuSet X r.
       inv_into (QuSet X r) rho (rho C) = C) \<and>
     (\<forall>t\<in>image rho (QuSet X r).
       rho (inv_into (QuSet X r) rho t) = t) \<and>
     (\<forall>t\<in>image rho (QuSet X r). \<forall>C\<in>QuSet X r.
       (inv_into (QuSet X r) rho t = C \<longleftrightarrow> rho C = t)) \<and>
     rgraph (image rho (QuSet X r)) (inv_into (QuSet X r) rho) =
       {(t, C). t \<in> image rho (QuSet X r) \<and>
                C \<in> QuSet X r \<and> rho C = t}"
proof -
  have linear: "strict_linear_on (QuSet X r) (qlt X r)"
    using transitive_incomparability_quotient[OF strict inc_trans] by blast
  have inj: "inj_on rho (QuSet X r)"
    using guarded_real_order_embedding_inj_on[OF linear rho_embedding] .
  show ?thesis
    using image_inverse_contract[OF inj] .
qed

end
