theory Core_Approximate_Boundary
  imports LCTR_Core_First_Failure_Report.Core_First_Failure_Report
begin

definition complete :: "(token\<Rightarrow>internal_state)\<Rightarrow>bool" where "complete q=(\<forall>i\<in>approximation_indices. q (3,i)=SAT)"
definition failed_scales :: "('a\<Rightarrow>token\<Rightarrow>internal_state)\<Rightarrow>'a set" where
  "failed_scales q={x. \<exists>i\<in>approximation_indices. q x (3,i)=Failed}"
definition unsatisfied_scales where "unsatisfied_scales q={x. \<not>complete (q x)}"
definition least_pre :: "'a::preorder set\<Rightarrow>'a\<Rightarrow>bool" where
  "least_pre S x=(x\<in>S \<and> (\<forall>y\<in>S. x\<le>y))"

lemma failure_implies_noncompletion: "failed_scales q\<subseteq>unsatisfied_scales q"
proof
  fix x assume "x\<in>failed_scales q"
  then obtain i where ii: "i\<in>approximation_indices" and qi: "q x (3,i)=Failed"
    by (auto simp: failed_scales_def)
  have "\<not>complete (q x)"
  proof
    assume all: "complete (q x)"
    have "q x (3,i)=SAT" using all ii by (simp add: complete_def)
    then show False using qi by simp
  qed
  then show "x\<in>unsatisfied_scales q" by (simp add: unsatisfied_scales_def)
qed

lemma least_failure_after_boundary:
  assumes a: "least_pre (failed_scales q) a"
    and b: "least_pre (unsatisfied_scales q) b"
  shows "b\<le>a"
proof -
  have af: "a\<in>failed_scales q" using a by (simp add: least_pre_def)
  have au: "a\<in>unsatisfied_scales q" by (rule subsetD[OF failure_implies_noncompletion af])
  show ?thesis using b au by (simp add: least_pre_def)
qed

lemma scale_sets_equal_if_failure_detected:
  assumes detect: "\<And>x. \<not>complete (q x) \<Longrightarrow>
    \<exists>i\<in>approximation_indices. q x (3,i)=Failed"
  shows "failed_scales q=unsatisfied_scales q"
  using failure_implies_noncompletion[of q] detect
  by (auto simp: failed_scales_def unsatisfied_scales_def)

lemma least_scales_equal_if_failure_detected:
  fixes a b :: "'a::order"
  assumes detect: "\<And>x. \<not>complete (q x) \<Longrightarrow>
    \<exists>i\<in>approximation_indices. q x (3,i)=Failed"
    and a: "least_pre (failed_scales q) a" and b: "least_pre (unsatisfied_scales q) b"
  shows "a=b"
proof -
  have eq: "failed_scales q=unsatisfied_scales q"
    by (rule scale_sets_equal_if_failure_detected) (fact detect)
  show ?thesis using a b eq by (auto simp: least_pre_def intro: antisym)
qed

lemma initial_completion_interval:
  fixes b :: "'a::linorder"
  assumes ini: "initial {x. complete (q x)}" and least: "least_pre (unsatisfied_scales q) b"
  shows "maximal_initial {x. complete (q x)}={x. x<b}"
proof -
  have lb: "least_in (-{x. complete (q x)}) b"
    using least by (simp add: least_pre_def least_in_def unsatisfied_scales_def)
  show ?thesis using maximal_initial_eq[OF ini] initial_boundary[OF ini lb] by simp
qed

lemma least_failure_unique:
  fixes a b :: "'a::order"
  shows "least_pre (failed_scales q) a \<Longrightarrow>
    least_pre (failed_scales q) b \<Longrightarrow> a=b"
  by (auto simp: least_pre_def intro: antisym)

lemma approximation_token_typed:
  "i\<in>approximation_indices \<Longrightarrow> (3,i)\<in>tokens"
  by (auto simp: approximation_indices_def tokens_def count_def)

lemma least_failure_case:
  assumes least: "least_pre (failed_scales q) a"
  shows "(\<exists>i\<in>approximation_indices. q a (3,i)=Failed) \<and>
    (structural_case (q a)=SingleFailure \<or> structural_case (q a)=ParallelFailure)"
proof -
  obtain i where ii: "i\<in>approximation_indices" and qi: "q a (3,i)=Failed"
    using least by (auto simp: least_pre_def failed_scales_def)
  have mem: "(3,i)\<in>failed_set (q a)"
    using approximation_token_typed[OF ii] qi by (simp add: failed_set_def)
  have pos: "0<card (failed_set (q a))"
    using finite_failed_set[of "q a"] mem by (auto simp: card_gt_0_iff)
  show ?thesis using ii qi pos by (auto simp: structural_case_def)
qed

lemma unformed_scale_separation_control:
  "failed_scales (\<lambda>_::unit. \<lambda>_::token. NotFormed)={} \<and>
    unsatisfied_scales (\<lambda>_::unit. \<lambda>_::token. NotFormed)=UNIV"
proof -
  have witness: "(1::nat)\<in>approximation_indices" by (simp add: approximation_indices_def)
  show ?thesis using witness
    by (auto simp: failed_scales_def unsatisfied_scales_def complete_def)
qed

definition approx_inputs where
  "approx_inputs f e s=((\<forall>t\<in>tokens. fst t=2 \<longrightarrow> s t=SAT) \<and>
    (\<forall>i\<in>approximation_indices. f (3,i) \<and> e (3,i)))"

lemma approx_carrier:
  "t\<in>tokens \<Longrightarrow> fst t=3 \<Longrightarrow> snd t\<in>approximation_indices"
  by (auto simp: tokens_def count_def approximation_indices_def)

lemma approx_predecessor:
  "x\<in>tokens \<Longrightarrow> y\<in>tokens \<Longrightarrow> fst x=3 \<Longrightarrow> edge y x \<Longrightarrow>
    fst y=3 \<or> fst y=2"
  by (auto simp: edge_def)

lemma native_approx_conditions:
  assumes rec: "recurs f e c s" and inputs: "approx_inputs f e s"
  shows "complete s=(\<forall>i\<in>approximation_indices. c (3,i))"
proof
  assume all: "complete s"
  show "\<forall>i\<in>approximation_indices. c (3,i)"
  proof (intro ballI)
    fix i assume ii: "i\<in>approximation_indices"
    have eq: "s (3,i)=state (f (3,i)) (e (3,i)) (predPass s (3,i)) (c (3,i))"
      using rec approximation_token_typed[OF ii] by (simp add: recurs_def step_def)
    have sat: "s (3,i)=SAT" using all ii by (simp add: complete_def)
    show "c (3,i)" using eq sat by (auto simp: state_def split: if_splits)
  qed
next
  assume cond: "\<forall>i\<in>approximation_indices. c (3,i)"
  have sat: "\<And>n t. rank t=n \<Longrightarrow> t\<in>tokens \<Longrightarrow> fst t=3 \<Longrightarrow> s t=SAT"
  proof -
    fix n
    show "\<And>t. rank t=n \<Longrightarrow> t\<in>tokens \<Longrightarrow> fst t=3 \<Longrightarrow> s t=SAT"
    proof (induction n rule: less_induct)
      case (less n)
      fix t
      assume rt: "rank t=n" and tt: "t\<in>tokens" and t3: "fst t=3"
      have ti: "snd t\<in>approximation_indices" by (rule approx_carrier[OF tt t3])
      have pair: "t=(3,snd t)" using t3 by (cases t) simp
      have fe: "f t \<and> e t" using inputs ti pair by (auto simp: approx_inputs_def)
      have ct: "c t" using cond ti pair by auto
      have prior: "predPass s t"
      proof (unfold predPass_def, intro ballI impI)
        fix y assume yy: "y\<in>tokens" and yt: "edge y t"
        show "s y=SAT"
        proof (cases "fst y=3")
          case True
          have rn: "rank y<n" using edge_rank[OF tt yy yt] rt by simp
          show ?thesis by (rule less.IH[OF rn refl yy True])
        next
          case False
          have y2: "fst y=2" using approx_predecessor[OF tt yy t3 yt] False by simp
          show ?thesis using inputs yy y2 by (auto simp: approx_inputs_def)
        qed
      qed
      have eq: "s t=state (f t) (e t) (predPass s t) (c t)"
        using rec tt by (simp add: recurs_def step_def)
      show "s t=SAT" using eq fe ct prior by (simp add: state_def)
    qed
  qed
  show "complete s"
    unfolding complete_def by (intro ballI, rule sat[OF refl approximation_token_typed]) auto
qed

definition encoded_defect :: "(nat\<Rightarrow>ereal)\<Rightarrow>(nat\<Rightarrow>bool)\<Rightarrow>nat\<Rightarrow>ereal" where
  "encoded_defect d q i=(if i\<le>6 then d i else if q i then 0 else 1)"
definition encoded_tolerance :: "(nat\<Rightarrow>ereal)\<Rightarrow>nat\<Rightarrow>ereal" where
  "encoded_tolerance e i=(if i\<le>6 then e i else ereal (1/2))"
definition encoded_condition where
  "encoded_condition d e q i=(if i\<le>6 then d i\<le>e i else q i)"

lemma encoding_exact:
  "encoded_condition d e q i=(encoded_defect d q i\<le>encoded_tolerance e i)"
  by (auto simp: encoded_condition_def encoded_defect_def encoded_tolerance_def one_ereal_def)

locale native_scale_input =
  fixes f e c :: "'a\<Rightarrow>token\<Rightarrow>bool"
    and d :: "'a\<Rightarrow>nat\<Rightarrow>ereal" and eps :: "nat\<Rightarrow>ereal"
    and qual :: "'a\<Rightarrow>nat\<Rightarrow>bool"
  assumes dn: "\<And>x i. i\<in>approximation_indices \<Longrightarrow> 0\<le>d x i"
    and en: "\<And>i. i\<in>approximation_indices \<Longrightarrow> 0\<le>eps i"
    and matching: "\<And>x i. i\<in>approximation_indices \<Longrightarrow>
      c x (3,i)=encoded_condition (d x) eps (qual x) i"
    and inputs: "\<And>x. approx_inputs (f x) (e x) (run (f x) (e x) (c x) 40)"
begin
abbreviation states where "states x \<equiv> run (f x) (e x) (c x) 40"
abbreviation defects where "defects x \<equiv> encoded_defect (d x) (qual x)"
abbreviation tolerances where "tolerances \<equiv> encoded_tolerance eps"
abbreviation signature where "signature x \<equiv> excess_signature (defects x) tolerances"

lemma defect_nonnegative: "i\<in>approximation_indices \<Longrightarrow> 0\<le>defects x i"
  by (simp add: encoded_defect_def dn)
lemma tolerance_nonnegative: "i\<in>approximation_indices \<Longrightarrow> 0\<le>tolerances i"
  by (simp add: encoded_tolerance_def en)

lemma native_completion_threshold:
  "complete (states x)=valid approximation_indices (defects x) tolerances"
proof -
  have eq: "complete (states x)=(\<forall>i\<in>approximation_indices. c x (3,i))"
    by (rule native_approx_conditions) (rule finite_run_solves, rule inputs)
  show ?thesis using eq matching[of _ x] by (simp add: valid_def encoding_exact)
qed

lemma native_saturation_is_valid:
  "i\<in>approximation_indices \<Longrightarrow> defects x i=tolerances i \<Longrightarrow> c x (3,i)"
  using matching by (simp add: encoding_exact)
end

lemma native_validity_initial:
  fixes d :: "'a::preorder\<Rightarrow>nat\<Rightarrow>ereal"
  assumes src: "native_scale_input f e c d eps qual"
    and mono: "\<And>i x y. i\<in>approximation_indices \<Longrightarrow> x\<le>y \<Longrightarrow>
      encoded_defect (d x) (qual x) i\<le>encoded_defect (d y) (qual y) i"
  shows "initial {x. complete (run (f x) (e x) (c x) 40)}"
proof -
  interpret N: native_scale_input f e c d eps qual by (fact src)
  show ?thesis unfolding N.native_completion_threshold
    by (rule monotone_defects_initial) (fact mono)
qed

lemma native_maximal_interval:
  fixes d :: "'a::preorder\<Rightarrow>nat\<Rightarrow>ereal"
  assumes src: "native_scale_input f e c d eps qual"
    and mono: "\<And>i x y. i\<in>approximation_indices \<Longrightarrow> x\<le>y \<Longrightarrow>
      encoded_defect (d x) (qual x) i\<le>encoded_defect (d y) (qual y) i"
  shows "maximal_initial {x. complete (run (f x) (e x) (c x) 40)}=
    {x. complete (run (f x) (e x) (c x) 40)}"
  by (rule maximal_initial_eq, rule native_validity_initial[OF src mono])

lemma native_all_scales_valid:
  fixes f :: "'a::preorder\<Rightarrow>token\<Rightarrow>bool"
  assumes all: "\<And>x. complete (run (f x) (e x) (c x) 40)"
  shows "maximal_initial {x. complete (run (f x) (e x) (c x) 40)}=UNIV"
proof -
  have seteq: "{x. complete (run (f x) (e x) (c x) 40)}=UNIV" using all by simp
  have ini: "initial (UNIV::'a set)" by (simp add: initial_def)
  show ?thesis by (simp only: seteq maximal_initial_eq[OF ini])
qed

lemma native_boundary_nonzero_signature:
  fixes d :: "'a::linorder\<Rightarrow>nat\<Rightarrow>ereal"
  assumes src: "native_scale_input f e c d eps qual"
    and mono: "\<And>i x y. i\<in>approximation_indices \<Longrightarrow> x\<le>y \<Longrightarrow>
      encoded_defect (d x) (qual x) i\<le>encoded_defect (d y) (qual y) i"
    and least: "least_pre (unsatisfied_scales (\<lambda>x. run (f x) (e x) (c x) 40)) b"
  shows "maximal_initial {x. complete (run (f x) (e x) (c x) 40)}={x. x<b} \<and>
    excess_signature (encoded_defect (d b) (qual b)) (encoded_tolerance eps)\<noteq>(\<lambda>_. False) \<and>
    (\<forall>x<b. excess_signature (encoded_defect (d x) (qual x)) (encoded_tolerance eps)=(\<lambda>_. False))"
proof -
  interpret N: native_scale_input f e c d eps qual by (fact src)
  have ini: "initial {x. complete (N.states x)}"
    by (rule native_validity_initial[OF src mono])
  have cut: "maximal_initial {x. complete (N.states x)}={x. x<b}"
    by (rule initial_completion_interval[OF ini least])
  have sig: "\<And>x. (N.signature x=(\<lambda>_. False))=complete (N.states x)"
  proof -
    fix x
    have eq: "(N.signature x=(\<lambda>_. False))=valid approximation_indices (N.defects x) N.tolerances"
      by (rule excess_signature_zero_iff) (auto intro: N.defect_nonnegative N.tolerance_nonnegative)
    show "(N.signature x=(\<lambda>_. False))=complete (N.states x)"
      using eq N.native_completion_threshold by simp
  qed
  have bad: "\<not>complete (N.states b)" using least by (simp add: least_pre_def unsatisfied_scales_def)
  have earlier: "\<And>x. x<b \<Longrightarrow> complete (N.states x)"
    using cut maximal_initial_eq[OF ini] by blast
  show ?thesis using cut bad earlier sig by blast
qed

ML \<open>
val roots = @{thms failure_implies_noncompletion least_failure_after_boundary
  scale_sets_equal_if_failure_detected least_scales_equal_if_failure_detected
  initial_completion_interval least_failure_unique least_failure_case unformed_scale_separation_control
  native_scale_input.native_completion_threshold native_scale_input.native_saturation_is_valid
  native_validity_initial native_maximal_interval native_all_scales_valid native_boundary_nonzero_signature};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
