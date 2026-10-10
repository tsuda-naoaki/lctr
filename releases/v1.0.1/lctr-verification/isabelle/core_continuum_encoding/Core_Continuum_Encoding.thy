theory Core_Continuum_Encoding
  imports LCTR_Core_Continuum_Topology.Core_Continuum_Topology
begin

definition bool_defect :: "bool\<Rightarrow>ereal" where "bool_defect b=(if b then 0 else 1)"
definition half :: ereal where "half=ereal (1/2)"
lemma half_exact: "half=(1/2::ereal)" by (simp add: half_def one_ereal_def numeral_eq_ereal)
lemma midpoint_encoding: "(bool_defect b\<le>half)=b"
  by (cases b) (simp_all add: bool_defect_def half_def one_ereal_def)
lemma midpoint_margin:
  "margin half (bool_defect b) = (if b then ereal (1/2) else -ereal (1/2))"
  by (cases b) (simp_all add: bool_defect_def half_def margin_def one_ereal_def)
lemma midpoint_positive_margin: "(0<margin half (bool_defect b))=b"
  by (simp add: midpoint_margin)

definition paper_condition where
  "paper_condition d eps b i = (if snd i\<le>6 then d i\<le>eps i else b i)"
definition paper_defect where
  "paper_defect d b i = (if snd i\<le>6 then d i else bool_defect (b i))"
definition paper_tolerance where
  "paper_tolerance eps i = (if snd i\<le>6 then eps i else half)"

lemma nine_component_encoding:
  "paper_condition d eps b i = (paper_defect d b i\<le>paper_tolerance eps i)"
  by (simp add: paper_condition_def paper_defect_def paper_tolerance_def midpoint_encoding)
lemma first_six_preserved:
  "snd i\<le>6 \<Longrightarrow> paper_defect d b i=d i \<and> paper_tolerance eps i=eps i"
  by (simp add: paper_defect_def paper_tolerance_def)
lemma final_three_margin:
  "\<not>snd i\<le>6 \<Longrightarrow> margin (paper_tolerance eps i) (paper_defect d b i)=
    (if b i then ereal (1/2) else -ereal (1/2))"
  by (simp add: paper_defect_def paper_tolerance_def midpoint_margin)

locale source_approximation_encoding =
  fixes f e c :: "token\<Rightarrow>bool" and s :: "token\<Rightarrow>eval_state"
    and d eps :: "token\<Rightarrow>ereal" and b :: "token\<Rightarrow>bool"
  assumes recurs: "s=eval_update edges f e c s" and inp: "input_sat f e s"
    and dn: "\<And>i. i\<in>approx_set \<Longrightarrow> snd i\<le>6 \<Longrightarrow> 0\<le>d i"
    and en: "\<And>i. i\<in>approx_set \<Longrightarrow> snd i\<le>6 \<Longrightarrow> 0\<le>eps i"
    and matching: "\<And>i. i\<in>approx_set \<Longrightarrow> c i=paper_condition d eps b i"
begin
lemma defect_nonnegative: "i\<in>approx_set \<Longrightarrow> 0\<le>paper_defect d b i"
  by (simp add: paper_defect_def bool_defect_def dn)
lemma tolerance_nonnegative: "i\<in>approx_set \<Longrightarrow> 0\<le>paper_tolerance eps i"
  by (simp add: paper_tolerance_def half_def en)
lemma source_quantitative_validity:
  "((\<forall>i\<in>approx_set. s i=Sat) = valid approx_set (paper_defect d b) (paper_tolerance eps)) \<and>
   ((\<forall>i\<in>approx_set. s i=Sat) = (\<forall>i\<in>approx_set. 0\<le>margin (paper_tolerance eps i) (paper_defect d b i))) \<and>
   ((\<forall>i\<in>approx_set. s i=Sat) = (\<forall>i\<in>approx_set. excess (paper_tolerance eps i) (paper_defect d b i)=0)) \<and>
   ((\<forall>i\<in>approx_set. s i=Sat) = (exceeded approx_set (paper_defect d b) (paper_tolerance eps)={}))"
proof -
  have enc: "\<And>i. i\<in>approx_set \<Longrightarrow> c i=(paper_defect d b i\<le>paper_tolerance eps i)"
    using matching nine_component_encoding by simp
  show ?thesis by (rule quantitative_validity[where f=f and e=e and c=c and s=s
    and d="paper_defect d b" and eps="paper_tolerance eps",
    OF recurs inp defect_nonnegative tolerance_nonnegative enc])
qed
lemma source_robust_validity:
  "operational_robust s (paper_defect d b) (paper_tolerance eps) =
    (\<forall>i\<in>approx_set. 0<margin (paper_tolerance eps i) (paper_defect d b i))"
proof -
  have enc: "\<And>i. i\<in>approx_set \<Longrightarrow> c i=(paper_defect d b i\<le>paper_tolerance eps i)"
    using matching nine_component_encoding by simp
  show ?thesis by (rule robust_positive_iff[where f=f and e=e and c=c and s=s
    and d="paper_defect d b" and eps="paper_tolerance eps",
    OF recurs inp defect_nonnegative tolerance_nonnegative enc])
qed
end

lemma wrong_threshold_controls:
  "\<not>0<margin 0 (bool_defect True)" "bool_defect False\<le>(1::ereal)"
  by (simp_all add: bool_defect_def margin_def)

ML \<open>
val roots = @{thms half_exact midpoint_encoding midpoint_margin midpoint_positive_margin
  nine_component_encoding first_six_preserved final_three_margin
  source_approximation_encoding.source_quantitative_validity source_approximation_encoding.source_robust_validity
  wrong_threshold_controls};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
