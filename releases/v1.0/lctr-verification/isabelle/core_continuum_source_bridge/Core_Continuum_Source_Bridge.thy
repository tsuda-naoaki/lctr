theory Core_Continuum_Source_Bridge
  imports LCTR_Core_Continuum_Encoding.Core_Continuum_Encoding
begin

definition approx_domain :: "('e \<Rightarrow> 'l \<Rightarrow> token \<Rightarrow> eval_state) \<Rightarrow> ('e \<times> 'l) set" where
  "approx_domain s = {x. \<forall>i\<in>approx_set. s (fst x) (snd x) i=Sat}"
definition scale_fibre where "scale_fibre s ev = {l. (ev,l)\<in>approx_domain s}"
definition condition_all where "condition_all c = (\<forall>i\<in>approx_set. c i)"

lemma fibre_membership: "(l\<in>scale_fibre s ev) = ((ev,l)\<in>approx_domain s)"
  by (simp add: scale_fibre_def)

lemma eight_conditions:
  fixes s :: "'e \<Rightarrow> 'l \<Rightarrow> token \<Rightarrow> eval_state"
    and d eps :: "token \<Rightarrow> ereal"
  assumes recurs: "s ev l=eval_update edges f e c (s ev l)"
    and inp: "input_sat f e (s ev l)"
    and dn: "\<And>i. i\<in>approx_set \<Longrightarrow> snd i\<le>6 \<Longrightarrow> 0\<le>d i"
    and en: "\<And>i. i\<in>approx_set \<Longrightarrow> snd i\<le>6 \<Longrightarrow> 0\<le>eps i"
    and matching: "\<And>i. i\<in>approx_set \<Longrightarrow> c i=paper_condition d eps b i"
  shows "((l\<in>scale_fibre s ev) = ((ev,l)\<in>approx_domain s)) \<and>
    (((ev,l)\<in>approx_domain s) = condition_all c) \<and>
    (condition_all c = (\<forall>i\<in>approx_set. c i)) \<and>
    ((\<forall>i\<in>approx_set. c i) = (\<forall>i\<in>approx_set. paper_defect d b i\<le>paper_tolerance eps i)) \<and>
    ((\<forall>i\<in>approx_set. paper_defect d b i\<le>paper_tolerance eps i) =
      (\<forall>i\<in>approx_set. 0\<le>margin (paper_tolerance eps i) (paper_defect d b i))) \<and>
    ((\<forall>i\<in>approx_set. 0\<le>margin (paper_tolerance eps i) (paper_defect d b i)) =
      (\<forall>i\<in>approx_set. excess (paper_tolerance eps i) (paper_defect d b i)=0)) \<and>
    ((\<forall>i\<in>approx_set. excess (paper_tolerance eps i) (paper_defect d b i)=0) =
      (exceeded approx_set (paper_defect d b) (paper_tolerance eps)={}))"
proof -
  interpret F: source_approximation_encoding f e c "s ev l" d eps b
    by standard (fact recurs, fact inp, fact dn, fact en, fact matching)
  have q: "((\<forall>i\<in>approx_set. s ev l i=Sat) = valid approx_set (paper_defect d b) (paper_tolerance eps)) \<and>
    ((\<forall>i\<in>approx_set. s ev l i=Sat) = (\<forall>i\<in>approx_set. 0\<le>margin (paper_tolerance eps i) (paper_defect d b i))) \<and>
    ((\<forall>i\<in>approx_set. s ev l i=Sat) = (\<forall>i\<in>approx_set. excess (paper_tolerance eps i) (paper_defect d b i)=0)) \<and>
    ((\<forall>i\<in>approx_set. s ev l i=Sat) = (exceeded approx_set (paper_defect d b) (paper_tolerance eps)={}))"
    by (rule F.source_quantitative_validity)
  have a: "(\<forall>i\<in>approx_set. s ev l i=Sat) = (\<forall>i\<in>approx_set. c i)"
    by (rule approx_states_iff_conditions[OF recurs inp])
  show ?thesis using q a
    unfolding scale_fibre_def approx_domain_def condition_all_def valid_def
    by auto
qed

ML \<open>
val roots = @{thms fibre_membership eight_conditions};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
