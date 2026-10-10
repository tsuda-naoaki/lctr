theory Negative_Controls
imports Region_Refinement_Isabelle
        Law_Candidate_Relation_Isabelle
        Global_Gluing_Isabelle
begin

lemma refinement_fails_without_shared_family:
  defines "P \<equiv> {False, True}"
      and "I0 \<equiv> {0::nat}"
      and "I1 \<equiv> {0::nat}"
      and "F0 \<equiv> (\<lambda>i::nat. if i = 0 then {False} else {})"
      and "F1 \<equiv> (\<lambda>i::nat. if i = 0 then {True} else {})"
  shows "I0 \<subseteq> I1"
    and "(\<forall>i\<in>I0. F0 i \<subseteq> P)"
    and "(\<forall>i\<in>I1. F1 i \<subseteq> P)"
    and "\<not> covered I0 F0 \<subseteq> covered I1 F1"
  unfolding P_def I0_def I1_def F0_def F1_def covered_def by auto

lemma refinement_fails_without_index_inclusion:
  defines "P \<equiv> {False}"
      and "I0 \<equiv> {0::nat}"
      and "I1 \<equiv> {}"
      and "F0 \<equiv> (\<lambda>i::nat. {False})"
      and "F1 \<equiv> (\<lambda>i::nat. {False})"
  shows "(\<forall>i\<in>I0. F0 i \<subseteq> P)"
    and "(\<forall>i\<in>I1. F1 i \<subseteq> P)"
    and "(\<forall>i\<in>I0. F0 i = F1 i)"
    and "\<not> covered I0 F0 \<subseteq> covered I1 F1"
  unfolding P_def I0_def I1_def F0_def F1_def covered_def by auto

lemma relation_domain_does_not_force_total_extension_uniqueness:
  defines "X \<equiv> (UNIV :: bool set)"
      and "Y \<equiv> (UNIV :: bool set)"
      and "R \<equiv> {(False, False)}"
      and "f \<equiv> (\<lambda>_::bool. False)"
      and "g \<equiv> (\<lambda>x::bool. x)"
  shows "right_unique X Y R"
    and "cand_rel_dom X Y R = {False}"
    and "R = restricted_graph (cand_rel_dom X Y R) f"
    and "R = restricted_graph (cand_rel_dom X Y R) g"
    and "f \<noteq> g"
proof -
  show "right_unique X Y R"
    unfolding X_def Y_def R_def right_unique_def by auto
  show "cand_rel_dom X Y R = {False}"
    unfolding X_def Y_def R_def cand_rel_dom_def by auto
  show "R = restricted_graph (cand_rel_dom X Y R) f"
    unfolding X_def Y_def R_def f_def cand_rel_dom_def restricted_graph_def by auto
  show "R = restricted_graph (cand_rel_dom X Y R) g"
    unfolding X_def Y_def R_def g_def cand_rel_dom_def restricted_graph_def by auto
  show "f \<noteq> g"
  proof
    assume fg: "f = g"
    have at_true: "f True = g True"
      using fun_cong[OF fg, of True] .
    show False
      using at_true unfolding f_def g_def by simp
  qed
qed

lemma supplied_designated_output_negative_control:
  assumes "y \<in> out_notG Slots"
  shows "gen_def (dep_repr C Slots) y (insert y (ctx_notG C))"
  using supplied_output_is_generated[OF assms] .

end
