theory Carrier_Jet_Transport
  imports "HOL-Analysis.Analysis"
begin

definition carrier_jet_domain where
  "carrier_jet_domain (k::nat) C V = {v\<in>PiE {..k} (\<lambda>_. C). v 0\<in>V}"
definition carrier_jet_push where
  "carrier_jet_push (k::nat) F v = restrict (\<lambda>n. F (v n)) {..k}"
definition carrier_ambient_push where
  "carrier_ambient_push k F p = (fst p,carrier_jet_push k F (snd p))"

lemma carrier_jet_component: "n\<le>k \<Longrightarrow> carrier_jet_push k F v n=F (v n)"
  by (simp add: carrier_jet_push_def restrict_def)

locale carrier_bijection =
  fixes F :: "'a \<Rightarrow> 'b" and G :: "'b \<Rightarrow> 'a" and C :: "'a set" and D :: "'b set"
  assumes F_map: "\<And>x. x\<in>C \<Longrightarrow> F x\<in>D"
    and G_map: "\<And>y. y\<in>D \<Longrightarrow> G y\<in>C"
    and GF: "\<And>x. x\<in>C \<Longrightarrow> G (F x)=x"
    and FG: "\<And>y. y\<in>D \<Longrightarrow> F (G y)=y"
begin

lemma jet_forward_typed:
  assumes v: "v\<in>carrier_jet_domain k C V"
  shows "carrier_jet_push k F v\<in>carrier_jet_domain k D (F ` V)"
  using v by (auto simp: carrier_jet_domain_def carrier_jet_push_def restrict_def PiE_def Pi_iff extensional_def intro: F_map)

lemma jet_reverse_typed:
  assumes V: "V\<subseteq>C" and v: "v\<in>carrier_jet_domain k D (F ` V)"
  shows "carrier_jet_push k G v\<in>carrier_jet_domain k C V"
proof -
  have v0: "v 0\<in>F ` V" using v by (simp add: carrier_jet_domain_def)
  obtain z where z: "z\<in>V" "v 0=F z" using v0 by blast
  have zC: "z\<in>C" using V z(1) by blast
  have base: "G (v 0)\<in>V" using z GF[OF zC] by simp
  show ?thesis using v base
    by (auto simp: carrier_jet_domain_def carrier_jet_push_def restrict_def PiE_def Pi_iff extensional_def intro: G_map)
qed

lemma jet_left_inverse:
  assumes v: "v\<in>carrier_jet_domain k C V"
  shows "carrier_jet_push k G (carrier_jet_push k F v)=v"
  using v by (auto simp: carrier_jet_domain_def carrier_jet_push_def restrict_def PiE_def Pi_iff extensional_def fun_eq_iff GF)

lemma jet_right_inverse:
  assumes v: "v\<in>carrier_jet_domain k D W"
  shows "carrier_jet_push k F (carrier_jet_push k G v)=v"
  using v by (auto simp: carrier_jet_domain_def carrier_jet_push_def restrict_def PiE_def Pi_iff extensional_def fun_eq_iff FG)

lemma jet_bijection:
  assumes V: "V\<subseteq>C"
  shows "bij_betw (carrier_jet_push k F) (carrier_jet_domain k C V) (carrier_jet_domain k D (F ` V))"
proof (rule bij_betwI)
  show "carrier_jet_push k F \<in> carrier_jet_domain k C V \<rightarrow> carrier_jet_domain k D (F ` V)"
    using jet_forward_typed by blast
  show "carrier_jet_push k G \<in> carrier_jet_domain k D (F ` V) \<rightarrow> carrier_jet_domain k C V"
    using jet_reverse_typed[OF V] by blast
  show "\<And>x. x\<in>carrier_jet_domain k C V \<Longrightarrow> carrier_jet_push k G (carrier_jet_push k F x)=x"
    by (rule jet_left_inverse)
  show "\<And>x. x\<in>carrier_jet_domain k D (F ` V) \<Longrightarrow> carrier_jet_push k F (carrier_jet_push k G x)=x"
    by (rule jet_right_inverse)
qed

lemma carrier_ambient_inverse:
  "p\<in>U \<times> carrier_jet_domain k C V \<Longrightarrow> carrier_ambient_push k G (carrier_ambient_push k F p)=p"
  by (cases p) (auto simp: carrier_ambient_push_def jet_left_inverse)

lemma carrier_relation_membership:
  assumes R: "R\<subseteq>U \<times> carrier_jet_domain k C V" and p: "p\<in>U \<times> carrier_jet_domain k C V"
  shows "carrier_ambient_push k F p\<in>carrier_ambient_push k F ` R \<longleftrightarrow> p\<in>R"
proof
  assume "carrier_ambient_push k F p\<in>carrier_ambient_push k F ` R"
  then obtain r where r: "r\<in>R" "carrier_ambient_push k F p=carrier_ambient_push k F r" by blast
  have rt: "r\<in>U \<times> carrier_jet_domain k C V" using R r(1) by blast
  have "p=r" using arg_cong[OF r(2), of "carrier_ambient_push k G"]
    carrier_ambient_inverse[OF p] carrier_ambient_inverse[OF rt] by simp
  then show "p\<in>R" using r(1) by simp
next
  assume "p\<in>R" then show "carrier_ambient_push k F p\<in>carrier_ambient_push k F ` R" by blast
qed

lemma carrier_relation_recovered:
  assumes R: "R\<subseteq>U \<times> carrier_jet_domain k C V"
  shows "carrier_ambient_push k G ` (carrier_ambient_push k F ` R)=R"
proof -
  have e: "\<And>p. p\<in>R \<Longrightarrow> carrier_ambient_push k G (carrier_ambient_push k F p)=p"
    using R carrier_ambient_inverse by blast
  have "carrier_ambient_push k G ` (carrier_ambient_push k F ` R)=(carrier_ambient_push k G \<circ> carrier_ambient_push k F) ` R"
    by (rule image_comp)
  also have "\<dots>=id ` R"
    by (rule image_cong[OF refl]) (simp only: comp_apply id_apply; rule e; assumption)
  also have "\<dots>=R" by simp
  finally show ?thesis .
qed

end

lemma carrier_numeric_time_preserved: "fst (carrier_ambient_push k F p)=fst p"
  by (simp add: carrier_ambient_push_def)

ML \<open>
val roots = @{thms carrier_jet_component carrier_bijection.jet_forward_typed carrier_bijection.jet_reverse_typed
 carrier_bijection.jet_left_inverse carrier_bijection.jet_right_inverse carrier_bijection.jet_bijection
 carrier_bijection.carrier_ambient_inverse carrier_bijection.carrier_relation_membership
 carrier_bijection.carrier_relation_recovered carrier_numeric_time_preserved};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
