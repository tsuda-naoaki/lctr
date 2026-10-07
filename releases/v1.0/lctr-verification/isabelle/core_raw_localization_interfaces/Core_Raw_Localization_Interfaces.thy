theory Core_Raw_Localization_Interfaces
  imports Main
begin

definition validity where "validity A p = {a\<in>A. p a}"
definition section_at where "section_at A q b = validity A (q b)"
definition family where "family A J K = {a\<in>A. \<forall>i\<in>J. K i a}"
lemma valid_membership: "a\<in>A \<Longrightarrow> (a\<in>validity A p) = p a"
  by (simp add: validity_def)
lemma section_membership: "a\<in>A \<Longrightarrow> (a\<in>section_at A q b) = q b a"
  by (simp add: section_at_def validity_def)
lemma family_intersection: "family A J K = A \<inter> (\<Inter>i\<in>J. validity A (K i))"
  by (auto simp: family_def validity_def)
lemma empty_family: "family A {} K = A" by (simp add: family_def)

definition approximation where "approximation L K e = {l\<in>L. K (e,l)}"
lemma approximation_membership: "l\<in>L \<Longrightarrow> (l\<in>approximation L K e) = K (e,l)"
  by (simp add: approximation_def)
lemma approximation_downward:
  fixes L :: "'l::linorder set"
  assumes "\<And>l m. l\<in>L \<Longrightarrow> m\<in>L \<Longrightarrow> l\<le>m \<Longrightarrow> K (e,m) \<Longrightarrow> K (e,l)"
  shows "\<forall>l\<in>L. \<forall>m\<in>L. m\<in>approximation L K e \<longrightarrow> l\<le>m \<longrightarrow> l\<in>approximation L K e"
  using assms by (auto simp: approximation_def)

datatype evaluation_state = Sat | Failed | Unformed | Unevaluable
lemma state_exhaustive: "s=Sat \<or> s=Failed \<or> s=Unformed \<or> s=Unevaluable"
  by (cases s) auto
lemma state_distinct: "Sat\<noteq>Failed \<and> Sat\<noteq>Unformed \<and> Sat\<noteq>Unevaluable \<and>
  Failed\<noteq>Unformed \<and> Failed\<noteq>Unevaluable \<and> Unformed\<noteq>Unevaluable" by simp

definition strict_failed where "strict_failed S q e = {t\<in>S. q (Inl (t,e))=Failed}"
definition approx_failed where "approx_failed A q e l = {t\<in>A. q (Inr (t,(e,l)))=Failed}"
definition minima :: "'t::order set \<Rightarrow> 't set" where
  "minima P = {t\<in>P. \<forall>u\<in>P. u\<le>t \<longrightarrow> u=t}"
definition strict_local where "strict_local S q e = minima (strict_failed S q e)"
definition approx_local where "approx_local A q e l = minima (approx_failed A q e l)"
lemma strict_failed_membership:
  "t\<in>S \<Longrightarrow> (t\<in>strict_failed S q e) = (q (Inl (t,e))=Failed)"
  by (simp add: strict_failed_def)
lemma approx_failed_membership:
  "t\<in>A \<Longrightarrow> (t\<in>approx_failed A q e l) = (q (Inr (t,(e,l)))=Failed)"
  by (simp add: approx_failed_def)
lemma strict_localization:
  "(t\<in>strict_local S q e) = (t\<in>strict_failed S q e \<and> (\<forall>u\<in>strict_failed S q e. u\<le>t \<longrightarrow> u=t))"
  by (simp add: strict_local_def minima_def)
lemma approx_localization:
  "(t\<in>approx_local A q e l) = (t\<in>approx_failed A q e l \<and> (\<forall>u\<in>approx_failed A q e l. u\<le>t \<longrightarrow> u=t))"
  by (simp add: approx_local_def minima_def)
lemma localization_subset: "minima P \<subseteq> P" by (auto simp: minima_def)
lemma localization_antichain:
  "x\<in>minima P \<Longrightarrow> y\<in>minima P \<Longrightarrow> x\<le>y \<Longrightarrow> x=y"
  by (auto simp: minima_def)

definition nontrans where
  "nontrans Y R = (\<exists>x\<in>Y. \<exists>y\<in>Y. \<exists>z\<in>Y. R x y \<and> R y z \<and> \<not>R x z)"
lemma nontrans_exact:
  "nontrans Y R = (\<exists>x\<in>Y. \<exists>y\<in>Y. \<exists>z\<in>Y. R x y \<and> R y z \<and> \<not>R x z)"
  by (simp add: nontrans_def)
lemma nontrans_iff_not_transitive:
  "nontrans Y R = (\<not>(\<forall>x\<in>Y. \<forall>y\<in>Y. \<forall>z\<in>Y. R x y \<longrightarrow> R y z \<longrightarrow> R x z))"
  by (auto simp: nontrans_def)

definition refsplit where "refsplit P I C = (\<Union>i\<in>I. C i, P - (\<Union>i\<in>I. C i))"
lemma split_components:
  "fst (refsplit P I C) = (\<Union>i\<in>I. C i) \<and> snd (refsplit P I C) = P - (\<Union>i\<in>I. C i)"
  by (simp add: refsplit_def)
lemma split_empty: "refsplit P {} C = ({},P)" by (simp add: refsplit_def)
lemma split_decomposition:
  assumes "\<And>i. i\<in>I \<Longrightarrow> C i \<subseteq> P"
  shows "P = fst (refsplit P I C) \<union> snd (refsplit P I C) \<and>
    fst (refsplit P I C) \<inter> snd (refsplit P I C) = {}"
  using assms by (auto simp: refsplit_def)

ML \<open>
val roots = @{thms valid_membership section_membership family_intersection empty_family
  approximation_membership approximation_downward state_exhaustive state_distinct
  strict_failed_membership approx_failed_membership strict_localization approx_localization
  localization_subset localization_antichain nontrans_exact nontrans_iff_not_transitive
  split_components split_empty split_decomposition};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
