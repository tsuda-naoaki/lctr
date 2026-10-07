theory Core_First_Boundary
  imports Complex_Main
begin

definition least_outside :: "'a::linorder set \<Rightarrow> 'a \<Rightarrow> bool" where
  "least_outside V a = (a \<notin> V \<and> (\<forall>x. x \<notin> V \<longrightarrow> a \<le> x))"
definition boundary_data :: "'a::linorder set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b) set" where
  "boundary_data V sig = {p. least_outside V (fst p) \<and> snd p = sig (fst p)}"

lemma boundary_singleton:
  assumes "least_outside V a"
  shows "boundary_data V sig = {(a,sig a)}"
proof (rule set_eqI)
  fix p
  show "p \<in> boundary_data V sig \<longleftrightarrow> p \<in> {(a,sig a)}"
  proof
    assume hp: "p \<in> boundary_data V sig"
    have eq: "fst p = a"
      using hp assms unfolding boundary_data_def least_outside_def by (auto intro: antisym)
    have val: "snd p = sig a" using hp eq unfolding boundary_data_def by auto
    show "p \<in> {(a,sig a)}" using eq val by (cases p) auto
  next
    assume "p \<in> {(a,sig a)}"
    then show "p \<in> boundary_data V sig" using assms unfolding boundary_data_def by simp
  qed
qed

lemma boundary_empty_iff:
  "boundary_data V sig = {} \<longleftrightarrow> \<not> (\<exists>a. least_outside V a)"
  unfolding boundary_data_def by auto

lemma boundary_empty_or_singleton:
  "boundary_data V sig = {} \<or> (\<exists>a. boundary_data V sig = {(a,sig a)})"
proof (cases "\<exists>a. least_outside V a")
  case True
  then obtain a where ha: "least_outside V a" by auto
  have "boundary_data V sig = {(a,sig a)}" by (rule boundary_singleton[OF ha])
  then show ?thesis by auto
next
  case False
  then have "boundary_data V sig = {}" by (simp add: boundary_empty_iff)
  then show ?thesis by auto
qed

lemma full_validity_has_no_boundary: "boundary_data UNIV sig = {}"
  unfolding boundary_data_def least_outside_def by simp

lemma no_least_boundary_control:
  "boundary_data {x::real. x \<le> 0} sig = {}"
proof (subst boundary_empty_iff, clarify)
  fix a
  assume h: "least_outside {x::real. x \<le> 0} a"
  have positive: "0 < a" using h unfolding least_outside_def by auto
  have half: "a / 2 \<notin> {x::real. x \<le> 0}" using positive by auto
  have lower: "a \<le> a / 2" using h half unfolding least_outside_def by blast
  show False using positive lower by linarith
qed

lemma boundary_presence_different_from_zero_signature:
  "boundary_data {x::nat. x < 1} (\<lambda>_. (\<lambda>i::nat. False)) = {(1,\<lambda>i::nat. False)}"
  by (rule boundary_singleton) (auto simp: least_outside_def)

ML \<open>
val roots = @{thms boundary_singleton boundary_empty_iff boundary_empty_or_singleton full_validity_has_no_boundary no_least_boundary_control boundary_presence_different_from_zero_signature};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
