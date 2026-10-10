theory Core_Validity_Maximum
  imports Main
begin

definition family_greatest where
  "family_greatest F U \<longleftrightarrow> U \<in> F \<and> (\<forall>V\<in>F. V \<subseteq> U)"

lemma greatest_equals_union:
  "family_greatest F U \<Longrightarrow> U = \<Union>F"
  unfolding family_greatest_def by auto

lemma union_is_greatest:
  "\<Union>F \<in> F \<Longrightarrow> family_greatest F (\<Union>F)"
  unfolding family_greatest_def by auto

lemma maximum_exists_iff_union_member:
  "(\<exists>U. family_greatest F U) \<longleftrightarrow> \<Union>F \<in> F"
proof
  assume "\<exists>U. family_greatest F U"
  then obtain U where h: "family_greatest F U" by blast
  have "U = \<Union>F" by (rule greatest_equals_union[OF h])
  with h show "\<Union>F \<in> F" unfolding family_greatest_def by simp
next
  assume h: "\<Union>F \<in> F"
  show "\<exists>U. family_greatest F U" using union_is_greatest[OF h] by blast
qed

lemma maximum_unique:
  "family_greatest F U \<Longrightarrow> family_greatest F V \<Longrightarrow> U = V"
  unfolding family_greatest_def by auto

lemma maximum_validity_domain:
  assumes typed: "\<And>U. U \<in> F \<Longrightarrow> U \<subseteq> V" and member: "\<Union>F \<in> F"
  shows "(\<exists>!U. family_greatest F U) \<and> \<Union>F \<subseteq> V"
proof
  show "\<exists>!U. family_greatest F U"
  proof (rule ex1I[of _ "\<Union>F"])
    show "family_greatest F (\<Union>F)" by (rule union_is_greatest[OF member])
    fix U assume "family_greatest F U"
    then show "U = \<Union>F" by (rule greatest_equals_union)
  qed
  show "\<Union>F \<subseteq> V" by (rule typed[OF member])
qed

lemma empty_family_no_maximum:
  "\<not> (\<exists>U. family_greatest {} U)"
  by (simp add: family_greatest_def)

lemma incomparable_family_no_maximum:
  "\<not> (\<exists>U. family_greatest {{False},{True}} U)"
  by (auto simp: family_greatest_def)

definition full_domain where
  "full_domain strict approximation = (strict \<times> UNIV) \<inter> approximation"

lemma full_domain_membership:
  "(e,l) \<in> full_domain strict approximation \<longleftrightarrow>
    e \<in> strict \<and> (e,l) \<in> approximation"
  by (simp add: full_domain_def)

ML \<open>
val roots = @{thms greatest_equals_union union_is_greatest maximum_exists_iff_union_member
  maximum_unique maximum_validity_domain empty_family_no_maximum
  incomparable_family_no_maximum full_domain_membership};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int (length roots));
\<close>
end
