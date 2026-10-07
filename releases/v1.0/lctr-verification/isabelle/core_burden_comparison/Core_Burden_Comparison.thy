theory Core_Burden_Comparison
  imports Main
begin

definition burden where
  "burden R m F = {s. \<exists>a\<in>F. \<exists>b. R a b \<and> m b = s}"

lemma equality_iff_empty_symmetric_difference:
  "burden R m F = burden R m G \<longleftrightarrow>
    (burden R m F - burden R m G) \<union> (burden R m G - burden R m F) = {}"
  by blast

lemma one_sided_separation:
  assumes ha: "a \<in> F" and hn: "\<not> burden R m {a} \<subseteq> burden R m G"
  shows "burden R m F - burden R m G \<noteq> {}"
  using ha hn unfolding burden_def by blast

lemma two_sided_incomparability:
  assumes hf: "\<exists>a\<in>F. \<not> burden R m {a} \<subseteq> burden R m G"
    and hg: "\<exists>a\<in>G. \<not> burden R m {a} \<subseteq> burden R m F"
  shows "\<not> burden R m F \<subseteq> burden R m G \<and>
    \<not> burden R m G \<subseteq> burden R m F"
proof -
  obtain a where a: "a \<in> F" "\<not> burden R m {a} \<subseteq> burden R m G"
    using hf by blast
  obtain b where b: "b \<in> G" "\<not> burden R m {b} \<subseteq> burden R m F"
    using hg by blast
  have left: "burden R m F - burden R m G \<noteq> {}"
    by (rule one_sided_separation[OF a])
  have right: "burden R m G - burden R m F \<noteq> {}"
    by (rule one_sided_separation[OF b])
  show ?thesis using left right by blast
qed

ML \<open>
val roots = @{thms equality_iff_empty_symmetric_difference one_sided_separation two_sided_incomparability};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
