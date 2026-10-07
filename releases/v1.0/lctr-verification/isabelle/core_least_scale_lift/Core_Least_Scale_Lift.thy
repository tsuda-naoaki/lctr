theory Core_Least_Scale_Lift
  imports Main
begin

definition least_at :: "'l::order set \<Rightarrow> 'l \<Rightarrow> bool" where
  "least_at A l = (l\<in>A \<and> (\<forall>m\<in>A. l\<le>m))"
definition first_domain where "first_domain X S = {x\<in>X. \<exists>l. least_at (S x) l}"
definition first_value where "first_value S x = (THE l. least_at (S x) l)"
definition first_graph where "first_graph X S = {(x,l). x\<in>X \<and> least_at (S x) l}"

lemma least_at_unique: "least_at A l \<Longrightarrow> least_at A m \<Longrightarrow> l=m"
  by (auto simp: least_at_def intro: antisym)
lemma domain_exact:
  "x\<in>X \<Longrightarrow> (x\<in>first_domain X S) = (\<exists>l\<in>S x. \<forall>m\<in>S x. l\<le>m)"
  by (auto simp: first_domain_def least_at_def)
lemma value_is_least:
  assumes h: "x\<in>first_domain X S"
  shows "least_at (S x) (first_value S x)"
proof -
  obtain l where l: "least_at (S x) l" using h by (auto simp: first_domain_def)
  have eq: "first_value S x=l"
    unfolding first_value_def
  proof (rule the_equality)
    show "least_at (S x) l" by (fact l)
  next
    fix m assume m: "least_at (S x) m"
    show "m=l" by (rule least_at_unique[OF m l])
  qed
  show ?thesis by (simp only: eq l)
qed
lemma value_unique:
  "x\<in>first_domain X S \<Longrightarrow> least_at (S x) l \<Longrightarrow> first_value S x=l"
  by (rule least_at_unique, rule value_is_least, assumption, assumption)
lemma graph_exact:
  assumes x: "x\<in>X"
  shows "((x,l)\<in>first_graph X S) = (x\<in>first_domain X S \<and> first_value S x=l)"
proof
  assume h: "(x,l)\<in>first_graph X S"
  have least: "least_at (S x) l" using h by (simp add: first_graph_def)
  have dom: "x\<in>first_domain X S" using x least by (auto simp: first_domain_def)
  show "x\<in>first_domain X S \<and> first_value S x=l"
    using dom value_unique[OF dom least] by simp
next
  assume h: "x\<in>first_domain X S \<and> first_value S x=l"
  have "least_at (S x) l" using value_is_least[OF h[THEN conjunct1]] h by simp
  then show "(x,l)\<in>first_graph X S" using x by (simp add: first_graph_def)
qed
lemma graph_singlevalued:
  "(x,l)\<in>first_graph X S \<Longrightarrow> (x,m)\<in>first_graph X S \<Longrightarrow> l=m"
  by (auto simp: first_graph_def intro: least_at_unique)
lemma empty_fibre_undefined: "S x={} \<Longrightarrow> x\<notin>first_domain X S"
  by (auto simp: first_domain_def least_at_def)
lemma same_sets_domain: "S x=T x \<Longrightarrow> (x\<in>first_domain X S) = (x\<in>first_domain X T)"
  by (simp add: first_domain_def)
lemma same_sets_value:
  "S x=T x \<Longrightarrow> x\<in>first_domain X S \<Longrightarrow> x\<in>first_domain X T \<Longrightarrow> first_value S x=first_value T x"
  by (simp add: first_value_def)

ML \<open>
val roots = @{thms domain_exact value_is_least value_unique graph_exact graph_singlevalued
  empty_fibre_undefined same_sets_domain same_sets_value};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
