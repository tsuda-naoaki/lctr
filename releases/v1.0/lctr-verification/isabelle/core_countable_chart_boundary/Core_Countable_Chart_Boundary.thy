theory Core_Countable_Chart_Boundary
  imports "HOL-Analysis.Uncountable_Sets"
begin

lemma real_open_countable_empty:
  fixes S :: "real set"
  assumes hc: "countable S" and ho: "open S"
  shows "S = {}"
proof (rule ccontr)
  assume "S \<noteq> {}"
  then obtain x where hx: "x \<in> S" by blast
  obtain e where he: "0 < e" and hs: "ball x e \<subseteq> S"
    using ho hx open_contains_ball by blast
  have "countable (ball x e)" by (rule countable_subset[OF hs hc])
  moreover have "uncountable (ball x e)" by (rule uncountable_ball[OF he])
  ultimately show False by contradiction
qed

lemma open_chart_domain_empty:
  fixes f :: "'a \<Rightarrow> real"
  assumes hc: "countable A" and ho: "open (f ` A)"
  shows "A = {}"
proof -
  have "f ` A = {}" by (rule real_open_countable_empty[OF countable_image[OF hc] ho])
  then show ?thesis by simp
qed

lemma no_nonempty_countable_cover:
  fixes H :: "'a set" and D :: "'i \<Rightarrow> 'a set" and f :: "'i \<Rightarrow> 'a \<Rightarrow> real"
  assumes hc: "countable H" and hn: "H \<noteq> {}"
    and hd: "\<And>i. D i \<subseteq> H"
    and ho: "\<And>i. open (f i ` D i)"
  shows "\<not> (\<forall>t\<in>H. \<exists>i. t \<in> D i)"
proof
  assume hcover: "\<forall>t\<in>H. \<exists>i. t \<in> D i"
  obtain t where ht: "t \<in> H" using hn by blast
  obtain i where hi: "t \<in> D i" using hcover ht by blast
  have dc: "countable (D i)" by (rule countable_subset[OF hd hc])
  have "D i = {}" by (rule open_chart_domain_empty[OF dc ho])
  with hi show False by simp
qed

lemma countable_tagged_sources_iff:
  "countable (A \<times> (UNIV :: nat set)) \<longleftrightarrow> countable A"
proof
  assume h: "countable (A \<times> (UNIV :: nat set))"
  have eq: "fst ` (A \<times> (UNIV :: nat set)) = A" by auto
  have "countable (fst ` (A \<times> (UNIV :: nat set)))" by (rule countable_image[OF h])
  then show "countable A" by (simp only: eq)
next
  assume "countable A"
  then show "countable (A \<times> (UNIV :: nat set))" by simp
qed

lemma each_source_countable:
  fixes r :: real
  shows "countable (range (\<lambda>n::nat. (r,n)))"
  by simp

lemma all_sources_uncountable:
  "\<not> countable ((UNIV :: real set) \<times> (UNIV :: nat set))"
  using countable_tagged_sources_iff[of "UNIV :: real set"] uncountable_UNIV_real by blast

lemma empty_time_domain_allows_empty_cover:
  "(\<forall>t\<in>({} :: nat set). \<exists>i::unit. t \<in> ({} :: nat set)) \<and>
   open ((\<lambda>_::nat. (0::real)) ` {})"
  by simp

ML \<open>
val roots = @{thms real_open_countable_empty open_chart_domain_empty no_nonempty_countable_cover countable_tagged_sources_iff each_source_countable all_sources_uncountable empty_time_domain_allows_empty_cover};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>

end
