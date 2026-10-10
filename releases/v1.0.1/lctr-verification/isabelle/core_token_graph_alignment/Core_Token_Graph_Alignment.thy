theory Core_Token_Graph_Alignment
  imports LCTR_Core_Token_Graph.Core_Token_Graph
begin
lemmas token_card = Core_Token_Graph.token_card

lemma series_card:
  "\<forall>s<6. card {t\<in>tokens. fst t=s}=count s"
proof (intro allI impI)
  fix s :: nat
  assume s: "s<6"
  have nth: "(map (\<lambda>k. card {t\<in>tokens. fst t=k}) [0..<6])!s =
    [8,3,8,9,5,5]!s"
    using Core_Token_Graph.series_card by simp
  show "card {t\<in>tokens. fst t=s}=count s"
    using nth s by (simp add: count_def)
qed

lemmas series_partition = Core_Token_Graph.series_partition
lemmas strict_approx_card = Core_Token_Graph.strict_approx_card
lemmas strict_approx_partition = Core_Token_Graph.strict_approx_partition
lemmas condition_classification_bijective = Core_Token_Graph.condition_classification_bijective
lemmas edge_count = Core_Token_Graph.edge_count
lemmas source_rank_bridge = Core_Token_Graph.source_rank_bridge
lemmas edge_lex_increasing = Core_Token_Graph.edge_lex_increasing

lemma rank_reachability_antisymm:
  assumes step: "\<And>a b. (a,b)\<in>E \<Longrightarrow> (r a,r b)\<in>P"
    and trans: "trans P" and irrefl: "irrefl P"
    and ab: "(a,b)\<in>E\<^sup>*" and ba: "(b,a)\<in>E\<^sup>*"
  shows "a=b"
proof -
  have ac: "acyclic E" by (rule general_rank_acyclic[
    where E=E and r=r and P=P, OF step trans irrefl])
  show ?thesis using acyclic_impl_antisym_rtrancl[OF ac] ab ba
    unfolding antisym_def by blast
qed

lemmas acyclic = Core_Token_Graph.concrete_acyclic
lemmas reachPartialOrder = Core_Token_Graph.concrete_partial_order

lemma designated_count:
  "card {(a,b)\<in>tokens\<times>tokens. designated a b}=111"
proof -
  have sig: "{(a,b)\<in>tokens\<times>tokens. designated a b} =
    Sigma tokens (\<lambda>a. {b\<in>tokens. designated a b})" by auto
  have dt: "distinct token_list" by (simp add: token_list_def)
  have len: "\<And>a. card {b\<in>tokens. designated a b} = length (filter (designated a) token_list)"
    unfolding tokens_def using distinct_filter[OF dt]
    by (simp only: set_filter[symmetric] distinct_card)
  have total: "sum_list (map (\<lambda>a. length (filter (designated a) token_list)) token_list)=111"
    by code_simp
  have "card {(a,b)\<in>tokens\<times>tokens. designated a b} =
    (\<Sum>a\<in>tokens. card {b\<in>tokens. designated a b})"
    by (subst sig) (simp add: finite_tokens)
  also have "... = (\<Sum>a\<in>tokens. length (filter (designated a) token_list))"
    by (simp only: len)
  also have "... = sum_list (map (\<lambda>a. length (filter (designated a) token_list)) token_list)"
    by (simp add: tokens_def sum_list_distinct_conv_sum_set[OF dt])
  also have "... = 111" by (rule total)
  finally show ?thesis .
qed

lemmas parallel_branches = Core_Token_Graph.parallel_branches
lemmas concrete_argument_unique = Core_Token_Graph.concrete_native_argument_unique

ML \<open>
val roots = @{thms token_card series_card series_partition strict_approx_card strict_approx_partition
  condition_classification_bijective edge_count source_rank_bridge edge_lex_increasing
  rank_reachability_antisymm acyclic reachPartialOrder designated_count parallel_branches
  concrete_argument_unique};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
