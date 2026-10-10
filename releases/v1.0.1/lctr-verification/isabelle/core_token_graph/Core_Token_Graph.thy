theory Core_Token_Graph
  imports LCTR_Core_Evaluation.Core_Evaluation
begin

type_synonym token = "nat \<times> nat"

definition token_list :: "token list" where
  "token_list = [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),
    (1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),
    (3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),
    (4,1),(4,2),(4,3),(4,4),(4,5),(5,1),(5,2),(5,3),(5,4),(5,5)]"
definition tokens :: "token set" where "tokens = set token_list"
definition count :: "nat \<Rightarrow> nat" where "count s = [8,3,8,9,5,5] ! s"

lemma token_carrier_exact: "tokens = {(s,i). s<6 \<and> 1\<le>i \<and> i\<le>count s}"
proof (rule equalityI)
  show "tokens \<subseteq> {(s,i). s<6 \<and> 1\<le>i \<and> i\<le>count s}"
    by (auto simp: tokens_def token_list_def count_def)
  show "{(s,i). s<6 \<and> 1\<le>i \<and> i\<le>count s} \<subseteq> tokens"
  proof
    fix t
    assume t: "t\<in>{(s,i). s<6 \<and> 1\<le>i \<and> i\<le>count s}"
    obtain s i where ti: "t=(s,i)" by (cases t) auto
    have h: "s<6" "1\<le>i" "i\<le>count s" using t ti by auto
    have cases: "s=0 \<or> s=1 \<or> s=2 \<or> s=3 \<or> s=4 \<or> s=5" using h(1) by presburger
    then show "t\<in>tokens" using h(2,3)
      unfolding ti tokens_def token_list_def count_def
      by (elim disjE; hypsubst; simp_all; presburger)
  qed
qed

lemma token_card: "card tokens = 38"
  by (simp add: tokens_def token_list_def)
lemma finite_tokens: "finite tokens" by (simp add: tokens_def)
lemma strict_approx_card:
  "card {t\<in>tokens. fst t \<noteq> 3} = 29 \<and> card {t\<in>tokens. fst t = 3} = 9"
  unfolding tokens_def by (simp only: set_filter[symmetric]) code_simp
lemma series_card:
  "map (\<lambda>s. card {t\<in>tokens. fst t = s}) [0..<6] = [8,3,8,9,5,5]"
  unfolding tokens_def by (simp only: set_filter[symmetric]) code_simp

lemma series_partition:
  "(\<forall>t\<in>tokens. \<exists>!s. s<6 \<and> fst t=s) \<and>
   (\<forall>s<6. \<exists>t\<in>tokens. fst t=s)"
proof -
  have nonempty: "list_all (\<lambda>s. list_ex (\<lambda>t. fst t=s) token_list) [0..<6]" by code_simp
  have typed: "\<forall>t\<in>tokens. fst t<6" by (auto simp: token_carrier_exact)
  show ?thesis using nonempty typed
    by (auto simp: tokens_def list_all_iff list_ex_iff)
qed

lemma strict_approx_partition:
  "tokens = {t\<in>tokens. fst t\<noteq>3} \<union> {t\<in>tokens. fst t=3} \<and>
   {t\<in>tokens. fst t\<noteq>3} \<inter> {t\<in>tokens. fst t=3} = {}" by auto

lemma condition_classification_bijective:
  "bij_betw (\<lambda>t. (t,K t)) tokens {(t,K t) |t. t\<in>tokens}"
  unfolding bij_betw_def inj_on_def by auto

definition within :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "within s i j = (if s=0 then 1\<le>i \<and> i<8 \<and> j=i+1
    else if s=1 then (i,j)\<in>{(1,2),(2,3)}
    else if s=2 then (i,j)\<in>{(1,6),(6,7),(2,3),(3,8),(6,8)}
    else if s=3 then (1\<le>i \<and> i\<le>6 \<and> j=7) \<or> (i,j)\<in>{(7,8),(7,9)}
    else if s=4 then (i,j)\<in>{(1,3),(1,5),(3,5)}
    else if s=5 then (i,j)\<in>{(1,2),(2,3),(1,4),(1,5)} else False)"
definition between :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "between s t = ((s,t)\<in>{(0,1),(1,2),(2,3),(2,4),(4,5)})"
definition edge :: "token \<Rightarrow> token \<Rightarrow> bool" where
  "edge a b = ((fst a=fst b \<and> within (fst a) (snd a) (snd b)) \<or> between (fst a) (fst b))"
definition edges :: "token rel" where
  "edges = {(a,b). a\<in>tokens \<and> b\<in>tokens \<and> edge a b}"
lemma edges_typed: "edges \<subseteq> tokens \<times> tokens" by (auto simp: edges_def)

definition edge_list where
  "edge_list = filter (\<lambda>(a,b). edge a b) (List.product token_list token_list)"
lemma edges_as_list: "edges = set edge_list"
  by (auto simp: edges_def edge_list_def tokens_def)
lemma distinct_edge_list: "distinct edge_list"
  unfolding edge_list_def by (intro distinct_filter distinct_product) (simp_all add: token_list_def)
lemma edge_count: "card edges = 214"
proof -
  have sig: "edges = Sigma tokens (\<lambda>a. {b\<in>tokens. edge a b})" by (auto simp: edges_def)
  have dt: "distinct token_list" by (simp add: token_list_def)
  have len: "\<And>a. card {b\<in>tokens. edge a b} = length (filter (edge a) token_list)"
    unfolding tokens_def using distinct_filter[OF dt]
    by (simp only: set_filter[symmetric] distinct_card)
  have total: "sum_list (map (\<lambda>a. length (filter (edge a) token_list)) token_list) = 214"
    by code_simp
  have c: "card edges = (\<Sum>a\<in>tokens. card {b\<in>tokens. edge a b})"
    by (simp add: sig finite_tokens)
  also have "... = (\<Sum>a\<in>tokens. length (filter (edge a) token_list))" by (simp only: len)
  also have "... = sum_list (map (\<lambda>a. length (filter (edge a) token_list)) token_list)"
    by (simp add: tokens_def sum_list_distinct_conv_sum_set[OF dt])
  also have "... = 214" by (rule total)
  finally show ?thesis .
qed

definition layer :: "nat \<Rightarrow> nat" where "layer s = [0,1,2,3,3,4] ! s"
definition intra_rank :: "token \<Rightarrow> nat" where
  "intra_rank t = ([[0,1,2,3,4,5,6,7],[0,1,2],[0,0,1,0,0,1,2,2],
    [0,0,0,0,0,0,1,2,2],[0,0,1,0,2],[0,1,2,1,1]] ! fst t) ! (snd t-1)"
definition rank :: "token \<Rightarrow> nat \<times> nat" where "rank t = (layer (fst t),intra_rank t)"
definition scalar_rank :: "token \<Rightarrow> nat" where "scalar_rank t = 8*fst(rank t)+snd(rank t)"
definition lex_less :: "(nat\<times>nat) \<Rightarrow> (nat\<times>nat) \<Rightarrow> bool" where
  "lex_less a b = (fst a<fst b \<or> (fst a=fst b \<and> snd a<snd b))"

lemma finite_rank_checks:
  "list_all (\<lambda>a. list_all (\<lambda>b.
      (lex_less (rank a) (rank b) = (scalar_rank a < scalar_rank b)) \<and>
      (edge a b \<longrightarrow> lex_less (rank a) (rank b))) token_list) token_list"
  by code_simp

lemma source_rank_bridge:
  "a\<in>tokens \<Longrightarrow> b\<in>tokens \<Longrightarrow> lex_less (rank a) (rank b) = (scalar_rank a<scalar_rank b)"
  using finite_rank_checks by (auto simp: tokens_def list_all_iff)
lemma edge_lex_increasing: "(a,b)\<in>edges \<Longrightarrow> lex_less (rank a) (rank b)"
  using finite_rank_checks by (auto simp: edges_def tokens_def list_all_iff)
lemma edge_rank_increasing: "(a,b)\<in>edges \<Longrightarrow> scalar_rank a<scalar_rank b"
  using source_rank_bridge edge_lex_increasing by (auto simp: edges_def)

lemma general_path_increases:
  assumes step: "\<And>a b. (a,b)\<in>E \<Longrightarrow> (r a,r b)\<in>P" and tr: "trans P"
    and path: "(a,b)\<in>E\<^sup>+"
  shows "(r a,r b)\<in>P"
  using path
proof (induction rule: trancl_induct)
  case (base y)
  then show ?case by (rule step)
next
  case (step y z)
  then show ?case using assms(1) tr unfolding trans_def by blast
qed

lemma general_rank_acyclic:
  assumes step: "\<And>a b. (a,b)\<in>E \<Longrightarrow> (r a,r b)\<in>P"
    and "trans P" "irrefl P"
  shows "acyclic E"
proof (unfold acyclic_def, intro allI notI)
  fix x
  assume p: "(x,x)\<in>E\<^sup>+"
  have "(r x,r x)\<in>P"
    by (rule general_path_increases[where E=E and P=P and r=r, OF step assms(2) p])
  then show False using assms(3) unfolding irrefl_def by blast
qed

lemma concrete_acyclic: "acyclic edges"
  by (rule general_rank_acyclic[where r=scalar_rank and P="{(a,b). a<b}"])
     (auto simp: trans_def irrefl_def intro: edge_rank_increasing less_trans)

definition reach :: "token rel" where "reach = edges\<^sup>* \<inter> (tokens \<times> tokens)"
lemma concrete_partial_order:
  "refl_on tokens reach \<and> trans reach \<and> antisym reach"
  using acyclic_impl_antisym_rtrancl[OF concrete_acyclic]
  unfolding reach_def refl_on_def trans_def antisym_def by (blast intro: rtrancl_trans)

definition allowed :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "allowed s t = (s=0 \<or> (s=1 \<and> t\<noteq>0) \<or> (s=2 \<and> t\<in>{2,3,4,5}) \<or>
    (s=3 \<and> t=3) \<or> (s=4 \<and> t\<in>{4,5}) \<or> (s=5 \<and> t=5))"
lemma allowed_trans: "allowed a b \<Longrightarrow> allowed b c \<Longrightarrow> allowed a c"
  by (auto simp: allowed_def)
lemma finite_allowed_check:
  "list_all (\<lambda>a. list_all (\<lambda>b. edge a b \<longrightarrow> allowed (fst a) (fst b)) token_list) token_list"
  by code_simp
lemma edge_allowed: "(a,b)\<in>edges \<Longrightarrow> allowed (fst a) (fst b)"
  using finite_allowed_check by (auto simp: edges_def tokens_def list_all_iff)
lemma path_allowed: "(a,b)\<in>edges\<^sup>+ \<Longrightarrow> allowed (fst a) (fst b)"
  by (erule trancl_induct) (auto intro: edge_allowed allowed_trans)
lemma path_rank: "(a,b)\<in>edges\<^sup>+ \<Longrightarrow> scalar_rank a<scalar_rank b"
  by (erule trancl_induct) (auto intro: edge_rank_increasing less_trans)

definition designated :: "token \<Rightarrow> token \<Rightarrow> bool" where
  "designated a b = ((fst a=3 \<and> fst b\<in>{4,5}) \<or>
    (fst a=2 \<and> fst b=2 \<and> snd a=4 \<and> snd b=5) \<or>
    (fst a=3 \<and> fst b=3 \<and> ((snd a<snd b \<and> snd b\<le>6) \<or> (snd a=8 \<and> snd b=9))) \<or>
    (fst a=4 \<and> fst b=4 \<and> snd a<snd b \<and> snd a\<in>{1,2,4} \<and> snd b\<in>{1,2,4}) \<or>
    (fst a=5 \<and> fst b=5 \<and> snd a=4 \<and> snd b=5))"

lemma finite_designated_check:
  "list_all (\<lambda>a. list_all (\<lambda>b. designated a b \<longrightarrow>
    a\<noteq>b \<and> (scalar_rank a=scalar_rank b \<or> (\<not>allowed (fst a) (fst b) \<and> \<not>allowed (fst b) (fst a))))
      token_list) token_list"
  by code_simp

lemma parallel_branches:
  assumes "a\<in>tokens" "b\<in>tokens" "designated a b"
  shows "(a,b)\<notin>reach \<and> (b,a)\<notin>reach"
proof -
  have crit: "a\<noteq>b \<and> (scalar_rank a=scalar_rank b \<or>
    (\<not>allowed (fst a) (fst b) \<and> \<not>allowed (fst b) (fst a)))"
    using finite_designated_check assms by (auto simp: tokens_def list_all_iff)
  have no_paths: "(a,b)\<notin>edges\<^sup>+ \<and> (b,a)\<notin>edges\<^sup>+"
  proof
    show "(a,b)\<notin>edges\<^sup>+"
    proof
      assume p: "(a,b)\<in>edges\<^sup>+"
      have "scalar_rank a<scalar_rank b" by (rule path_rank[OF p])
      moreover have "allowed (fst a) (fst b)" by (rule path_allowed[OF p])
      ultimately show False using crit by auto
    qed
    show "(b,a)\<notin>edges\<^sup>+"
    proof
      assume p: "(b,a)\<in>edges\<^sup>+"
      have "scalar_rank b<scalar_rank a" by (rule path_rank[OF p])
      moreover have "allowed (fst b) (fst a)" by (rule path_allowed[OF p])
      ultimately show False using crit by auto
    qed
  qed
  show ?thesis using no_paths crit by (auto simp: reach_def rtrancl_eq_or_trancl)
qed

lemma concrete_argument_unique:
  "\<exists>!s. s = eval_update (argument_edges edges Spec res) f e c s"
  by (rule typed_argument_unique[OF finite_tokens edges_typed concrete_acyclic])

lemma concrete_native_argument_unique:
  "\<exists>!s. s = native_eval_update (Sigma tokens Spec) (argument_edges edges Spec res) f e c s"
proof -
  have fin: "finite edges" using finite_tokens edges_typed finite_subset by blast
  have wf: "wf edges" by (rule finite_acyclic_wf[OF fin concrete_acyclic])
  show ?thesis by (rule native_argument_unique[OF wf])
qed

ML \<open>
val roots = @{thms token_carrier_exact token_card strict_approx_card series_card series_partition strict_approx_partition
  condition_classification_bijective edge_count source_rank_bridge edge_lex_increasing general_rank_acyclic
  concrete_acyclic concrete_partial_order parallel_branches concrete_argument_unique concrete_native_argument_unique};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
