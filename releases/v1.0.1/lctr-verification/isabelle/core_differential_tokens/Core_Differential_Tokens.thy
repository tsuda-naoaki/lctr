theory Core_Differential_Tokens
  imports LCTR_Core_Differential_Selected.Core_Differential_Selected
    LCTR_Core_Finite_Audit.Core_Finite_Audit
begin

fun diff_token :: "node\<Rightarrow>token" where
  "diff_token N1=(5,1)" | "diff_token N2=(5,2)" | "diff_token N3=(5,3)"
| "diff_token N4=(5,4)" | "diff_token N5=(5,5)"
definition differential_set where "differential_set={t\<in>tokens. fst t=5}"
definition failed_strict where "failed_strict st={t\<in>tokens. fst t\<noteq>3 \<and> st t=Failed}"
definition ready where
  "ready f e st i=(f (diff_token i) \<and> e (diff_token i) \<and>
    (\<forall>y\<in>tokens. Core_Finite_Audit.edge y (diff_token i) \<longrightarrow> st y=SAT))"

lemma diff_typed: "diff_token i\<in>tokens"
  by (cases i) (simp_all add: tokens_def count_def)
lemma all_nodes: "(UNIV::node set)={N1,N2,N3,N4,N5}"
  by (auto, case_tac x, auto)
lemma node_exists: "(\<exists>i::node. P i)=(P N1 \<or> P N2 \<or> P N3 \<or> P N4 \<or> P N5)"
  by (metis node.exhaust)
lemma token_bijection: "bij_betw diff_token UNIV differential_set"
proof -
  have carrier: "differential_set={(5,1),(5,2),(5,3),(5,4),(5,5)}"
    by (auto simp: differential_set_def tokens_def count_def; presburger)
  show ?thesis unfolding bij_betw_def inj_on_def
    by (simp add: all_nodes carrier)
qed

lemma within_edges_exact:
  "Core_Finite_Audit.edge (diff_token i) (diff_token j)=Core_Differential_Failure.edge i j"
  by (cases i; cases j) (simp_all add: Core_Finite_Audit.edge_def within_def Core_Differential_Failure.edge_def)

lemma incoming_edges_exact:
  assumes yt: "y\<in>tokens"
  shows "Core_Finite_Audit.edge y (diff_token i) =
    (fst y=4 \<or> (\<exists>j. y=diff_token j \<and> Core_Differential_Failure.edge j i))"
  using yt
  by (cases i; cases y; auto simp: Core_Finite_Audit.edge_def within_def Core_Differential_Failure.edge_def
    tokens_def count_def node_exists)

lemma recursive_failure:
  assumes rec: "recurs f e c st"
  shows "(st (diff_token i)=Failed)=(ready f e st i \<and> \<not>c (diff_token i))"
proof -
  have eq: "st (diff_token i)=state (f (diff_token i)) (e (diff_token i))
    (predPass st (diff_token i)) (c (diff_token i))"
    using rec diff_typed[of i] by (simp add: recurs_def step_def)
  show ?thesis by (simp only: eq) (auto simp: state_def ready_def predPass_def split: if_splits)
qed

lemma ready_failure:
  "recurs f e c st \<Longrightarrow> ready f e st i \<Longrightarrow> (st (diff_token i)=Failed)=(\<not>c (diff_token i))"
  using recursive_failure by blast

context matching_differential
begin
lemma minimal_token_correspondence:
  assumes rec: "recurs f e c st"
    and assignment: "c (diff_token i)=nativeCondition ev i"
    and ancestors: "bound.ancestorReady ev i" and rdy: "ready f e st i"
  shows "nativeMinimal ev i=(diff_token i\<in>failed_strict st)"
proof -
  have exact: "(st (diff_token i)=Failed)=(\<not>c (diff_token i))"
    by (rule ready_failure[OF rec rdy])
  have series: "fst (diff_token i)=5" by (cases i) simp_all
  show ?thesis using exact assignment ancestors diff_typed[of i] series
    by (simp add: minimal_exact bound.minimalFailure_def condition_exact failed_strict_def)
qed

lemma signature_token_correspondence:
  assumes rec: "recurs f e c st"
    and assignment: "\<And>i. c (diff_token i)=nativeCondition ev i"
    and ancestors: "\<And>i. bound.ancestorReady ev i"
    and rdy: "\<And>i. ready f e st i"
  shows "\<forall>i. bound.signature ev i=(diff_token i\<in>failed_strict st)"
  unfolding bound.signature_def
  by (simp only: minimal_exact[symmetric]) (intro allI, rule minimal_token_correspondence[OF rec assignment ancestors rdy])

lemma failure_set_token_image:
  assumes rec: "recurs f e c st"
    and assignment: "\<And>i. c (diff_token i)=nativeCondition ev i"
    and ancestors: "\<And>i. bound.ancestorReady ev i"
    and rdy: "\<And>i. ready f e st i"
  shows "diff_token ` {i. nativeMinimal ev i}=failed_strict st\<inter>differential_set"
proof -
  have eq: "\<And>i. nativeMinimal ev i=(diff_token i\<in>failed_strict st)"
    by (rule minimal_token_correspondence[OF rec assignment ancestors rdy])
  have onto: "diff_token ` UNIV=differential_set" using token_bijection by (simp add: bij_betw_def)
  show ?thesis
  proof (rule set_eqI)
    fix t
    show "(t\<in>diff_token ` {i. nativeMinimal ev i})=(t\<in>failed_strict st\<inter>differential_set)"
    proof
      assume "t\<in>diff_token ` {i. nativeMinimal ev i}"
      then obtain i where ti: "t=diff_token i" and ni: "nativeMinimal ev i" by auto
      have fail: "t\<in>failed_strict st" using eq[of i] ni ti by simp
      have diff: "t\<in>differential_set" using onto ti by blast
      show "t\<in>failed_strict st\<inter>differential_set" using fail diff by simp
    next
      assume both: "t\<in>failed_strict st\<inter>differential_set"
      then obtain i where ti: "t=diff_token i" using onto by blast
      have ni: "nativeMinimal ev i" using eq[of i] both ti by simp
      show "t\<in>diff_token ` {i. nativeMinimal ev i}" using ti ni by blast
    qed
  qed
qed

lemma relative_nonemptiness:
  "(\<exists>w::node\<Rightarrow>'e. \<forall>i. nativeMinimal (w i) i)=(\<forall>i. \<exists>ev. nativeMinimal ev i)"
  by (metis choice)
lemma relative_nonempty_witness_family:
  "(\<forall>i. \<exists>ev. nativeMinimal ev i)=(\<exists>w::node\<Rightarrow>'e. \<forall>i. nativeMinimal (w i) i)"
  by (simp only: relative_nonemptiness)
lemma finite_witness_set:
  assumes witness: "\<And>i. nativeMinimal (w i) i"
  shows "\<exists>A. finite A \<and> card A\<le>5 \<and> (\<forall>i. \<exists>ev\<in>A. nativeMinimal ev i)"
proof -
  have fin: "finite (UNIV::node set)" by (simp add: all_nodes)
  have bound: "card (w ` (UNIV::node set))\<le>5"
    using card_image_le[OF fin, of w] by (simp add: all_nodes)
  show ?thesis
    by (rule exI[of _ "w ` UNIV"]) (use fin bound witness in auto)
qed
end

lemma direct_nonsat:
  assumes rec: "recurs f e c st" and xt: "x\<in>tokens" and yt: "y\<in>tokens"
    and link: "Core_Finite_Audit.edge x y" and no: "st x\<noteq>SAT"
  shows "st y=NotFormed"
proof -
  have prior: "\<not>predPass st y" using xt link no by (auto simp: predPass_def)
  have eq: "st y=state (f y) (e y) (predPass st y) (c y)"
    using rec yt by (simp add: recurs_def step_def)
  show ?thesis using eq prior by (simp add: state_def)
qed

lemma law_failure_blocks_differential:
  assumes rec: "recurs f e c st" and typed: "t\<in>tokens" and series: "fst t=4"
    and failed: "st t=Failed"
  shows "\<forall>i. st (diff_token i)=NotFormed"
proof
  fix i
  have link: "Core_Finite_Audit.edge t (diff_token i)"
    using incoming_edges_exact[OF typed, of i] series by simp
  show "st (diff_token i)=NotFormed"
    by (rule direct_nonsat[OF rec typed diff_typed link]) (simp add: failed)
qed

lemma atlas_failure_blocks_descendants:
  assumes rec: "recurs f e c st" and failed: "st (diff_token N1)=Failed"
  shows "\<forall>i. i\<noteq>N1 \<longrightarrow> st (diff_token i)=NotFormed"
proof -
  have no: "st (diff_token N1)\<noteq>SAT" using failed by simp
  have direct: "\<And>i. Core_Differential_Failure.edge N1 i \<Longrightarrow> st (diff_token i)=NotFormed"
  proof -
    fix i assume hi: "Core_Differential_Failure.edge N1 i"
    have link: "Core_Finite_Audit.edge (diff_token N1) (diff_token i)"
      using within_edges_exact[of N1 i] hi by blast
    show "st (diff_token i)=NotFormed"
      by (rule direct_nonsat[OF rec diff_typed[of N1] diff_typed link no])
  qed
  have two: "st (diff_token N2)=NotFormed" by (rule direct) (simp add: Core_Differential_Failure.edge_def)
  have link23: "Core_Finite_Audit.edge (diff_token N2) (diff_token N3)"
    using within_edges_exact[of N2 N3] by (simp add: Core_Differential_Failure.edge_def)
  have no2: "st (diff_token N2)\<noteq>SAT" using two by simp
  have three: "st (diff_token N3)=NotFormed"
    by (rule direct_nonsat[OF rec diff_typed[of N2] diff_typed[of N3] link23 no2])
  have four: "st (diff_token N4)=NotFormed" by (rule direct) (simp add: Core_Differential_Failure.edge_def)
  have five: "st (diff_token N5)=NotFormed" by (rule direct) (simp add: Core_Differential_Failure.edge_def)
  show ?thesis using two three four five by (intro allI, case_tac i) auto
qed

ML \<open>
val roots = @{thms token_bijection within_edges_exact incoming_edges_exact recursive_failure ready_failure
  matching_differential.minimal_token_correspondence matching_differential.signature_token_correspondence
  matching_differential.failure_set_token_image law_failure_blocks_differential atlas_failure_blocks_descendants
  matching_differential.relative_nonemptiness matching_differential.relative_nonempty_witness_family
  matching_differential.finite_witness_set};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
