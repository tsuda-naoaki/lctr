theory Core_Differential_Execution
  imports LCTR_Core_Differential_Tokens.Core_Differential_Tokens
begin

declare diff_token.simps[simp del]

fun node_at :: "nat\<Rightarrow>node" where
  "node_at 0=N1" | "node_at (Suc 0)=N1" | "node_at (Suc (Suc 0))=N2"
| "node_at (Suc (Suc (Suc 0)))=N3" | "node_at (Suc (Suc (Suc (Suc 0))))=N4"
| "node_at (Suc (Suc (Suc (Suc (Suc n)))))=N5"
definition test_condition where "test_condition b t=(if fst t=5 then b (node_at (snd t)) else True)"
definition test_state where "test_state b=run (\<lambda>_. True) (\<lambda>_. True) (test_condition b) 40"
lemma token_condition: "test_condition b (diff_token i)=b i"
  by (cases i) (simp_all add: test_condition_def diff_token.simps numeral_eq_Suc)
lemma test_recursion: "recurs (\<lambda>_. True) (\<lambda>_. True) (test_condition b) (test_state b)"
  unfolding test_state_def by (rule finite_run_solves)

lemma outside_differential_passes:
  assumes typed: "t\<in>tokens" and outside: "fst t\<noteq>5"
  shows "test_state b t=SAT"
proof -
  have step: "\<And>n t. rank t=n \<Longrightarrow> t\<in>tokens \<Longrightarrow> fst t\<noteq>5 \<Longrightarrow> test_state b t=SAT"
  proof -
    fix n
    show "\<And>t. rank t=n \<Longrightarrow> t\<in>tokens \<Longrightarrow> fst t\<noteq>5 \<Longrightarrow> test_state b t=SAT"
    proof (induction n rule: less_induct)
      case (less n)
      fix t assume rt: "rank t=n" and tt: "t\<in>tokens" and out: "fst t\<noteq>5"
      have prior: "predPass (test_state b) t"
      proof (unfold predPass_def, intro ballI impI)
        fix y assume yy: "y\<in>tokens" and link: "Core_Finite_Audit.edge y t"
        have yout: "fst y\<noteq>5" using link out by (auto simp: Core_Finite_Audit.edge_def)
        have rn: "rank y<n" using edge_rank[OF tt yy link] rt by simp
        show "test_state b y=SAT" by (rule less.IH[OF rn refl yy yout])
      qed
      have eq: "test_state b t=state True True (predPass (test_state b) t) (test_condition b t)"
        using test_recursion[of b] tt by (simp add: recurs_def step_def)
      show "test_state b t=SAT" using eq prior out by (simp add: state_def test_condition_def)
    qed
  qed
  show ?thesis by (rule step[OF refl typed outside])
qed

lemma node_recursion:
  "test_state b (diff_token i)=state True True
    (\<forall>j. Core_Differential_Failure.edge j i \<longrightarrow> test_state b (diff_token j)=SAT) (b i)"
proof -
  have prior: "predPass (test_state b) (diff_token i)=
    (\<forall>j. Core_Differential_Failure.edge j i \<longrightarrow> test_state b (diff_token j)=SAT)"
  proof
    assume pre: "predPass (test_state b) (diff_token i)"
    show "\<forall>j. Core_Differential_Failure.edge j i \<longrightarrow> test_state b (diff_token j)=SAT"
    proof (intro allI impI)
      fix j assume ji: "Core_Differential_Failure.edge j i"
      have link: "Core_Finite_Audit.edge (diff_token j) (diff_token i)"
        using within_edges_exact[of j i] ji by blast
      show "test_state b (diff_token j)=SAT" using pre diff_typed[of j] link
        unfolding predPass_def by blast
    qed
  next
    assume pre: "\<forall>j. Core_Differential_Failure.edge j i \<longrightarrow> test_state b (diff_token j)=SAT"
    show "predPass (test_state b) (diff_token i)"
    proof (unfold predPass_def, intro ballI impI)
      fix y assume yy: "y\<in>tokens" and link: "Core_Finite_Audit.edge y (diff_token i)"
      have branches: "fst y=4 \<or> (\<exists>j. y=diff_token j \<and> Core_Differential_Failure.edge j i)"
        using incoming_edges_exact[OF yy, of i] link by blast
      show "test_state b y=SAT"
      proof (cases "fst y=4")
        case True
        show ?thesis by (rule outside_differential_passes[OF yy]) (simp add: True)
      next
        case False
        show ?thesis using branches False pre by blast
      qed
    qed
  qed
  show ?thesis using test_recursion[of b] diff_typed[of i]
    by (simp add: recurs_def step_def prior token_condition)
qed

lemma node_states:
  "test_state b (diff_token i)=
    (if (\<forall>j. ancestor j i \<longrightarrow> b j) then if b i then SAT else Failed else NotFormed)"
proof -
  have n1: "test_state b (diff_token N1)=(if b N1 then SAT else Failed)"
    by (simp only: node_recursion[of _ N1]) (simp add: state_def Core_Differential_Failure.edge_def)
  have n2: "test_state b (diff_token N2)=(if b N1 then if b N2 then SAT else Failed else NotFormed)"
    by (simp only: node_recursion[of _ N2]) (auto simp: Core_Differential_Failure.edge_def n1 state_def)
  show ?thesis
    by (cases i; subst node_recursion; auto simp: Core_Differential_Failure.edge_def ancestor_def n1 n2 state_def)
qed

lemma test_ready_and_satisfaction:
  assumes anc: "\<And>j. ancestor j i \<Longrightarrow> b j"
  shows "ready (\<lambda>_. True) (\<lambda>_. True) (test_state b) i \<and>
    ((test_state b (diff_token i)=SAT)=b i)"
proof -
  have pred: "\<And>j. Core_Differential_Failure.edge j i \<Longrightarrow> test_state b (diff_token j)=SAT"
    using anc edge_ancestor ancestor_transitive by (auto simp: node_states)
  have ready: "ready (\<lambda>_. True) (\<lambda>_. True) (test_state b) i"
    unfolding ready_def using incoming_edges_exact outside_differential_passes pred by auto
  show ?thesis using ready anc by (auto simp: node_states)
qed

lemma test_failure:
  "(\<And>j. ancestor j i \<Longrightarrow> b j) \<Longrightarrow>
    (test_state b (diff_token i)=Failed)=(\<not>b i)"
  by (simp add: node_states)

definition pair_profile where "pair_profile i=(i=N1 \<or> i=N2 \<or> i=N3)"
definition triple_profile where "triple_profile i=(i=N1)"
definition atlas_profile where "atlas_profile i=False"

lemma simultaneous_pair_execution:
  "test_state pair_profile (diff_token N4)=Failed \<and> test_state pair_profile (diff_token N5)=Failed \<and>
    test_state pair_profile (diff_token N1)=SAT \<and> test_state pair_profile (diff_token N3)=SAT"
  by (simp add: node_states pair_profile_def ancestor_def)
lemma simultaneous_three_with_blocked_descendant:
  "test_state triple_profile (diff_token N2)=Failed \<and> test_state triple_profile (diff_token N4)=Failed \<and>
    test_state triple_profile (diff_token N5)=Failed \<and> test_state triple_profile (diff_token N3)=NotFormed"
  by (simp add: node_states triple_profile_def ancestor_def)
lemma atlas_only_failure_execution:
  "test_state atlas_profile (diff_token N1)=Failed \<and>
    (\<forall>i. i\<noteq>N1 \<longrightarrow> test_state atlas_profile (diff_token i)=NotFormed)"
  by (simp add: node_states atlas_profile_def ancestor_def) (metis node.exhaust)

definition native_profile :: "(node\<Rightarrow>bool)\<Rightarrow>unit native" where
  "native_profile b=\<lparr>space=UNIV, atlas=(\<lambda>_. b N1), jet=(\<lambda>_. b N2),
    member=(\<lambda>_. b N3), valueCov=(\<lambda>_. b N4), timeCov=(\<lambda>_ _. b N5)\<rparr>"
fun native_truth where
  "native_truth b N1=b N1" | "native_truth b N2=b N2" | "native_truth b N3=(b N2 \<and> b N3)"
| "native_truth b N4=(b N1 \<and> b N4)" | "native_truth b N5=(b N1 \<and> b N5)"
lemma profile_truth_is_native: "native_truth b i=condition (native_profile b) i"
  by (cases i) (simp_all add: native_profile_def)
lemma control_profiles_have_native_inputs:
  "(\<forall>i. pair_profile i=condition (native_profile pair_profile) i) \<and>
    (\<forall>i. triple_profile i=condition (native_profile triple_profile) i) \<and>
    (\<forall>i. atlas_profile i=condition (native_profile atlas_profile) i)"
  by (simp only: profile_truth_is_native[symmetric])
    (intro conjI allI; case_tac i; simp add: pair_profile_def triple_profile_def atlas_profile_def)

ML \<open>
val roots = @{thms outside_differential_passes test_ready_and_satisfaction test_failure
  simultaneous_pair_execution simultaneous_three_with_blocked_descendant atlas_only_failure_execution
  profile_truth_is_native control_profiles_have_native_inputs};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
