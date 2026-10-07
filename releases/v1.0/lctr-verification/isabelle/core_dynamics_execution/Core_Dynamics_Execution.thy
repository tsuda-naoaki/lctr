theory Core_Dynamics_Execution
 imports "LCTR_Core_Dynamics_Tokens.Core_Dynamics_Tokens"
 "LCTR_Core_Finite_Audit.Core_Finite_Audit"
begin
fun state_cast :: "internal_state\<Rightarrow>eval_state" where
 "state_cast SAT=Sat" | "state_cast Core_Finite_Audit.Failed=Core_Evaluation.Failed"
 | "state_cast NotFormed=Core_Evaluation.Unformed" | "state_cast NotEvaluable=Unevaluable"
lemma state_cast_sat: "state_cast x=Sat \<longleftrightarrow> x=SAT"
 by (cases x) simp_all
lemma carriers_same: "Core_Finite_Audit.tokens=Core_Token_Graph.tokens"
 by (simp add: Core_Finite_Audit.tokens_def token_carrier_exact
  Core_Finite_Audit.count_def Core_Token_Graph.count_def)
lemma edges_same:
 "Core_Finite_Audit.edge x y=Core_Token_Graph.edge x y"
 by (simp add: Core_Finite_Audit.edge_def Core_Token_Graph.edge_def
  Core_Finite_Audit.within_def Core_Token_Graph.within_def between_def)
lemma cast_state:
 "state_cast(state f e p c)=local_state f e p c"
 by (simp add: state_def local_state_def)
lemma cast_step:
 "state_cast(Core_Finite_Audit.step f e c st x)=
  eval_update Core_Token_Graph.edges f e c (state_cast \<circ> st)x"
 if xt: "x\<in>Core_Token_Graph.tokens"
proof -
 have pred: "(\<forall>y\<in>Core_Finite_Audit.tokens. Core_Finite_Audit.edge y x \<longrightarrow> st y=SAT)=
  (\<forall>y. (y,x)\<in>Core_Token_Graph.edges \<longrightarrow> state_cast(st y)=Sat)"
  using xt by (auto simp: Core_Token_Graph.edges_def carriers_same edges_same state_cast_sat; blast)
 show ?thesis
  by (simp only: Core_Finite_Audit.step_def cast_state predPass_def eval_update_def pred comp_apply)
qed
definition checked_run where
 "checked_run f e c t=(if t\<in>Core_Token_Graph.tokens then
  state_cast(Core_Finite_Audit.run f e c 40 t) else local_state(f t)(e t)True(c t))"
lemma checked_run_recurs:
 "checked_run f e c=eval_update Core_Token_Graph.edges f e c (checked_run f e c)"
proof -
 let ?s = "state_cast \<circ> Core_Finite_Audit.run f e c 40"
 have rec: "\<And>x. x\<in>Core_Token_Graph.tokens \<Longrightarrow>
  ?s x=eval_update Core_Token_Graph.edges f e c ?s x"
 proof -
  fix x assume x: "x\<in>Core_Token_Graph.tokens"
  have at: "Core_Finite_Audit.run f e c 40 x=
   Core_Finite_Audit.step f e c (Core_Finite_Audit.run f e c 40)x"
   using finite_run_solves[of f e c] x unfolding recurs_def carriers_same by blast
  show "?s x=eval_update Core_Token_Graph.edges f e c ?s x"
   using arg_cong[OF at, of state_cast] cast_step[OF x, of f e c "Core_Finite_Audit.run f e c 40"] by simp
 qed
 have extension: "(\<lambda>x. if x\<in>Core_Token_Graph.tokens then ?s x else local_state(f x)(e x)True(c x))=
  eval_update Core_Token_Graph.edges f e c
   (\<lambda>x. if x\<in>Core_Token_Graph.tokens then ?s x else local_state(f x)(e x)True(c x))"
  using conjunct1[OF carrier_recursion_extension[OF edges_typed rec]] .
 show ?thesis using extension unfolding checked_run_def comp_def .
qed
definition test_condition where "test_condition b t=(if fst t=2 then b(snd t-1) else True)"
definition test_state where "test_state b=checked_run(\<lambda>_. True)(\<lambda>_. True)(test_condition b)"
lemma test_recurs:
 "test_state b=eval_update Core_Token_Graph.edges (\<lambda>_. True)(\<lambda>_. True)(test_condition b)(test_state b)"
 unfolding test_state_def by (rule checked_run_recurs)
lemma test_condition_at: "test_condition b (dyn_token i)=b i"
 by (simp add: test_condition_def dyn_token_def)

lemma upstream_closed:
 "x\<in>Core_Token_Graph.tokens \<Longrightarrow> fst x<2 \<Longrightarrow>
  (y,x)\<in>Core_Token_Graph.edges \<Longrightarrow> y\<in>Core_Token_Graph.tokens \<and> fst y<2"
 by (auto simp: Core_Token_Graph.edges_def Core_Token_Graph.edge_def between_def)
lemma upstream_sat:
 assumes rec: "st=eval_update Core_Token_Graph.edges f e c st"
 and formed: "\<And>t. t\<in>Core_Token_Graph.tokens \<Longrightarrow> fst t<2 \<Longrightarrow> f t \<and> e t"
 and tests: "\<And>t. t\<in>Core_Token_Graph.tokens \<Longrightarrow> fst t<2 \<Longrightarrow> c t"
 shows "\<forall>t\<in>Core_Token_Graph.tokens. fst t<2 \<longrightarrow> st t=Sat"
proof -
 let ?J="{t\<in>Core_Token_Graph.tokens. fst t<2}"
 have inp: "\<And>x. x\<in>?J \<Longrightarrow> f x \<and> e x" using formed by simp
 have out: "\<And>x y. x\<in>?J \<Longrightarrow> (y,x)\<in>Core_Token_Graph.edges \<Longrightarrow> y\<notin>?J \<Longrightarrow> st y=Sat"
  using upstream_closed by blast
 have cond: "\<forall>x\<in>?J. c x" using tests by simp
 have sat: "\<forall>x\<in>?J. st x=Sat"
  by (rule iffD2[OF all_sat_iff_tests[where J="?J", OF concrete_wf rec inp out] cond])
 show ?thesis using sat by auto
qed
lemma upstream_passes:
 "t\<in>Core_Token_Graph.tokens \<Longrightarrow> fst t<2 \<Longrightarrow> test_state b t=Sat"
proof -
 have sat: "\<forall>t\<in>Core_Token_Graph.tokens. fst t<2 \<longrightarrow> test_state b t=Sat"
  by (rule upstream_sat[OF test_recurs]) (auto simp: test_condition_def)
 show "t\<in>Core_Token_Graph.tokens \<Longrightarrow> fst t<2 \<Longrightarrow> test_state b t=Sat" using sat by blast
qed
lemma test_input_sat: "dyn_input_sat(\<lambda>_. True)(\<lambda>_. True)(test_state b)"
 unfolding dyn_input_sat_def using upstream_passes[of _ b] by auto
lemma root_failure:
 assumes root: "i\<in>{0,1,3,4}"
 shows "test_state b(dyn_token i)=Core_Evaluation.Failed \<longleftrightarrow> \<not>b i"
proof -
 have i: "i<8" using root by auto
 have no_internal: "\<And>j. j<8 \<Longrightarrow> (dyn_token j,dyn_token i)\<notin>Core_Token_Graph.edges"
  using root within_edges_exact[OF _ i] by auto
 have ready: "dyn_ready(\<lambda>_. True)(\<lambda>_. True)(test_state b)i"
 proof (unfold dyn_ready_def, intro conjI allI impI)
  show True by simp
  show True by simp
  fix y assume yi: "(y,dyn_token i)\<in>Core_Token_Graph.edges"
  have yt: "y\<in>Core_Token_Graph.tokens" using yi unfolding Core_Token_Graph.edges_def by simp
  have rep: "fst y=1" using incoming_edges_exact[OF i yt] yi no_internal by blast
  show "test_state b y=Sat" by (rule upstream_passes[OF yt]) (simp add: rep)
 qed
 show ?thesis using recursive_failure[OF test_recurs[of b], where i=i] ready
  by (simp add: test_condition_at)
qed
lemma four_root_failures_and_descendants:
 "test_state(\<lambda>_. False)(dyn_token 0)=Core_Evaluation.Failed \<and>
  test_state(\<lambda>_. False)(dyn_token 1)=Core_Evaluation.Failed \<and>
  test_state(\<lambda>_. False)(dyn_token 3)=Core_Evaluation.Failed \<and>
  test_state(\<lambda>_. False)(dyn_token 4)=Core_Evaluation.Failed \<and>
  test_state(\<lambda>_. False)(dyn_token 2)=Core_Evaluation.Unformed \<and>
  test_state(\<lambda>_. False)(dyn_token 5)=Core_Evaluation.Unformed \<and>
  test_state(\<lambda>_. False)(dyn_token 6)=Core_Evaluation.Unformed \<and>
  test_state(\<lambda>_. False)(dyn_token 7)=Core_Evaluation.Unformed"
proof -
 have fail: "\<And>i. i\<in>{0,1,3,4} \<Longrightarrow>
  test_state(\<lambda>_. False)(dyn_token i)=Core_Evaluation.Failed"
  using root_failure[where b="\<lambda>_. False"] by simp
 have a: "test_state(\<lambda>_. False)(dyn_token 2)=Core_Evaluation.Unformed"
  by (rule direct_nonsat_unformed[OF test_recurs, where a="dyn_token 1"])
   (simp_all add: within_edges_exact fail)
 have b: "test_state(\<lambda>_. False)(dyn_token 5)=Core_Evaluation.Unformed"
  by (rule direct_nonsat_unformed[OF test_recurs, where a="dyn_token 0"])
   (simp_all add: within_edges_exact fail)
 have c: "test_state(\<lambda>_. False)(dyn_token 6)=Core_Evaluation.Unformed"
  by (rule direct_nonsat_unformed[OF test_recurs, where a="dyn_token 5"])
   (simp_all add: within_edges_exact b)
 have d: "test_state(\<lambda>_. False)(dyn_token 7)=Core_Evaluation.Unformed"
  by (rule direct_nonsat_unformed[OF test_recurs, where a="dyn_token 5"])
   (simp_all add: within_edges_exact b)
 show ?thesis using fail[of 0] fail[of 1] fail[of 3] fail[of 4] a b c d by simp
qed
definition late_profile where "late_profile i=(i\<noteq>6 \<and> i\<noteq>7)"
lemma late_rank_check:
 "list_all(\<lambda>i. list_all(\<lambda>j.
  Core_Token_Graph.scalar_rank(dyn_token j)<Core_Token_Graph.scalar_rank(dyn_token i)
  \<longrightarrow> late_profile j)[0..<8])[0..<8]"
 by code_simp
lemma final_pair_failure:
 "test_state late_profile(dyn_token 6)=Core_Evaluation.Failed \<and>
  test_state late_profile(dyn_token 7)=Core_Evaluation.Failed"
proof -
 have ready: "\<And>i. i<8 \<Longrightarrow> dyn_ready(\<lambda>_. True)(\<lambda>_. True)(test_state late_profile)i"
 proof -
  fix i :: nat assume i: "i<8"
  show "dyn_ready(\<lambda>_. True)(\<lambda>_. True)(test_state late_profile)i"
  proof (rule iffD2[OF ready_iff_ancestor_conditions[OF test_recurs test_input_sat i]], intro allI impI)
   fix j :: nat assume j: "j<8" and p: "(dyn_token j,dyn_token i)\<in>Core_Token_Graph.edges\<^sup>+"
   have lower: "Core_Token_Graph.scalar_rank(dyn_token j)<Core_Token_Graph.scalar_rank(dyn_token i)"
    by (rule path_rank[OF p])
   have "late_profile j" using late_rank_check i j lower by (auto simp: list_all_iff)
   then show "test_condition late_profile(dyn_token j)" by (simp add: test_condition_at)
  qed
 qed
 show ?thesis using recursive_failure[OF test_recurs[of late_profile], where i=6]
  recursive_failure[OF test_recurs[of late_profile], where i=7]
  ready[of 6] ready[of 7] by (simp add: test_condition_at late_profile_def)
qed
definition absent_formation where "absent_formation t=(t\<noteq>dyn_token 0)"
definition absent_state where "absent_state=checked_run absent_formation(\<lambda>_. True)absent_formation"
lemma absent_recurs:
 "absent_state=eval_update Core_Token_Graph.edges absent_formation(\<lambda>_. True)absent_formation absent_state"
 unfolding absent_state_def by (rule checked_run_recurs)
lemma absent_upstream_passes:
 "t\<in>Core_Token_Graph.tokens \<Longrightarrow> fst t<2 \<Longrightarrow> absent_state t=Sat"
proof -
 have formed: "\<And>t. fst t<2 \<Longrightarrow> absent_formation t"
  unfolding absent_formation_def dyn_token_def by auto
 have sat: "\<forall>t\<in>Core_Token_Graph.tokens. fst t<2 \<longrightarrow> absent_state t=Sat"
  by (rule upstream_sat[OF absent_recurs]) (auto intro: formed)
 show "t\<in>Core_Token_Graph.tokens \<Longrightarrow> fst t<2 \<Longrightarrow> absent_state t=Sat" using sat by blast
qed
lemma missing_formation_not_failure:
 "absent_state(dyn_token 0)=Core_Evaluation.Unformed \<and> absent_state(dyn_token 0)\<noteq>Core_Evaluation.Failed"
 using fun_cong[OF absent_recurs, of "dyn_token 0"]
 by (simp add: eval_update_def local_state_def absent_formation_def)
lemma missing_formation_blocks_descendant: "absent_state(dyn_token 5)=Core_Evaluation.Unformed"
 by (rule direct_nonsat_unformed[OF absent_recurs, where a="dyn_token 0"])
  (simp_all add: within_edges_exact missing_formation_not_failure)
ML \<open>
val roots = @{thms upstream_passes test_input_sat root_failure four_root_failures_and_descendants
 final_pair_failure absent_upstream_passes missing_formation_not_failure missing_formation_blocks_descendant};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
