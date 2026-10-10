theory Core_Continuum_Failure
 imports "LCTR_Core_Continuum_Encoding.Core_Continuum_Encoding"
 "LCTR_Core_Dynamics_Execution.Core_Dynamics_Execution"
begin

definition approx_token :: "nat\<Rightarrow>token" where "approx_token i=(3,Suc i)"
definition approx_pred where
 "approx_pred s i=(\<forall>y. (y,approx_token i)\<in>Core_Token_Graph.edges \<longrightarrow> s y=Sat)"
definition approx_ready where
 "approx_ready f e s i=(f(approx_token i) \<and> e(approx_token i) \<and> approx_pred s i)"
definition fa where "fa s i=(s(approx_token i)=Core_Evaluation.Failed)"
definition approx_failed where
 "approx_failed s={t\<in>Core_Token_Graph.tokens. fst t=3 \<and> s t=Core_Evaluation.Failed}"
lemma approx_token_typed: "i<9 \<Longrightarrow> approx_token i\<in>Core_Token_Graph.tokens"
 by (simp add: approx_token_def token_carrier_exact Core_Token_Graph.count_def)
lemma approx_token_member: "i<9 \<Longrightarrow> approx_token i\<in>approx_set"
 using approx_token_typed[of i] by (simp add: approx_set_def approx_token_def)
lemma approx_image: "approx_set=approx_token ` {..<9}"
proof (rule equalityI)
 show "approx_set\<subseteq>approx_token ` {..<9}"
 proof
  fix t assume "t\<in>approx_set"
  then obtain i :: nat where t: "t=(3,i)" and lo: "1\<le>i" and hi: "i\<le>9"
   unfolding approx_set_exact by blast
  have a: "i-1<9" using lo hi by arith
  have b: "approx_token(i-1)=t" using lo unfolding t approx_token_def by simp
  have mem: "approx_token(i-1)\<in>approx_token ` {..<9}" by (rule imageI) (use a in simp)
  show "t\<in>approx_token ` {..<9}" using mem b by simp
 qed
 show "approx_token ` {..<9}\<subseteq>approx_set"
  using approx_token_member by auto
qed

lemma incoming_exact:
 assumes i: "i<9" and y: "y\<in>Core_Token_Graph.tokens"
 shows "(y,approx_token i)\<in>Core_Token_Graph.edges \<longleftrightarrow>
 fst y=2 \<or> (fst y=3 \<and> ((snd y\<le>6 \<and> i=6) \<or>
 (snd y=7 \<and> (i=7 \<or> i=8))))"
 using i y
 by (auto simp: Core_Token_Graph.edges_def Core_Token_Graph.edge_def
  Core_Token_Graph.within_def between_def approx_token_def token_carrier_exact
  Core_Token_Graph.count_def)
lemma first_incoming_exact:
 assumes i: "i<6" and y: "y\<in>Core_Token_Graph.tokens"
 shows "(y,approx_token i)\<in>Core_Token_Graph.edges \<longleftrightarrow> fst y=2"
 using incoming_exact[OF _ y, where i=i] i by auto
lemma seventh_incoming_exact:
 assumes y: "y\<in>Core_Token_Graph.tokens"
 shows "(y,approx_token 6)\<in>Core_Token_Graph.edges \<longleftrightarrow>
 fst y=2 \<or> (\<exists>i<6. y=approx_token i)"
 using incoming_exact[OF _ y, where i=6] y
 by (auto simp: approx_token_def token_carrier_exact Core_Token_Graph.count_def; presburger)
lemma final_incoming_exact:
 assumes i: "i<9" "7\<le>i" and y: "y\<in>Core_Token_Graph.tokens"
 shows "(y,approx_token i)\<in>Core_Token_Graph.edges \<longleftrightarrow> fst y=2 \<or> y=approx_token 6"
 using incoming_exact[OF i(1) y] i by (cases y) (auto simp: approx_token_def; presburger)

lemma first_incomparable:
 assumes i: "i<6" and j: "j<6" and ne: "i\<noteq>j"
 shows "(approx_token i,approx_token j)\<notin>Core_Token_Graph.edges\<^sup>* \<and>
 (approx_token j,approx_token i)\<notin>Core_Token_Graph.edges\<^sup>*"
proof -
 have it: "approx_token i\<in>Core_Token_Graph.tokens" by (rule approx_token_typed) (use i in auto)
 have jt: "approx_token j\<in>Core_Token_Graph.tokens" by (rule approx_token_typed) (use j in auto)
 have p: "(approx_token i,approx_token j)\<notin>Core_Token_Graph.reach \<and>
  (approx_token j,approx_token i)\<notin>Core_Token_Graph.reach"
 proof (cases "i<j")
  case True
  show ?thesis by (rule parallel_branches[OF it jt]) (use True j in \<open>simp add: designated_def approx_token_def\<close>)
 next
  case False
  have ji: "j<i" using False ne by auto
  have p: "(approx_token j,approx_token i)\<notin>Core_Token_Graph.reach \<and>
   (approx_token i,approx_token j)\<notin>Core_Token_Graph.reach"
   by (rule parallel_branches[OF jt it]) (use ji i in \<open>simp add: designated_def approx_token_def\<close>)
  show ?thesis using p by blast
 qed
 show ?thesis using p it jt by (simp add: Core_Token_Graph.reach_def)
qed
lemma final_incomparable:
 "(approx_token 7,approx_token 8)\<notin>Core_Token_Graph.edges\<^sup>* \<and>
  (approx_token 8,approx_token 7)\<notin>Core_Token_Graph.edges\<^sup>*"
proof -
 have a: "approx_token 7\<in>Core_Token_Graph.tokens" by (rule approx_token_typed) simp
 have b: "approx_token 8\<in>Core_Token_Graph.tokens" by (rule approx_token_typed) simp
 have p: "(approx_token 7,approx_token 8)\<notin>Core_Token_Graph.reach \<and>
  (approx_token 8,approx_token 7)\<notin>Core_Token_Graph.reach"
  by (rule parallel_branches[OF a b]) (simp add: designated_def approx_token_def)
 show ?thesis using p a b by (simp add: Core_Token_Graph.reach_def)
qed

lemma recursive_failure:
 assumes rec: "s=eval_update Core_Token_Graph.edges f e c s"
 shows "fa s i \<longleftrightarrow> approx_ready f e s i \<and> \<not>c(approx_token i)"
 using fun_cong[OF rec, of "approx_token i"]
 by (simp add: fa_def approx_ready_def approx_pred_def eval_update_def state_failed_iff)
lemma ready_failure_iff:
 "s=eval_update Core_Token_Graph.edges f e c s \<Longrightarrow> approx_ready f e s i \<Longrightarrow>
 fa s i \<longleftrightarrow> \<not>c(approx_token i)"
 using recursive_failure by blast
lemma ready_sat_iff:
 assumes rec: "s=eval_update Core_Token_Graph.edges f e c s"
 and r: "approx_ready f e s i"
 shows "s(approx_token i)=Sat \<longleftrightarrow> c(approx_token i)"
 using fun_cong[OF rec, of "approx_token i"] r
 by (auto simp: approx_ready_def approx_pred_def eval_update_def state_sat_iff)
lemma first_ready:
 assumes inp: "input_sat f e s" and i: "i<6"
 shows "approx_ready f e s i"
proof -
 have ti: "approx_token i\<in>approx_set" by (rule approx_token_member) (use i in auto)
 have pred: "approx_pred s i"
 proof (unfold approx_pred_def, intro allI impI)
  fix y assume ed: "(y,approx_token i)\<in>Core_Token_Graph.edges"
  have yt: "y\<in>Core_Token_Graph.tokens" using ed edges_typed by blast
  have dy: "fst y=2" using first_incoming_exact[OF i yt] ed by blast
  show "s y=Sat" using inp yt dy unfolding input_sat_def by blast
 qed
 show ?thesis using inp ti pred unfolding approx_ready_def input_sat_def by blast
qed
lemma seventh_pred:
 assumes dyn: "\<And>t. t\<in>Core_Token_Graph.tokens \<Longrightarrow> fst t=2 \<Longrightarrow> s t=Sat"
 shows "approx_pred s 6 \<longleftrightarrow> (\<forall>i<6. s(approx_token i)=Sat)"
proof
 assume h: "approx_pred s 6"
 show "\<forall>i<6. s(approx_token i)=Sat"
 proof (intro allI impI)
  fix i :: nat assume i: "i<6"
  have it: "approx_token i\<in>Core_Token_Graph.tokens" by (rule approx_token_typed) (use i in auto)
  have ed: "(approx_token i,approx_token 6)\<in>Core_Token_Graph.edges"
   using seventh_incoming_exact[OF it] i by blast
  show "s(approx_token i)=Sat" using h ed unfolding approx_pred_def by blast
 qed
next
 assume h: "\<forall>i<6. s(approx_token i)=Sat"
 show "approx_pred s 6"
 proof (unfold approx_pred_def, intro allI impI)
  fix y assume ed: "(y,approx_token 6)\<in>Core_Token_Graph.edges"
  have yt: "y\<in>Core_Token_Graph.tokens" using ed edges_typed by blast
  show "s y=Sat" using seventh_incoming_exact[OF yt] ed dyn[OF yt] h by blast
 qed
qed
lemma final_pred:
 assumes dyn: "\<And>t. t\<in>Core_Token_Graph.tokens \<Longrightarrow> fst t=2 \<Longrightarrow> s t=Sat"
 and i: "i<9" "7\<le>i"
 shows "approx_pred s i \<longleftrightarrow> s(approx_token 6)=Sat"
proof -
 have t: "approx_token 6\<in>Core_Token_Graph.tokens" by (rule approx_token_typed) simp
 have ed: "(approx_token 6,approx_token i)\<in>Core_Token_Graph.edges"
  using final_incoming_exact[OF i t] by simp
 show ?thesis
 proof
  assume "approx_pred s i"
  then show "s(approx_token 6)=Sat" using ed unfolding approx_pred_def by blast
 next
  assume h: "s(approx_token 6)=Sat"
  show "approx_pred s i"
  proof (unfold approx_pred_def, intro allI impI)
   fix y assume ed: "(y,approx_token i)\<in>Core_Token_Graph.edges"
   have yt: "y\<in>Core_Token_Graph.tokens" using ed edges_typed by blast
   show "s y=Sat" using final_incoming_exact[OF i yt] ed dyn[OF yt] h by blast
  qed
 qed
qed
lemma ninth_not_dependent_on_eighth:
 "(approx_token 7,approx_token 8)\<notin>Core_Token_Graph.edges"
 by (simp add: Core_Token_Graph.edges_def Core_Token_Graph.edge_def
  Core_Token_Graph.within_def between_def approx_token_def)

lemma quantitative_failure:
 fixes d eps :: "token\<Rightarrow>ereal"
 assumes rec: "s=eval_update Core_Token_Graph.edges f e c s"
 and i: "i<9" and r: "approx_ready f e s i"
 and dn: "0\<le>d(approx_token i)" and en: "0\<le>eps(approx_token i)"
 and encoding: "c(approx_token i)=(d(approx_token i)\<le>eps(approx_token i))"
 shows "(fa s i \<longleftrightarrow> eps(approx_token i)<d(approx_token i)) \<and>
 (fa s i \<longleftrightarrow> approx_token i\<in>exceeded approx_set d eps)"
 using ready_failure_iff[OF rec r] encoding excess_positive[OF en dn] approx_token_member[OF i]
 by (auto simp: exceeded_def)
lemma source_nine_witnesses:
 fixes d eps :: "token\<Rightarrow>ereal"
 assumes rec: "s=eval_update Core_Token_Graph.edges f e c s"
 and i: "i<9" and r: "approx_ready f e s i"
 and dn: "snd(approx_token i)\<le>6 \<Longrightarrow> 0\<le>d(approx_token i)"
 and en: "snd(approx_token i)\<le>6 \<Longrightarrow> 0\<le>eps(approx_token i)"
 and matching: "c(approx_token i)=paper_condition d eps b (approx_token i)"
 shows "(fa s i \<longleftrightarrow> paper_tolerance eps (approx_token i)<paper_defect d b (approx_token i)) \<and>
 (fa s i \<longleftrightarrow> approx_token i\<in>exceeded approx_set (paper_defect d b) (paper_tolerance eps))"
proof -
 have d: "0\<le>paper_defect d b (approx_token i)" by (simp add: paper_defect_def bool_defect_def dn)
 have e: "0\<le>paper_tolerance eps (approx_token i)" by (simp add: paper_tolerance_def half_def en)
 have enc: "c(approx_token i)=(paper_defect d b (approx_token i)\<le>paper_tolerance eps (approx_token i))"
  using matching nine_component_encoding by simp
 show ?thesis by (rule quantitative_failure[where d="paper_defect d b" and eps="paper_tolerance eps",
  OF rec i r d e enc])
qed
lemma source_first_witness:
 fixes d eps :: "token\<Rightarrow>ereal"
 assumes rec: "s=eval_update Core_Token_Graph.edges f e c s"
 and i: "i<6" and r: "approx_ready f e s i"
 and dn: "0\<le>d(approx_token i)" and en: "0\<le>eps(approx_token i)"
 and matching: "c(approx_token i)=paper_condition d eps b (approx_token i)"
 shows "fa s i \<longleftrightarrow> eps(approx_token i)<d(approx_token i)"
 using ready_failure_iff[OF rec r] matching i
 by (simp add: paper_condition_def approx_token_def not_le)

lemma failed_set_exact: "approx_failed s=approx_token ` {i. i<9 \<and> fa s i}"
proof -
 have set: "approx_failed s={t\<in>approx_set. s t=Core_Evaluation.Failed}"
  by (auto simp: approx_failed_def approx_set_def)
 show ?thesis unfolding set approx_image fa_def by auto
qed
lemma failure_disjunction: "approx_failed s\<noteq>{} \<longleftrightarrow> (\<exists>i<9. fa s i)"
 by (auto simp: failed_set_exact)

definition first_failures where "first_failures s=approx_token ` {i. i<6 \<and> fa s i}"
lemma first_failures_finite: "finite(first_failures s)"
 unfolding first_failures_def by simp
lemma first_failures_card:
 assumes i: "i<6" and j: "j<6" and ne: "i\<noteq>j" and hi: "fa s i" and hj: "fa s j"
 shows "2\<le>card(first_failures s)"
proof -
 have sub: "{approx_token i,approx_token j}\<subseteq>first_failures s"
  using i j hi hj unfolding first_failures_def by blast
 have neq: "approx_token i\<noteq>approx_token j" using ne by (simp add: approx_token_def)
 have "card {approx_token i,approx_token j}\<le>card(first_failures s)"
  by (rule card_mono[OF first_failures_finite sub])
 then show ?thesis by (simp add: neq)
qed
lemma quantitative_first_pair:
 fixes d eps :: "token\<Rightarrow>ereal"
 assumes rec: "s=eval_update Core_Token_Graph.edges f e c s"
 and i: "i<6" and j: "j<6" and ne: "i\<noteq>j"
 and ri: "approx_ready f e s i" and rj: "approx_ready f e s j"
 and dn: "\<And>k. k<6 \<Longrightarrow> 0\<le>d(approx_token k)"
 and en: "\<And>k. k<6 \<Longrightarrow> 0\<le>eps(approx_token k)"
 and matching: "\<And>k. k<9 \<Longrightarrow> c(approx_token k)=paper_condition d eps b (approx_token k)"
 and hi: "eps(approx_token i)<d(approx_token i)" and hj: "eps(approx_token j)<d(approx_token j)"
 shows "2\<le>card(first_failures s)"
proof -
 have fi: "fa s i" using source_first_witness[OF rec i ri dn[OF i] en[OF i] matching[of i]] i hi by auto
 have fj: "fa s j" using source_first_witness[OF rec j rj dn[OF j] en[OF j] matching[of j]] j hj by auto
 show ?thesis by (rule first_failures_card[OF i j ne fi fj])
qed
lemma final_pair:
 "fa s 7 \<Longrightarrow> fa s 8 \<Longrightarrow> approx_token 7\<in>approx_failed s \<and> approx_token 8\<in>approx_failed s"
 unfolding failed_set_exact by auto
lemma all_failures_minimal:
 assumes rec: "s=eval_update Core_Token_Graph.edges f e c s"
 and x: "x\<in>approx_failed s"
 shows "\<forall>y\<in>approx_failed s. (y,x)\<in>Core_Token_Graph.edges\<^sup>* \<longrightarrow> y=x"
 using Core_Evaluation.failed_minimal[OF rec] x unfolding approx_failed_def by blast
lemma first_failure_blocks_extension:
 assumes rec: "s=eval_update Core_Token_Graph.edges f e c s"
 and i: "i<6" and h: "fa s i"
 shows "s(approx_token 6)=Core_Evaluation.Unformed"
proof -
 have it: "approx_token i\<in>Core_Token_Graph.tokens" by (rule approx_token_typed) (use i in auto)
 have ed: "(approx_token i,approx_token 6)\<in>Core_Token_Graph.edges"
  using seventh_incoming_exact[OF it] i by blast
 have ns: "s(approx_token i)\<noteq>Sat" using h by (simp add: fa_def)
 show ?thesis by (rule direct_nonsat_unformed[OF rec ed ns])
qed
lemma extension_failure_blocks_final:
 assumes rec: "s=eval_update Core_Token_Graph.edges f e c s" and h: "fa s 6"
 shows "s(approx_token 7)=Core_Evaluation.Unformed \<and> s(approx_token 8)=Core_Evaluation.Unformed"
proof -
 have it: "approx_token 6\<in>Core_Token_Graph.tokens" by (rule approx_token_typed) simp
 have a: "(approx_token 6,approx_token 7)\<in>Core_Token_Graph.edges"
  using final_incoming_exact[OF _ _ it, where i=7] by simp
 have b: "(approx_token 6,approx_token 8)\<in>Core_Token_Graph.edges"
  using final_incoming_exact[OF _ _ it, where i=8] by simp
 have ns: "s(approx_token 6)\<noteq>Sat" using h by (simp add: fa_def)
 show ?thesis using direct_nonsat_unformed[OF rec a ns] direct_nonsat_unformed[OF rec b ns] by blast
qed

definition approx_test_condition where
 "approx_test_condition b t=(if fst t=3 then b(snd t-1) else True)"
definition approx_test_state where
 "approx_test_state b=checked_run(\<lambda>_. True)(\<lambda>_. True)(approx_test_condition b)"
lemma approx_test_recurs:
 "approx_test_state b=eval_update Core_Token_Graph.edges (\<lambda>_. True)(\<lambda>_. True)
 (approx_test_condition b)(approx_test_state b)"
 unfolding approx_test_state_def by (rule checked_run_recurs)
lemma approx_test_condition_at: "approx_test_condition b (approx_token i)=b i"
 by (simp add: approx_test_condition_def approx_token_def)
lemma nonapprox_closed:
 "x\<in>Core_Token_Graph.tokens \<Longrightarrow> fst x\<noteq>3 \<Longrightarrow>
 (y,x)\<in>Core_Token_Graph.edges \<Longrightarrow> y\<in>Core_Token_Graph.tokens \<and> fst y\<noteq>3"
 by (auto simp: Core_Token_Graph.edges_def Core_Token_Graph.edge_def between_def)
lemma test_input_sat:
 "input_sat(\<lambda>_. True)(\<lambda>_. True)(approx_test_state b)"
proof -
 let ?J="{t\<in>Core_Token_Graph.tokens. fst t\<noteq>3}"
 have inp: "\<And>x. x\<in>?J \<Longrightarrow> True \<and> True" by simp
 have out: "\<And>x y. x\<in>?J \<Longrightarrow> (y,x)\<in>Core_Token_Graph.edges \<Longrightarrow> y\<notin>?J
  \<Longrightarrow> approx_test_state b y=Sat" using nonapprox_closed by blast
 have cond: "\<forall>x\<in>?J. approx_test_condition b x" by (simp add: approx_test_condition_def)
 have sat: "\<forall>x\<in>?J. approx_test_state b x=Sat"
  by (rule iffD2[OF all_sat_iff_tests[where J="?J", OF concrete_wf approx_test_recurs inp out] cond])
 show ?thesis using sat by (auto simp: input_sat_def)
qed
lemma test_first_sat:
 assumes i: "i<6"
 shows "approx_test_state b (approx_token i)=Sat \<longleftrightarrow> b i"
proof -
 have r: "approx_ready(\<lambda>_. True)(\<lambda>_. True)(approx_test_state b)i"
  by (rule first_ready[OF test_input_sat i])
 show ?thesis using ready_sat_iff[OF approx_test_recurs r] by (simp add: approx_test_condition_at)
qed
lemma test_first_failure:
 assumes i: "i<6"
 shows "fa (approx_test_state b) i \<longleftrightarrow> \<not>b i"
proof -
 have r: "approx_ready(\<lambda>_. True)(\<lambda>_. True)(approx_test_state b)i"
  by (rule first_ready[OF test_input_sat i])
 show ?thesis using ready_failure_iff[OF approx_test_recurs r] by (simp add: approx_test_condition_at)
qed
lemma test_extension_sat:
 assumes h: "\<forall>i<6. b i"
 shows "approx_test_state b (approx_token 6)=Sat \<longleftrightarrow> b 6"
proof -
 have dyn: "\<And>t. t\<in>Core_Token_Graph.tokens \<Longrightarrow> fst t=2 \<Longrightarrow> approx_test_state b t=Sat"
  using test_input_sat[of b] unfolding input_sat_def by blast
 have pred: "approx_pred(approx_test_state b)6"
  using seventh_pred[where s="approx_test_state b", OF dyn] test_first_sat[where b=b] h by blast
 have r: "approx_ready(\<lambda>_. True)(\<lambda>_. True)(approx_test_state b)6"
  using pred by (simp add: approx_ready_def)
 show ?thesis using ready_sat_iff[OF approx_test_recurs r] by (simp add: approx_test_condition_at)
qed
lemma test_final_failure:
 assumes h: "\<forall>j<6. b j" and h7: "b 6" and i: "i<9" "7\<le>i"
 shows "fa(approx_test_state b)i \<longleftrightarrow> \<not>b i"
proof -
 have dyn: "\<And>t. t\<in>Core_Token_Graph.tokens \<Longrightarrow> fst t=2 \<Longrightarrow> approx_test_state b t=Sat"
  using test_input_sat[of b] unfolding input_sat_def by blast
 have pred: "approx_pred(approx_test_state b)i"
  using final_pred[where s="approx_test_state b" and i=i, OF dyn i] test_extension_sat[OF h] h7 by blast
 have r: "approx_ready(\<lambda>_. True)(\<lambda>_. True)(approx_test_state b)i"
  using pred by (simp add: approx_ready_def)
 show ?thesis using ready_failure_iff[OF approx_test_recurs r] by (simp add: approx_test_condition_at)
qed
definition first_pair_test where "first_pair_test i=(i\<noteq>0 \<and> i\<noteq>1)"
definition final_pair_test where "final_pair_test (i::nat)=(i<7)"
lemma first_pair_execution:
 "fa(approx_test_state first_pair_test)0 \<and> fa(approx_test_state first_pair_test)1 \<and>
 2\<le>card(first_failures(approx_test_state first_pair_test)) \<and>
 approx_test_state first_pair_test (approx_token 6)=Core_Evaluation.Unformed"
proof -
 have a: "fa(approx_test_state first_pair_test)0" using test_first_failure[of 0 first_pair_test]
  by (simp add: first_pair_test_def)
 have b: "fa(approx_test_state first_pair_test)1" using test_first_failure[of 1 first_pair_test]
  by (simp add: first_pair_test_def)
 have c: "2\<le>card(first_failures(approx_test_state first_pair_test))"
  by (rule first_failures_card[OF _ _ _ a b]) simp_all
 have d: "approx_test_state first_pair_test(approx_token 6)=Core_Evaluation.Unformed"
  by (rule first_failure_blocks_extension[OF approx_test_recurs _ a]) simp
 show ?thesis using a b c d by blast
qed
lemma final_pair_execution:
 "fa(approx_test_state final_pair_test)7 \<and> fa(approx_test_state final_pair_test)8 \<and>
 approx_test_state final_pair_test(approx_token 6)=Sat"
proof -
 have h: "\<forall>i<6. final_pair_test i" by (simp add: final_pair_test_def)
 have h7: "final_pair_test 6" by (simp add: final_pair_test_def)
 have a: "fa(approx_test_state final_pair_test)7"
  using test_final_failure[where b=final_pair_test and i=7, OF h h7]
  by (simp only: numeral_less_iff numeral_le_iff; simp add: final_pair_test_def)
 have b: "fa(approx_test_state final_pair_test)8"
  using test_final_failure[where b=final_pair_test and i=8, OF h h7]
  by (simp only: numeral_less_iff numeral_le_iff; simp add: final_pair_test_def)
 have c: "approx_test_state final_pair_test(approx_token 6)=Sat"
  using test_extension_sat[OF h] h7 by blast
 show ?thesis using a b c by blast
qed

ML \<open>
val roots = @{thms incoming_exact first_incoming_exact seventh_incoming_exact final_incoming_exact
 first_incomparable final_incomparable recursive_failure ready_failure_iff ready_sat_iff
 first_ready seventh_pred final_pred ninth_not_dependent_on_eighth quantitative_failure
 source_nine_witnesses source_first_witness failed_set_exact failure_disjunction first_failures_card
 quantitative_first_pair final_pair all_failures_minimal first_failure_blocks_extension
 extension_failure_blocks_final test_input_sat test_first_sat test_first_failure test_extension_sat
 test_final_failure first_pair_execution final_pair_execution};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
