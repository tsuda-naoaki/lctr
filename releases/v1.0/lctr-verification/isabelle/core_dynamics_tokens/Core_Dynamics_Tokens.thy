theory Core_Dynamics_Tokens
 imports "LCTR_Core_Continuum_Integration.Core_Continuum_Integration"
 "LCTR_Core_Evaluation_Alignment.Core_Evaluation_Alignment"
begin
definition dyn_token :: "nat\<Rightarrow>token" where "dyn_token i=(2,Suc i)"
definition dynamics_set where "dynamics_set={t\<in>tokens. fst t=2}"
definition failed_strict where "failed_strict st={t\<in>tokens. fst t\<noteq>3 \<and> st t=Failed}"
definition dyn_ready where
 "dyn_ready f e st i \<longleftrightarrow> f(dyn_token i) \<and> e(dyn_token i) \<and>
  (\<forall>y. (y,dyn_token i)\<in>edges \<longrightarrow> st y=Sat)"
definition dyn_input_sat where
 "dyn_input_sat f e st \<longleftrightarrow>
  (\<forall>i<8. f(dyn_token i) \<and> e(dyn_token i)) \<and>
  (\<forall>y\<in>tokens. fst y=1 \<longrightarrow> st y=Sat)"
definition minimal_false where
 "minimal_false c i \<longleftrightarrow> \<not>c(dyn_token i) \<and>
  (\<forall>j<8. \<not>c(dyn_token j) \<longrightarrow> (dyn_token j,dyn_token i)\<in>edges\<^sup>* \<longrightarrow> j=i)"
lemma dyn_typed: "i<8 \<Longrightarrow> dyn_token i\<in>tokens"
 by (simp add: dyn_token_def token_carrier_exact count_def)
lemma dyn_injective: "dyn_token i=dyn_token j \<longleftrightarrow> i=j"
 by (simp add: dyn_token_def)
lemma dyn_onto: "image dyn_token {..<8}=dynamics_set"
proof -
 have carrier: "dynamics_set={(2,i) |i. 1\<le>i \<and> i\<le>8}"
  by (auto simp: dynamics_set_def token_carrier_exact count_def)
 show ?thesis
 proof
  show "image dyn_token {..<8}\<subseteq>dynamics_set"
   unfolding carrier dyn_token_def by auto
  show "dynamics_set\<subseteq>image dyn_token {..<8}"
  proof
   fix t assume "t\<in>dynamics_set"
   then obtain k where tk: "t=(2,k)" and low: "1\<le>k" and high: "k\<le>8"
    unfolding carrier by blast
   have idx: "k-1<8" and recover: "Suc(k-1)=k" using low high by arith+
   have mem: "k-1\<in>{..<8}" using idx by simp
   have eq: "t=dyn_token(k-1)" using tk recover unfolding dyn_token_def by simp
   show "t\<in>image dyn_token {..<8}" using imageI[OF mem, of dyn_token] eq by simp
  qed
 qed
qed
lemma token_bijection: "bij_betw dyn_token {..<8} dynamics_set"
 using dyn_onto unfolding bij_betw_def inj_on_def by (simp add: dyn_token_def)
lemma dynamics_members: "t\<in>dynamics_set \<longleftrightarrow> (\<exists>i<8. t=dyn_token i)"
 by (subst dyn_onto[symmetric]) auto
lemma within_edges_exact:
 "i<8 \<Longrightarrow> j<8 \<Longrightarrow>
  ((dyn_token i,dyn_token j)\<in>edges \<longleftrightarrow>
   (i,j)\<in>{(0,5),(5,6),(1,2),(2,7),(5,7)})"
 by (auto simp: edges_def dyn_typed dyn_token_def edge_def within_def between_def token_carrier_exact count_def)
lemma incoming_edges_exact:
 assumes i: "i<8" and y: "y\<in>tokens"
 shows "(y,dyn_token i)\<in>edges \<longleftrightarrow>
  fst y=1 \<or> (\<exists>j<8. y=dyn_token j \<and> (dyn_token j,dyn_token i)\<in>edges)"
proof -
 have typed: "dyn_token i\<in>tokens" by (rule dyn_typed[OF i])
 have represent: "fst y=2 \<Longrightarrow> \<exists>j<8. y=dyn_token j"
  using y dynamics_members[of y] unfolding dynamics_set_def by blast
 show ?thesis using y typed represent
  unfolding edges_def edge_def between_def dyn_token_def by auto
qed
lemma recursive_failure:
 assumes rec: "st=eval_update edges f e c st"
 shows "st(dyn_token i)=Failed \<longleftrightarrow> dyn_ready f e st i \<and> \<not>c(dyn_token i)"
 using fun_cong[OF rec, of "dyn_token i"]
 by (simp add: eval_update_def state_failed_iff dyn_ready_def)
lemma condition_correspondence:
 "st=eval_update edges f e c st \<Longrightarrow> i<8 \<Longrightarrow>
  c(dyn_token i)=K i \<Longrightarrow>
  (dyn_token i\<in>failed_strict st \<longleftrightarrow> dyn_ready f e st i \<and> \<not>K i)"
 using recursive_failure[of st f e c i]
 by (simp add: failed_strict_def dyn_typed dyn_token_def token_carrier_exact count_def)
lemma sat_implies_condition:
 "st=eval_update E f e c st \<Longrightarrow> st t=Sat \<Longrightarrow> c t"
 using state_sat_iff unfolding eval_update_def by metis
lemma concrete_wf: "wf edges"
 by (rule finite_acyclic_wf[OF _ concrete_acyclic])
  (use finite_tokens edges_typed in \<open>meson finite_SigmaI finite_subset\<close>)

lemma ready_iff_ancestor_conditions:
 assumes rec: "st=eval_update edges f e c st" and inp: "dyn_input_sat f e st" and i: "i<8"
 shows "dyn_ready f e st i \<longleftrightarrow>
  (\<forall>j<8. (dyn_token j,dyn_token i)\<in>edges\<^sup>+ \<longrightarrow> c(dyn_token j))"
proof
 assume ready: "dyn_ready f e st i"
 show "\<forall>j<8. (dyn_token j,dyn_token i)\<in>edges\<^sup>+ \<longrightarrow> c(dyn_token j)"
 proof (intro allI impI)
  fix j assume j: "j<8" and path: "(dyn_token j,dyn_token i)\<in>edges\<^sup>+"
  obtain z where p: "(dyn_token j,z)\<in>edges\<^sup>*" and last: "(z,dyn_token i)\<in>edges"
   using tranclD2[OF path] by blast
  have sz: "st z=Sat" using ready last unfolding dyn_ready_def by blast
  have sj: "st(dyn_token j)=Sat"
  proof (rule ccontr)
   assume no: "st(dyn_token j)\<noteq>Sat"
   have bad: "dyn_token j=z \<or> st z=Unformed"
   proof (cases "dyn_token j=z")
    case True then show ?thesis by simp
   next
    case False
    have strict: "(dyn_token j,z)\<in>edges\<^sup>+" using p False by (simp add: rtrancl_eq_or_trancl)
    have "st z=Unformed" by (rule path_nonsat_unformed[OF rec strict no])
    then show ?thesis by simp
   qed
   show False using bad no sz by auto
  qed
  show "c(dyn_token j)" by (rule sat_implies_condition[OF rec sj])
 qed
next
 assume cond: "\<forall>j<8. (dyn_token j,dyn_token i)\<in>edges\<^sup>+ \<longrightarrow> c(dyn_token j)"
 let ?J = "{t\<in>dynamics_set. (t,dyn_token i)\<in>edges\<^sup>+}"
 have formed: "\<And>x. x\<in>?J \<Longrightarrow> f x \<and> e x"
  using inp unfolding dyn_input_sat_def dynamics_members by blast
 have outside: "\<And>x y. x\<in>?J \<Longrightarrow> (y,x)\<in>edges \<Longrightarrow> y\<notin>?J \<Longrightarrow> st y=Sat"
 proof -
  fix x y assume x: "x\<in>?J" and yx: "(y,x)\<in>edges" and ny: "y\<notin>?J"
  obtain k where k: "k<8" and xk: "x=dyn_token k" using x dynamics_members[of x] by blast
  have yt: "y\<in>tokens" using yx unfolding edges_def by simp
  have kinds: "fst y=1 \<or> (\<exists>j<8. y=dyn_token j \<and> (dyn_token j,dyn_token k)\<in>edges)"
   using incoming_edges_exact[OF k yt] yx xk by simp
  have path: "(y,dyn_token i)\<in>edges\<^sup>+"
   using yx x by (blast intro: trancl_trans r_into_trancl)
  have prior: "fst y=1" using kinds path ny dynamics_members[of y] by blast
  show "st y=Sat" using inp yt prior unfolding dyn_input_sat_def by blast
 qed
 have tests: "\<forall>x\<in>?J. c x" using cond unfolding dynamics_members by blast
 have allsat: "\<forall>x\<in>?J. st x=Sat"
  by (rule iffD2[OF all_sat_iff_tests[where J="?J", OF concrete_wf rec formed outside] tests])
 have pred: "\<forall>y. (y,dyn_token i)\<in>edges \<longrightarrow> st y=Sat"
 proof (intro allI impI)
  fix y assume yi: "(y,dyn_token i)\<in>edges"
  have yt: "y\<in>tokens" using yi unfolding edges_def by simp
  have kinds: "fst y=1 \<or> (\<exists>j<8. y=dyn_token j \<and> (dyn_token j,dyn_token i)\<in>edges)"
   using incoming_edges_exact[OF i yt] yi by simp
  show "st y=Sat" using kinds inp yt allsat dynamics_members[of y]
   unfolding dyn_input_sat_def by (blast intro: r_into_trancl)
 qed
 show "dyn_ready f e st i" using inp i pred unfolding dyn_input_sat_def dyn_ready_def by blast
qed

lemma minimal_false_iff:
 "minimal_false c i \<longleftrightarrow>
  (\<forall>j<8. (dyn_token j,dyn_token i)\<in>edges\<^sup>+ \<longrightarrow> c(dyn_token j)) \<and> \<not>c(dyn_token i)"
proof
 assume m: "minimal_false c i"
 have ancestors: "\<forall>j<8. (dyn_token j,dyn_token i)\<in>edges\<^sup>+ \<longrightarrow> c(dyn_token j)"
 proof (intro allI impI)
  fix j assume j: "j<8" and path: "(dyn_token j,dyn_token i)\<in>edges\<^sup>+"
  show "c(dyn_token j)"
  proof (rule ccontr)
   assume no: "\<not>c(dyn_token j)"
   have ji: "j=i" using m j no trancl_into_rtrancl[OF path] unfolding minimal_false_def by blast
   show False using path ji concrete_acyclic unfolding acyclic_def by blast
  qed
 qed
 show "(\<forall>j<8. (dyn_token j,dyn_token i)\<in>edges\<^sup>+ \<longrightarrow> c(dyn_token j)) \<and> \<not>c(dyn_token i)"
  using ancestors m unfolding minimal_false_def by blast
next
 assume h: "(\<forall>j<8. (dyn_token j,dyn_token i)\<in>edges\<^sup>+ \<longrightarrow> c(dyn_token j)) \<and> \<not>c(dyn_token i)"
 show "minimal_false c i"
  using h unfolding minimal_false_def by (auto simp: rtrancl_eq_or_trancl dyn_injective)
qed
lemma failure_iff_minimal:
 assumes rec: "st=eval_update edges f e c st" and inp: "dyn_input_sat f e st" and i: "i<8"
 shows "st(dyn_token i)=Failed \<longleftrightarrow> minimal_false c i"
 by (simp only: recursive_failure[OF rec] ready_iff_ancestor_conditions[OF rec inp i]
  minimal_false_iff)
lemma false_condition_has_failure:
 assumes rec: "st=eval_update edges f e c st" and inp: "dyn_input_sat f e st"
 and i: "i<8" and no: "\<not>c(dyn_token i)"
 shows "\<exists>j<8. st(dyn_token j)=Failed"
proof -
 have induction: "\<And>n i. scalar_rank(dyn_token i)=n \<Longrightarrow> i<8 \<Longrightarrow>
   \<not>c(dyn_token i) \<Longrightarrow> \<exists>j<8. st(dyn_token j)=Failed"
 proof -
  fix n
  show "\<And>i. scalar_rank(dyn_token i)=n \<Longrightarrow> i<8 \<Longrightarrow>
   \<not>c(dyn_token i) \<Longrightarrow> \<exists>j<8. st(dyn_token j)=Failed"
  proof (induction n rule: less_induct)
   case (less n)
   show ?case
   proof (cases "\<forall>j<8. (dyn_token j,dyn_token i)\<in>edges\<^sup>+ \<longrightarrow> c(dyn_token j)")
    case True
    have m: "minimal_false c i" using minimal_false_iff[of c i] True less.prems by blast
    have fail: "st(dyn_token i)=Failed" using failure_iff_minimal[OF rec inp less.prems(2)] m by blast
    show ?thesis using less.prems(2) fail by blast
   next
    case False
    then obtain j where j: "j<8" and path: "(dyn_token j,dyn_token i)\<in>edges\<^sup>+" and no: "\<not>c(dyn_token j)" by blast
    have lower: "scalar_rank(dyn_token j)<n" using path_rank[OF path] less.prems(1) by simp
    show ?thesis by (rule less.IH[OF lower refl j no])
   qed
  qed
 qed
 show ?thesis by (rule induction[OF refl i no])
qed
lemma stage_failure_iff:
 assumes rec: "st=eval_update edges f e c st" and inp: "dyn_input_sat f e st"
 shows "(\<exists>i<8. st(dyn_token i)=Failed) \<longleftrightarrow> \<not>(\<forall>i<8. c(dyn_token i))"
 using false_condition_has_failure[OF rec inp] recursive_failure[OF rec] by blast
lemma failed_intersection_image:
 "failed_strict st\<inter>dynamics_set=image dyn_token {i. i<8 \<and> st(dyn_token i)=Failed}"
 by (auto simp: dynamics_members failed_strict_def dyn_typed dyn_token_def token_carrier_exact count_def)
lemma stage_intersection_nonempty:
 "failed_strict st\<inter>dynamics_set\<noteq>{} \<longleftrightarrow> (\<exists>i<8. st(dyn_token i)=Failed)"
 by (simp add: failed_intersection_image)
lemma minimal_set_nonempty:
 assumes rec: "st=eval_update edges f e c st" and inp: "dyn_input_sat f e st"
 shows "(\<exists>i<8. minimal_false c i) \<longleftrightarrow> \<not>(\<forall>i<8. c(dyn_token i))"
 using stage_failure_iff[OF rec inp] failure_iff_minimal[OF rec inp] by blast
lemma unconditional_antichain:
 assumes rec: "st=eval_update edges f e c st" and hi: "st(dyn_token i)=Failed"
 and hj: "st(dyn_token j)=Failed" and p: "(dyn_token i,dyn_token j)\<in>edges\<^sup>*"
 shows "i=j"
 using failed_minimal[OF rec hi hj p] by (simp add: dyn_injective)
lemma simultaneous_minima:
 assumes rec: "st=eval_update edges f e c st" and inp: "dyn_input_sat f e st"
 and i: "i<8" and j: "j<8" and mi: "minimal_false c i" and mj: "minimal_false c j"
 shows "st(dyn_token i)=Failed \<and> st(dyn_token j)=Failed"
 using failure_iff_minimal[OF rec inp i] failure_iff_minimal[OF rec inp j] mi mj by blast
lemma upstream_failure_blocks_all:
 assumes rec: "st=eval_update edges f e c st" and r: "r\<in>tokens" and series: "fst r=1"
 and failed: "st r=Failed"
 shows "\<forall>i<8. st(dyn_token i)=Unformed"
proof (intro allI impI)
 fix i :: nat assume i: "i<8"
 have link: "(r,dyn_token i)\<in>edges" using incoming_edges_exact[OF i r] series by simp
 show "st(dyn_token i)=Unformed" by (rule direct_nonsat_unformed[OF rec link]) (simp add: failed)
qed
ML \<open>
val roots = @{thms token_bijection within_edges_exact incoming_edges_exact recursive_failure
 condition_correspondence sat_implies_condition ready_iff_ancestor_conditions minimal_false_iff
 failure_iff_minimal false_condition_has_failure stage_failure_iff failed_intersection_image
 stage_intersection_nonempty minimal_set_nonempty unconditional_antichain simultaneous_minima upstream_failure_blocks_all};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
