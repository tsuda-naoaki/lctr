theory Core_Representation_Failure
 imports LCTR_Core_Refinement_Forest.Core_Refinement_Forest
begin

definition repr_indices :: "nat set" where "repr_indices={1..3}"
definition repr_token :: "nat\<Rightarrow>token" where "repr_token i=(1,i)"
lemma repr_typed: "i\<in>repr_indices \<Longrightarrow> repr_token i\<in>tokens"
 by (simp add: repr_indices_def repr_token_def tokens_def count_def)
theorem representation_incoming_exact:
 assumes i: "i\<in>repr_indices" and t: "t\<in>tokens"
 shows "edge t (repr_token i) \<longleftrightarrow>
  (\<exists>j\<in>cmp_indices. t=cmp_token j) \<or>
  (\<exists>j\<in>repr_indices. t=repr_token j \<and> j+1=i)"
 using i t
 by (cases t; auto simp: repr_indices_def repr_token_def cmp_indices_def cmp_token_def
  edge_def within_def tokens_def count_def; arith)

definition repr_prefix where "repr_prefix c i \<longleftrightarrow> (\<forall>j\<in>repr_indices. j<i \<longrightarrow> c(repr_token j))"
definition repr_first where "repr_first c i \<longleftrightarrow> repr_prefix c i \<and> \<not>c(repr_token i)"
definition repr_generated where "repr_generated c n \<longleftrightarrow> (\<forall>j\<in>repr_indices. j\<le>n \<longrightarrow> c(repr_token j))"

theorem incoming_prefix:
 assumes ii: "i\<in>repr_indices"
 and external: "\<And>j. j\<in>cmp_indices \<Longrightarrow> s(cmp_token j)=SAT"
 and prior: "\<And>j. j\<in>repr_indices \<Longrightarrow> j<i \<Longrightarrow>
  ((s(repr_token j)=SAT) \<longleftrightarrow> (\<forall>k\<in>repr_indices. k\<le>j \<longrightarrow> c(repr_token k)))"
 shows "predPass s (repr_token i) \<longleftrightarrow> repr_prefix c i"
proof
 assume passed: "predPass s (repr_token i)"
 show "repr_prefix c i"
 proof (unfold repr_prefix_def, intro ballI impI)
  fix j assume ji: "j\<in>repr_indices" and lt: "j<i"
  have p: "i-1\<in>repr_indices" and pi: "i-1<i" and suc: "(i-1)+1=i"
   using ii ji lt by (auto simp: repr_indices_def)
  have ed: "edge(repr_token(i-1))(repr_token i)"
   using representation_incoming_exact[OF ii repr_typed[OF p]] p suc by blast
  have sat: "s(repr_token(i-1))=SAT" using passed repr_typed[OF p] ed
   unfolding predPass_def by blast
  have all: "\<forall>k\<in>repr_indices. k\<le>i-1 \<longrightarrow> c(repr_token k)"
   using prior[OF p pi] sat by simp
  show "c(repr_token j)" using all ji lt by auto
 qed
next
 assume pre: "repr_prefix c i"
 show "predPass s (repr_token i)"
 proof (unfold predPass_def, intro ballI impI)
  fix t assume tt: "t\<in>tokens" and ed: "edge t (repr_token i)"
  have cases: "(\<exists>j\<in>cmp_indices. t=cmp_token j) \<or>
   (\<exists>j\<in>repr_indices. t=repr_token j \<and> j+1=i)"
   using representation_incoming_exact[OF ii tt] ed by simp
  then show "s t=SAT"
  proof
   assume "\<exists>j\<in>cmp_indices. t=cmp_token j"
   then show ?thesis using external by blast
  next
   assume "\<exists>j\<in>repr_indices. t=repr_token j \<and> j+1=i"
   then obtain j where ji: "j\<in>repr_indices" and tj: "t=repr_token j" and suc: "j+1=i" by blast
   have lt: "j<i" using suc by arith
   have all: "\<forall>k\<in>repr_indices. k\<le>j \<longrightarrow> c(repr_token k)"
    using pre lt unfolding repr_prefix_def by auto
   show ?thesis using prior[OF ji lt] all tj by simp
  qed
 qed
qed

locale ready_representation =
 fixes f e c :: "token\<Rightarrow>bool" and s :: "token\<Rightarrow>internal_state"
 assumes rec: "recurs f e c s"
 and external: "\<And>j. j\<in>cmp_indices \<Longrightarrow> s(cmp_token j)=SAT"
 and ready: "\<And>i. i\<in>repr_indices \<Longrightarrow> f(repr_token i) \<and> e(repr_token i)"
begin
theorem representation_sat_prefix:
 "i\<in>repr_indices \<Longrightarrow>
  ((s(repr_token i)=SAT) \<longleftrightarrow> (\<forall>j\<in>repr_indices. j\<le>i \<longrightarrow> c(repr_token j)))"
proof (induction i rule: less_induct)
 case (less i)
 have ii: "i\<in>repr_indices" by fact
 have inc: "predPass s (repr_token i) \<longleftrightarrow> repr_prefix c i"
 proof (rule incoming_prefix[where s=s and c=c, OF ii external])
  fix j assume ji: "j\<in>repr_indices" and lt: "j<i"
  show "(s(repr_token j)=SAT) \<longleftrightarrow> (\<forall>k\<in>repr_indices. k\<le>j \<longrightarrow> c(repr_token k))"
   by (rule less.IH[OF lt ji])
 qed
 have at: "s(repr_token i)=state(f(repr_token i))(e(repr_token i))
   (predPass s (repr_token i))(c(repr_token i))"
  using rec repr_typed[OF ii] by (simp add: recurs_def step_def)
 have exact: "(s(repr_token i)=SAT) \<longleftrightarrow> repr_prefix c i \<and> c(repr_token i)"
  using at ready[OF ii] inc by (auto simp: state_def)
 show ?case using ii exact unfolding repr_prefix_def by (auto simp: le_eq_less_or_eq)
qed
theorem representation_failed_prefix:
 assumes ii: "i\<in>repr_indices"
 shows "(s(repr_token i)=Failed) \<longleftrightarrow> repr_first c i"
proof -
 have inc: "predPass s (repr_token i) \<longleftrightarrow> repr_prefix c i"
 proof (rule incoming_prefix[where s=s and c=c, OF ii external])
  fix j assume ji: "j\<in>repr_indices" and lt: "j<i"
  show "(s(repr_token j)=SAT) \<longleftrightarrow> (\<forall>k\<in>repr_indices. k\<le>j \<longrightarrow> c(repr_token k))"
   by (rule representation_sat_prefix[OF ji])
 qed
 have at: "s(repr_token i)=state(f(repr_token i))(e(repr_token i))
   (predPass s (repr_token i))(c(repr_token i))"
  using rec repr_typed[OF ii] by (simp add: recurs_def step_def)
 show ?thesis using at ready[OF ii] inc by (auto simp: state_def repr_first_def)
qed
end

theorem generation_boundary:
 assumes ii: "i\<in>repr_indices"
 shows "repr_first c i \<longleftrightarrow> repr_generated c (i-1) \<and> \<not>repr_generated c i"
proof -
 have pos: "0<i" using ii by (simp add: repr_indices_def)
 have before: "repr_generated c (i-1) \<longleftrightarrow> repr_prefix c i"
  unfolding repr_generated_def repr_prefix_def using pos by auto
 have upto: "repr_generated c i \<longleftrightarrow> repr_prefix c i \<and> c(repr_token i)"
  unfolding repr_generated_def repr_prefix_def using ii by (auto simp: le_eq_less_or_eq)
 show ?thesis using before upto unfolding repr_first_def by blast
qed
theorem repr_first_index_unique:
 "i\<in>repr_indices \<Longrightarrow> j\<in>repr_indices \<Longrightarrow>
  repr_first c i \<Longrightarrow> repr_first c j \<Longrightarrow> i=j"
 unfolding repr_first_def repr_prefix_def by (metis less_linear)
theorem repr_first_failure_partition:
 "(\<not>(\<forall>i\<in>repr_indices. c(repr_token i))) \<longleftrightarrow>
  (\<exists>!i. i\<in>repr_indices \<and> repr_first c i)"
proof
 assume fail: "\<not>(\<forall>i\<in>repr_indices. c(repr_token i))"
 let ?bad = "{i\<in>repr_indices. \<not>c(repr_token i)}"
 have fin: "finite ?bad" by (simp add: repr_indices_def)
 have ne: "?bad\<noteq>{}" using fail by blast
 have mem: "Min ?bad\<in>?bad" by (rule Min_in[OF fin ne])
 have low: "\<And>j. j\<in>?bad \<Longrightarrow> Min ?bad\<le>j" by (rule Min_le[OF fin])
 have pre: "repr_prefix c (Min ?bad)" using low unfolding repr_prefix_def by fastforce
 have first: "repr_first c (Min ?bad)" using mem pre by (simp add: repr_first_def)
 show "\<exists>!i. i\<in>repr_indices \<and> repr_first c i"
 proof (rule ex1I[where a="Min ?bad"])
  show "Min ?bad\<in>repr_indices \<and> repr_first c (Min ?bad)" using mem first by simp
  fix j assume j: "j\<in>repr_indices \<and> repr_first c j"
  show "j=Min ?bad" by (rule repr_first_index_unique) (use j mem first in auto)
 qed
next
 assume "\<exists>!i. i\<in>repr_indices \<and> repr_first c i"
 then show "\<not>(\<forall>i\<in>repr_indices. c(repr_token i))" unfolding repr_first_def by blast
qed

theorem comparison_success:
 assumes ready: "\<And>j. j\<in>cmp_indices \<Longrightarrow> f(cmp_token j) \<and> e(cmp_token j)"
 and pass: "\<And>j. j\<in>cmp_indices \<Longrightarrow> c(cmp_token j)"
 shows "\<forall>j\<in>cmp_indices. run f e c 40 (cmp_token j)=SAT"
proof -
 interpret C: native_comparison f e c by standard (fact ready)
 show ?thesis using C.R.comparison_sat_prefix pass by auto
qed

locale native_representation =
 fixes op :: "'a\<Rightarrow>bool" and f e c :: "'a\<Rightarrow>token\<Rightarrow>bool"
 assumes cmp_ready: "\<And>x j. op x \<Longrightarrow> j\<in>cmp_indices \<Longrightarrow> f x(cmp_token j) \<and> e x(cmp_token j)"
 and cmp_pass: "\<And>x j. op x \<Longrightarrow> j\<in>cmp_indices \<Longrightarrow> c x(cmp_token j)"
 and repr_ready: "\<And>x i. op x \<Longrightarrow> i\<in>repr_indices \<Longrightarrow> f x(repr_token i) \<and> e x(repr_token i)"
 and outside: "\<And>x i. \<not>op x \<Longrightarrow> i\<in>repr_indices \<Longrightarrow> \<not>f x(repr_token i)"
begin
abbreviation states where "states x\<equiv>run(f x)(e x)(c x)40"
definition region where "region i={x. op x \<and> states x(repr_token i)=Failed}"
definition failure_domain where "failure_domain={x. op x \<and> \<not>(\<forall>i\<in>repr_indices. c x(repr_token i))}"
theorem native_failed_prefix:
 assumes ox: "op x" and ii: "i\<in>repr_indices"
 shows "(states x(repr_token i)=Failed) \<longleftrightarrow> repr_first(c x)i"
proof -
 have cmp: "\<And>j. j\<in>cmp_indices \<Longrightarrow> states x(cmp_token j)=SAT"
  using comparison_success[where f="f x" and e="e x" and c="c x", OF cmp_ready[OF ox] cmp_pass[OF ox]] by blast
 interpret R: ready_representation "f x" "e x" "c x" "states x"
  by unfold_locales (fact finite_run_solves, fact cmp, fact repr_ready[OF ox])
 show ?thesis by (rule R.representation_failed_prefix[OF ii])
qed
theorem native_generation_boundary:
 "op x \<Longrightarrow> i\<in>repr_indices \<Longrightarrow>
  (x\<in>region i \<longleftrightarrow> repr_generated(c x)(i-1) \<and> \<not>repr_generated(c x)i)"
 by (simp add: region_def native_failed_prefix generation_boundary)
theorem native_localization:
 "x\<in>failure_domain \<longleftrightarrow> (\<exists>!i. i\<in>repr_indices \<and> x\<in>region i)"
proof (cases "op x")
 case False then show ?thesis by (auto simp: failure_domain_def region_def)
next
 case True
 have eq: "\<And>i. (i\<in>repr_indices \<and> x\<in>region i) \<longleftrightarrow>
  (i\<in>repr_indices \<and> repr_first(c x)i)"
  using True native_failed_prefix by (auto simp: region_def)
 show ?thesis by (simp only: eq repr_first_failure_partition[symmetric])
  (simp add: failure_domain_def True)
qed
theorem native_region_union:
 "failure_domain=(\<Union>i\<in>repr_indices. region i)"
 using native_localization native_failed_prefix by (auto simp: failure_domain_def region_def repr_first_def)
theorem native_regions_disjoint:
 "i\<in>repr_indices \<Longrightarrow> j\<in>repr_indices \<Longrightarrow> i\<noteq>j \<Longrightarrow> region i\<inter>region j={}"
 using native_failed_prefix repr_first_index_unique by (auto simp: region_def)
theorem outside_has_no_failed_representation:
 assumes ox: "\<not>op x" and ii: "i\<in>repr_indices"
 shows "states x(repr_token i)\<noteq>Failed"
proof -
 have at: "states x(repr_token i)=step(f x)(e x)(c x)(states x)(repr_token i)"
  using finite_run_solves repr_typed[OF ii] by (simp add: recurs_def)
 show ?thesis using at outside[OF ox ii] by (simp add: step_def state_def)
qed
theorem token_region_correspondence:
 "i\<in>repr_indices \<Longrightarrow> ((states x(repr_token i)=Failed) \<longleftrightarrow> x\<in>region i)"
 using outside_has_no_failed_representation by (auto simp: region_def)
theorem domain_separation:
 "{x. \<not>op x}\<inter>failure_domain={} \<and> failure_domain\<subseteq>{x. op x}"
 by (auto simp: failure_domain_def)
definition signature where "signature x i=(if x\<in>region i then 1 else 0::nat)"
definition basis where "basis i j=(if j=i then 1 else 0::nat)"
theorem signature_token_correspondence:
 "i\<in>repr_indices \<Longrightarrow> ((signature x i=1) \<longleftrightarrow> x\<in>region i) \<and>
  ((x\<in>region i) \<longleftrightarrow> states x(repr_token i)=Failed)"
 by (simp add: signature_def token_region_correspondence)
theorem signature_at_failure:
 assumes ii: "i\<in>repr_indices" and hi: "x\<in>region i"
 shows "\<forall>j\<in>repr_indices. signature x j=basis i j"
proof (intro ballI)
 fix j assume ji: "j\<in>repr_indices"
 have iff: "(x\<in>region j) \<longleftrightarrow> j=i"
  using native_regions_disjoint[OF ji ii] hi by blast
 show "signature x j=basis i j" by (simp add: signature_def basis_def iff)
qed
theorem signature_one_hot:
 assumes hf: "x\<in>failure_domain"
 shows "(\<exists>!i. i\<in>repr_indices \<and> (\<forall>j\<in>repr_indices. signature x j=basis i j)) \<and>
  sum(signature x)repr_indices=1"
proof -
 obtain i where ii: "i\<in>repr_indices" and hi: "x\<in>region i" using native_localization hf by blast
 have sig: "\<forall>j\<in>repr_indices. signature x j=basis i j" by (rule signature_at_failure[OF ii hi])
 have unique: "\<exists>!i. i\<in>repr_indices \<and> (\<forall>j\<in>repr_indices. signature x j=basis i j)"
 proof (rule ex1I[where a=i])
  show "i\<in>repr_indices \<and> (\<forall>j\<in>repr_indices. signature x j=basis i j)" using ii sig by simp
  fix k assume k: "k\<in>repr_indices \<and> (\<forall>j\<in>repr_indices. signature x j=basis k j)"
  have "basis k i=1" using k ii hi by (auto simp: signature_def)
  then show "k=i" by (auto simp: basis_def split: if_splits)
 qed
 have eq: "sum(signature x)repr_indices=sum(basis i)repr_indices" by (rule sum.cong) (use sig in auto)
 have sum: "sum(signature x)repr_indices=1" using eq ii by (simp add: basis_def repr_indices_def)
 show ?thesis using unique sum by blast
qed
theorem all_conditions_pass_no_failure:
 assumes hp: "\<And>i. i\<in>repr_indices \<Longrightarrow> c x(repr_token i)"
 shows "\<forall>i\<in>repr_indices. signature x i=0"
 using native_failed_prefix hp by (auto simp: signature_def region_def repr_first_def)
end

theorem comparison_failure_blocks_representation:
 assumes ji: "j\<in>cmp_indices" and ii: "i\<in>repr_indices"
 and hj: "run f e c 40(cmp_token j)=Failed"
 shows "run f e c 40(repr_token i)=NotFormed"
proof -
 have ed: "edge(cmp_token j)(repr_token i)"
  using representation_incoming_exact[OF ii cmp_typed[OF ji]] ji by blast
 have pred: "\<not>predPass(run f e c 40)(repr_token i)"
  using hj ed cmp_typed[OF ji] by (auto simp: predPass_def)
 have at: "run f e c 40(repr_token i)=step f e c (run f e c 40)(repr_token i)"
  using finite_run_solves repr_typed[OF ii] by (simp add: recurs_def)
 show ?thesis using at pred by (simp add: step_def state_def)
qed

locale representation_refinement = native_representation op f e c
 for op :: "'a\<Rightarrow>bool" and f e c +
 fixes J :: "nat\<Rightarrow>'j set" and K :: "nat\<Rightarrow>'j\<Rightarrow>'k set"
 and r1 :: "nat\<Rightarrow>'j\<Rightarrow>'a set" and r2 :: "nat\<Rightarrow>'j\<Rightarrow>'k\<Rightarrow>'a set"
 assumes first_sub: "\<And>i j. i\<in>repr_indices \<Longrightarrow> j\<in>J i \<Longrightarrow> r1 i j\<subseteq>region i"
 and second_sub: "\<And>i j k. i\<in>repr_indices \<Longrightarrow> j\<in>J i \<Longrightarrow> k\<in>K i j \<Longrightarrow> r2 i j k\<subseteq>r1 i j"
begin
sublocale T: two_level_regions repr_indices J K region r1 r2
 by unfold_locales (fact first_sub, fact second_sub)
theorem native_refinement_coverage:
 "(\<forall>n. node_region region r1 r2 n=T.F.covered n\<union>T.F.unrefined n \<and>
   T.F.covered n\<inter>T.F.unrefined n={}) \<and>
  (\<forall>n m. rtranclp T.F.child_edge n m \<longrightarrow> node_region region r1 r2 m\<subseteq>node_region region r1 r2 n)"
 using T.F.node_decomposition T.F.ancestor_inclusion by blast
theorem native_conditional_child_partition:
 assumes pairwise: "\<forall>i\<in>child_indices repr_indices J K n. \<forall>j\<in>child_indices repr_indices J K n.
  i\<noteq>j \<longrightarrow> node_region region r1 r2(child_node n i)\<inter>node_region region r1 r2(child_node n j)={}"
 shows "(\<forall>i\<in>child_indices repr_indices J K n. \<forall>j\<in>child_indices repr_indices J K n.
  i\<noteq>j \<longrightarrow> node_region region r1 r2(child_node n i)\<inter>node_region region r1 r2(child_node n j)={}) \<and>
  (\<forall>i\<in>child_indices repr_indices J K n. node_region region r1 r2(child_node n i)\<inter>T.F.unrefined n={})"
 by (rule T.F.child_family_with_remainder[OF pairwise])
end

context native_representation
begin
theorem native_refinement_monotonicity:
 fixes embed :: "'j\<Rightarrow>'k" and r :: "'j\<Rightarrow>'a set" and s :: "'k\<Rightarrow>'a set"
 assumes maps: "\<And>j. j\<in>I \<Longrightarrow> embed j\<in>J"
 and same: "\<And>j. j\<in>I \<Longrightarrow> r j=s(embed j)"
 shows "(\<Union>j\<in>I. r j)\<subseteq>(\<Union>k\<in>J. s k) \<and>
  region i-(\<Union>k\<in>J. s k)\<subseteq>region i-(\<Union>j\<in>I. r j)"
 by (rule snapshot_monotonicity[where embed=embed and r=r and s=s, OF maps same])
end

ML \<open>
val roots = @{thms representation_incoming_exact incoming_prefix
 ready_representation.representation_sat_prefix ready_representation.representation_failed_prefix
 generation_boundary repr_first_index_unique repr_first_failure_partition comparison_success
 native_representation.native_failed_prefix native_representation.native_generation_boundary
 native_representation.native_localization native_representation.native_region_union
 native_representation.native_regions_disjoint native_representation.outside_has_no_failed_representation
 native_representation.token_region_correspondence native_representation.domain_separation
 native_representation.signature_token_correspondence native_representation.signature_at_failure
 native_representation.signature_one_hot comparison_failure_blocks_representation
 native_representation.all_conditions_pass_no_failure representation_refinement.native_refinement_coverage
 native_representation.native_refinement_monotonicity representation_refinement.native_conditional_child_partition};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
