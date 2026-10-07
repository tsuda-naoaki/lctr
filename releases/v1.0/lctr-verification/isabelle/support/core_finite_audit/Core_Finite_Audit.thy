theory Core_Finite_Audit
  imports Main
begin

type_synonym token = "nat \<times> nat"
datatype internal_state = SAT | Failed | NotFormed | NotEvaluable
datatype audit_status = Pass | Indeterminate | Unformed | Blocked | Fail
definition state where
  "state f e p q = (if \<not>(f \<and> p) then NotFormed else if \<not>e then NotEvaluable else if q then SAT else Failed)"
fun lift where
  "lift False s = Blocked"
| "lift True SAT = Pass"
| "lift True Failed = Fail"
| "lift True NotFormed = Unformed"
| "lift True NotEvaluable = Indeterminate"
definition count :: "nat \<Rightarrow> nat" where "count s = [8,3,8,9,5,5]!s"
definition tokens :: "token set" where
  "tokens = {(s,i). s<6 \<and> 1\<le>i \<and> i\<le>count s}"
definition token_list :: "token list" where
  "token_list = concat (map (\<lambda>s. map (\<lambda>i. (s,i+1)) [0..<count s]) [0..<6])"
lemma token_list_exact: "set token_list = tokens"
proof (rule set_eqI)
  fix t :: token
  obtain s i :: nat where t: "t=(s,i)" by (cases t) auto
  have index: "(\<exists>j<count s. i=j+1) \<longleftrightarrow> 1\<le>i \<and> i\<le>count s" by presburger
  have mem: "(s,i)\<in>set token_list \<longleftrightarrow> s<6 \<and> (\<exists>j<count s. i=j+1)"
    by (auto simp: token_list_def image_iff)
  have "t\<in>set token_list \<longleftrightarrow> s<6 \<and> (\<exists>j<count s. i=j+1)" by (simp only: t mem)
  also have "... \<longleftrightarrow> s<6 \<and> 1\<le>i \<and> i\<le>count s" using index by blast
  also have "... \<longleftrightarrow> t\<in>tokens" by (simp add: t tokens_def)
  finally show "t\<in>set token_list \<longleftrightarrow> t\<in>tokens" .
qed
definition within :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "within s i j = (if s=0 then 1\<le>i \<and> i<8 \<and> j=i+1
    else if s=1 then (i,j)\<in>{(1,2),(2,3)}
    else if s=2 then (i,j)\<in>{(1,6),(6,7),(2,3),(3,8),(6,8)}
    else if s=3 then (1\<le>i \<and> i\<le>6 \<and> j=7) \<or> (i,j)\<in>{(7,8),(7,9)}
    else if s=4 then (i,j)\<in>{(1,3),(1,5),(3,5)}
    else if s=5 then (i,j)\<in>{(1,2),(2,3),(1,4),(1,5)} else False)"
definition edge :: "token \<Rightarrow> token \<Rightarrow> bool" where
  "edge a b = ((fst a=fst b \<and> within (fst a) (snd a) (snd b)) \<or>
    (fst a,fst b)\<in>{(0,1),(1,2),(2,3),(2,4),(4,5)})"
definition rank :: "token \<Rightarrow> nat" where
  "rank t = 8 * ([0,1,2,3,3,4]!fst t) +
    (([[0,1,2,3,4,5,6,7],[0,1,2],[0,0,1,0,0,1,2,2],
      [0,0,0,0,0,0,1,2,2],[0,0,1,0,2],[0,1,2,1,1]]!fst t)!(snd t-1))"
lemma finite_rank_checks:
  "list_all (\<lambda>x. rank x<40 \<and> list_all (\<lambda>y. edge y x \<longrightarrow> rank y<rank x) token_list) token_list"
  by code_simp
lemma rank_bound: "x\<in>tokens \<Longrightarrow> rank x<40"
  using finite_rank_checks by (auto simp: list_all_iff token_list_exact)
lemma edge_rank: "x\<in>tokens \<Longrightarrow> y\<in>tokens \<Longrightarrow> edge y x \<Longrightarrow> rank y<rank x"
  using finite_rank_checks by (auto simp: list_all_iff token_list_exact)
lemma count_bound: "s<6 \<Longrightarrow> count s\<le>9"
proof -
  assume h: "s<6"
  have "s=0 \<or> s=1 \<or> s=2 \<or> s=3 \<or> s=4 \<or> s=5" using h by presburger
  then show ?thesis by (auto simp: count_def)
qed

definition tabulate :: "(token \<Rightarrow> internal_state) \<Rightarrow> internal_state list list" where
  "tabulate st = map (\<lambda>s. map (\<lambda>i. if i<count s then st (s,i+1) else NotFormed) [0..<9]) [0..<6]"
definition lookup where "lookup table t = (table!fst t)!(snd t-1)"
lemma lookup_tabulate: "t\<in>tokens \<Longrightarrow> lookup (tabulate st) t=st t"
proof -
  assume t: "t\<in>tokens"
  have a: "fst t<6" "1\<le>snd t" "snd t\<le>count (fst t)" using t by (auto simp: tokens_def)
  have i: "snd t-1<9" using count_bound[OF a(1)] a by arith
  have j: "snd t-1<count (fst t)" using a by arith
  show ?thesis using a i j by (simp add: lookup_def tabulate_def)
qed
definition predPass where "predPass st x = (\<forall>y\<in>tokens. edge y x \<longrightarrow> st y=SAT)"
definition step where "step f e q st x = state (f x) (e x) (predPass st x) (q x)"
fun runTable where
  "runTable f e q 0 = tabulate (\<lambda>_. NotFormed)"
| "runTable f e q (Suc n) = tabulate (step f e q (lookup (runTable f e q n)))"
definition run where "run f e q n = lookup (runTable f e q n)"
definition recurs where "recurs f e q st = (\<forall>x\<in>tokens. st x = step f e q st x)"
lemma run_zero: "x\<in>tokens \<Longrightarrow> run f e q 0 x=NotFormed"
  by (simp add: run_def lookup_tabulate)
lemma run_suc: "x\<in>tokens \<Longrightarrow> run f e q (Suc n) x=step f e q (run f e q n) x"
  by (simp add: run_def lookup_tabulate)
lemma predecessor_iff:
  "predPass st x \<longleftrightarrow> (\<forall>y\<in>{y\<in>tokens. edge y x}. st y=SAT)"
  by (auto simp: predPass_def)
lemma step_eq_native:
  "step f e q st x = state (f x) (e x) (\<forall>y\<in>{y\<in>tokens. edge y x}. st y=SAT) (q x)"
  by (simp only: step_def predecessor_iff)
lemma step_cong:
  "(\<And>y. y\<in>tokens \<Longrightarrow> edge y x \<Longrightarrow> st y=su y) \<Longrightarrow> step f e q st x=step f e q su x"
  by (auto simp: step_def predPass_def)

lemma run_matches_solution:
  assumes rec: "recurs f e q st"
  shows "x\<in>tokens \<Longrightarrow> rank x<n \<Longrightarrow> run f e q n x=st x"
proof (induction n arbitrary: x)
  case 0 then show ?case by simp
next
  case (Suc n)
  have at_x: "st x=step f e q st x" using rec Suc.prems(1) by (simp add: recurs_def)
  have prior: "\<And>y. y\<in>tokens \<Longrightarrow> edge y x \<Longrightarrow> run f e q n y=st y"
    using Suc.IH edge_rank[OF Suc.prems(1)] Suc.prems(2) by (meson less_Suc_eq_le less_le_trans)
  show ?case by (simp only: run_suc[OF Suc.prems(1)] step_cong[OF prior] at_x[symmetric])
qed

lemma run_stable:
  "x\<in>tokens \<Longrightarrow> rank x<n \<Longrightarrow> rank x<m \<Longrightarrow> run f e q n x=run f e q m x"
proof (induction n arbitrary: m x)
  case 0 then show ?case by simp
next
  case (Suc n)
  obtain k where mk: "m=Suc k" using Suc.prems(3) by (cases m) auto
  have prior: "\<And>y. y\<in>tokens \<Longrightarrow> edge y x \<Longrightarrow> run f e q n y=run f e q k y"
    using Suc.IH edge_rank[OF Suc.prems(1)] Suc.prems(2,3) mk
    by (meson less_Suc_eq_le less_le_trans)
  show ?case by (simp only: mk run_suc[OF Suc.prems(1)] step_cong[OF prior])
qed
lemma finite_run_solves: "recurs f e q (run f e q 40)"
proof (unfold recurs_def, intro ballI)
  fix x assume x: "x\<in>tokens"
  have stable: "run f e q 40 x=run f e q (Suc 40) x"
    by (rule run_stable[OF x rank_bound[OF x]]) (use rank_bound[OF x] in arith)
  show "run f e q 40 x=step f e q (run f e q 40) x"
    by (rule trans[OF stable run_suc[OF x, where n=40]])
qed
lemma finite_run_unique:
  "recurs f e q st \<Longrightarrow> x\<in>tokens \<Longrightarrow> st x=run f e q 40 x"
  using run_matches_solution rank_bound by metis

definition auditAt where "auditAt st x = lift (predPass st x) (st x)"
definition auditOutput where "auditOutput f e q x = lift (predPass (run f e q 40) x) (run f e q 40 x)"
lemma audit_output_eq_native: "auditOutput f e q x = auditAt (run f e q 40) x"
  by (simp add: auditOutput_def auditAt_def)
lemma finite_audit_output_unique:
  assumes rec: "recurs f e q st" and x: "x\<in>tokens"
  shows "auditOutput f e q x=auditAt st x"
proof -
  have all: "\<And>y. y\<in>tokens \<Longrightarrow> run f e q 40 y=st y"
    by (rule sym, rule finite_run_unique[OF rec])
  have pred: "predPass (run f e q 40) x=predPass st x" by (simp add: predPass_def all)
  show ?thesis by (simp add: auditOutput_def auditAt_def pred all[OF x])
qed

ML \<open>
val roots = @{thms predecessor_iff step_eq_native rank_bound run_matches_solution finite_run_solves finite_run_unique audit_output_eq_native finite_audit_output_unique};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
