theory Core_Differential_Failure
  imports Main
begin

datatype node = N1 | N2 | N3 | N4 | N5

definition edge :: "node \<Rightarrow> node \<Rightarrow> bool" where
  "edge i j \<longleftrightarrow> (i = N1 \<and> j = N2) \<or> (i = N2 \<and> j = N3) \<or>
    (i = N1 \<and> j = N4) \<or> (i = N1 \<and> j = N5)"
definition ancestor :: "node \<Rightarrow> node \<Rightarrow> bool" where
  "ancestor i j \<longleftrightarrow> (i = N1 \<and> j \<noteq> N1) \<or> (i = N2 \<and> j = N3)"

lemma edge_ancestor: "edge i j \<Longrightarrow> ancestor i j"
  by (auto simp: edge_def ancestor_def)
lemma ancestor_transitive: "ancestor i j \<Longrightarrow> ancestor j k \<Longrightarrow> ancestor i k"
  by (auto simp: ancestor_def)
lemma ancestor_irreflexive: "\<not> ancestor i i"
  by (auto simp: ancestor_def)
lemma ancestors_exact: "tranclp edge i j \<longleftrightarrow> ancestor i j"
proof
  assume "tranclp edge i j"
  then show "ancestor i j"
    by (induction rule: tranclp_induct) (auto intro: edge_ancestor ancestor_transitive)
next
  assume "ancestor i j"
  then have "edge i j \<or> (i = N1 \<and> j = N3)"
    by (cases j) (auto simp: ancestor_def edge_def)
  then show "tranclp edge i j"
    by (meson edge_def tranclp.r_into_trancl tranclp.trancl_into_trancl)
qed

lemma ancestor_conjunctions_all:
  "(\<forall>j. ancestor j i \<longrightarrow> c j) \<longleftrightarrow>
    (case i of N1 \<Rightarrow> True | N2 \<Rightarrow> c N1 | N3 \<Rightarrow> c N1 \<and> c N2 |
      N4 \<Rightarrow> c N1 | N5 \<Rightarrow> c N1)"
  by (cases i) (auto simp: ancestor_def)

record 'o native =
  space :: "'o set"
  atlas :: "'o \<Rightarrow> bool"
  jet :: "'o \<Rightarrow> bool"
  member :: "'o \<Rightarrow> bool"
  valueCov :: "'o \<Rightarrow> bool"
  timeCov :: "'o \<Rightarrow> 'o \<Rightarrow> bool"

fun condition :: "'o native \<Rightarrow> node \<Rightarrow> bool" where
  "condition d N1 = (\<forall>r\<in>space d. atlas d r)"
| "condition d N2 = (\<forall>r\<in>space d. jet d r)"
| "condition d N3 = (\<forall>r\<in>space d. jet d r \<and> member d r)"
| "condition d N4 = (\<forall>r\<in>space d. atlas d r \<and> valueCov d r)"
| "condition d N5 = (\<forall>r\<in>space d. \<forall>s\<in>space d. atlas d r \<and> atlas d s \<and> timeCov d r s)"

fun counter :: "'o native \<Rightarrow> node \<Rightarrow> bool" where
  "counter d N1 = (\<exists>r\<in>space d. \<not> atlas d r)"
| "counter d N2 = (\<exists>r\<in>space d. \<not> jet d r)"
| "counter d N3 = (\<exists>r\<in>space d. jet d r \<longrightarrow> \<not> member d r)"
| "counter d N4 = (\<exists>r\<in>space d. atlas d r \<longrightarrow> \<not> valueCov d r)"
| "counter d N5 = (\<exists>r\<in>space d. \<exists>s\<in>space d. atlas d r \<longrightarrow> atlas d s \<longrightarrow> \<not> timeCov d r s)"

lemma condition_failure_witness: "(\<not> condition d i) \<longleftrightarrow> counter d i"
  by (cases i) auto
lemma all_conditions_complete:
  "(\<forall>i. condition d i) \<longleftrightarrow>
    condition d N1 \<and> condition d N2 \<and> condition d N3 \<and> condition d N4 \<and> condition d N5"
  by (metis node.exhaust)

locale selected_differential =
  fixes D :: "'e set"
    and lawSource :: "'e \<Rightarrow> 'law"
    and data :: "'e \<Rightarrow> 'o native"
    and lawOK :: "'law \<Rightarrow> bool"
begin

definition selectedCondition where
  "selectedCondition e i \<longleftrightarrow> e \<in> D \<and> condition (data e) i"
definition lawReady where
  "lawReady e \<longleftrightarrow> e \<in> D \<and> lawOK (lawSource e)"
definition ancestorReady where
  "ancestorReady e i \<longleftrightarrow> lawReady e \<and> (\<forall>j. ancestor j i \<longrightarrow> selectedCondition e j)"
definition minimalFailure where
  "minimalFailure e i \<longleftrightarrow> ancestorReady e i \<and> \<not> selectedCondition e i"
definition failure where
  "failure e \<longleftrightarrow> lawReady e \<and> \<not> (\<forall>i. selectedCondition e i)"

lemma selected_restricts:
  "e \<in> D \<Longrightarrow> selectedCondition e i \<longleftrightarrow> condition (data e) i"
  by (simp add: selectedCondition_def)
lemma ancestor_restricts:
  "e \<in> D \<Longrightarrow> ancestorReady e i \<longleftrightarrow>
    lawOK (lawSource e) \<and> (\<forall>j. ancestor j i \<longrightarrow> condition (data e) j)"
  by (simp add: ancestorReady_def lawReady_def selectedCondition_def)
lemma outside_selection_no_failure:
  "e \<notin> D \<Longrightarrow> \<not> failure e \<and> (\<forall>i. \<not> minimalFailure e i)"
  by (simp add: failure_def minimalFailure_def ancestorReady_def lawReady_def)
lemma failure_vs_operative:
  "e \<in> D \<Longrightarrow> failure e \<longleftrightarrow> lawOK (lawSource e) \<and>
    \<not> (lawOK (lawSource e) \<and> (\<forall>i. condition (data e) i))"
  by (auto simp: failure_def lawReady_def selectedCondition_def)
lemma minimal_failure_witness:
  "e \<in> D \<Longrightarrow> minimalFailure e i \<longleftrightarrow>
    ancestorReady e i \<and> counter (data e) i"
  by (simp add: minimalFailure_def selectedCondition_def condition_failure_witness)

lemma failure_cover: "failure e \<longleftrightarrow> (\<exists>i. minimalFailure e i)"
proof -
  have nodes: "(\<forall>i. selectedCondition e i) \<longleftrightarrow>
    selectedCondition e N1 \<and> selectedCondition e N2 \<and> selectedCondition e N3 \<and>
    selectedCondition e N4 \<and> selectedCondition e N5"
    by (metis node.exhaust)
  have regions: "(\<exists>i. minimalFailure e i) \<longleftrightarrow>
    minimalFailure e N1 \<or> minimalFailure e N2 \<or> minimalFailure e N3 \<or>
    minimalFailure e N4 \<or> minimalFailure e N5"
    by (metis node.exhaust)
  have "failure e \<longleftrightarrow> lawReady e \<and> \<not>
    (selectedCondition e N1 \<and> selectedCondition e N2 \<and> selectedCondition e N3 \<and>
      selectedCondition e N4 \<and> selectedCondition e N5)"
    by (simp only: failure_def nodes)
  also have "... \<longleftrightarrow> minimalFailure e N1 \<or> minimalFailure e N2 \<or>
    minimalFailure e N3 \<or> minimalFailure e N4 \<or> minimalFailure e N5"
    by (simp only: minimalFailure_def ancestorReady_def ancestor_conjunctions_all node.case) blast
  also have "... \<longleftrightarrow> (\<exists>i. minimalFailure e i)" using regions by blast
  finally show ?thesis .
qed

lemma failure_region_union:
  "{e. failure e} = (\<Union>i. {e. minimalFailure e i})"
  using failure_cover by auto
lemma minimal_antichain:
  "minimalFailure e i \<Longrightarrow> minimalFailure e j \<Longrightarrow>
    \<not> tranclp edge i j \<and> \<not> tranclp edge j i"
  by (auto simp: minimalFailure_def ancestorReady_def ancestors_exact)

definition signature where "signature e i = minimalFailure e i"
lemma signature_support: "{i. signature e i} = {i. minimalFailure e i}"
  by (simp add: signature_def)
lemma signature_nonzero: "signature e \<noteq> (\<lambda>_. False) \<longleftrightarrow> failure e"
  by (auto simp: fun_eq_iff signature_def failure_cover)
lemma finite_nonempty_failure_set:
  "failure e \<Longrightarrow> finite {i. minimalFailure e i} \<and> {i. minimalFailure e i} \<noteq> {}"
proof -
  have all: "(UNIV::node set) = {N1,N2,N3,N4,N5}"
    by (rule set_eqI, case_tac x, auto)
  assume f: "failure e"
  have "finite (UNIV::node set)" by (simp add: all)
  then have fin: "finite {i. minimalFailure e i}"
    by (rule finite_subset[OF subset_UNIV])
  show ?thesis using fin f failure_cover by auto
qed
end

definition independentJet :: "unit native" where
  "independentJet = \<lparr>space = UNIV, atlas = (\<lambda>_. False), jet = (\<lambda>_. True),
    member = (\<lambda>_. True), valueCov = (\<lambda>_. False), timeCov = (\<lambda>_ _. False)\<rparr>"
lemma jet_does_not_require_atlas:
  "condition independentJet N2 \<and> \<not> condition independentJet N1"
  by (simp add: independentJet_def)

ML \<open>
val roots = @{thms edge_ancestor ancestor_transitive ancestor_irreflexive ancestors_exact ancestor_conjunctions_all condition_failure_witness all_conditions_complete selected_differential.selected_restricts selected_differential.ancestor_restricts selected_differential.outside_selection_no_failure selected_differential.failure_vs_operative selected_differential.minimal_failure_witness selected_differential.failure_cover selected_differential.failure_region_union selected_differential.minimal_antichain selected_differential.signature_support selected_differential.signature_nonzero selected_differential.finite_nonempty_failure_set jet_does_not_require_atlas};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
