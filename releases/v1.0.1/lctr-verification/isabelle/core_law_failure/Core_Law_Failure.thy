theory Core_Law_Failure
  imports Main
begin

datatype law_node = Law1 | Law2 | Law3 | Law4 | Law5

definition edge where "edge i j \<longleftrightarrow> (i = Law1 \<and> j = Law3) \<or> (i = Law3 \<and> j = Law5)"
definition ancestor where "ancestor i j \<longleftrightarrow> edge i j \<or> (i = Law1 \<and> j = Law5)"
fun rank :: "law_node \<Rightarrow> nat" where
  "rank Law1 = 0" | "rank Law2 = 0" | "rank Law3 = 1" | "rank Law4 = 0" | "rank Law5 = 2"

lemma forall_nodes: "(\<forall>i. P i) \<longleftrightarrow> P Law1 \<and> P Law2 \<and> P Law3 \<and> P Law4 \<and> P Law5"
  by (metis law_node.exhaust)
lemma exists_nodes: "(\<exists>i. P i) \<longleftrightarrow> P Law1 \<or> P Law2 \<or> P Law3 \<or> P Law4 \<or> P Law5"
  by (metis law_node.exhaust)
lemma edge_rank: "edge i j \<Longrightarrow> rank i < rank j"
  unfolding edge_def by auto
lemma ancestor_transitive: "ancestor i j \<Longrightarrow> ancestor j k \<Longrightarrow> ancestor i k"
  unfolding ancestor_def edge_def by auto
lemma ancestor_irreflexive: "\<not> ancestor i i"
  unfolding ancestor_def edge_def by auto

lemma ancestors_exact: "tranclp edge i j \<longleftrightarrow> ancestor i j"
proof
  assume "tranclp edge i j"
  then show "ancestor i j"
    by (induction rule: tranclp_induct) (auto simp: ancestor_def edge_def)
next
  assume a: "ancestor i j"
  have p13: "tranclp edge Law1 Law3"
    by (rule tranclp.r_into_trancl) (simp add: edge_def)
  have p35: "tranclp edge Law3 Law5"
    by (rule tranclp.r_into_trancl) (simp add: edge_def)
  have p15: "tranclp edge Law1 Law5" by (rule tranclp_trans[OF p13 p35])
  show "tranclp edge i j" using a p15 unfolding ancestor_def by (auto intro: tranclp.r_into_trancl)
qed

lemma graph_acyclic: "\<not> tranclp edge i i"
  using ancestors_exact ancestor_irreflexive by blast

definition ancestors_hold where "ancestors_hold K i \<longleftrightarrow> (\<forall>j. ancestor j i \<longrightarrow> K j)"
definition minimal where "minimal selected K i \<longleftrightarrow> selected \<and> ancestors_hold K i \<and> \<not> K i"
definition fails where "fails selected K \<longleftrightarrow> selected \<and> \<not> (\<forall>i. K i)"

lemma ancestors_explicit:
  "ancestors_hold K Law1 \<and> ancestors_hold K Law2 \<and> ancestors_hold K Law4 \<and>
   (ancestors_hold K Law3 \<longleftrightarrow> K Law1) \<and>
   (ancestors_hold K Law5 \<longleftrightarrow> K Law1 \<and> K Law3)"
  by (simp add: ancestors_hold_def forall_nodes ancestor_def edge_def)

lemma failure_cover: "fails selected K \<longleftrightarrow> (\<exists>i. minimal selected K i)"
  unfolding fails_def minimal_def ancestors_hold_def
  by (auto simp: forall_nodes exists_nodes ancestor_def edge_def)

lemma minimal_antichain:
  assumes "minimal selected K i" "minimal selected K j"
  shows "\<not> tranclp edge i j \<and> \<not> tranclp edge j i"
  using assms unfolding minimal_def ancestors_hold_def
  by (auto simp: ancestors_exact)

lemma outside_selection: "\<not> fails False K \<and> (\<forall>i. \<not> minimal False K i)"
  by (simp add: fails_def minimal_def)

lemma failure_domain_union:
  "{e. fails (selected e) (K e)} = (\<Union>i. {e. minimal (selected e) (K e) i})"
  using failure_cover by auto

datatype eval_state = Sat | Failed | Unformed
definition classified_state where
  "classified_state selected K i =
    (if \<not> selected then Unformed else if K i then Sat
     else if ancestors_hold K i then Failed else Unformed)"

lemma failed_state_exact:
  "classified_state selected K i = Failed \<longleftrightarrow> minimal selected K i"
  by (auto simp: classified_state_def minimal_def)

lemma sat_state_exact:
  "classified_state selected K i = Sat \<longleftrightarrow> selected \<and> K i"
  by (auto simp: classified_state_def)

lemma failure_state_exists:
  "(\<exists>i. classified_state selected K i = Failed) \<longleftrightarrow> fails selected K"
  using failure_cover failed_state_exact by blast

ML \<open>
val roots = @{thms edge_rank ancestors_exact graph_acyclic ancestors_explicit
  failure_cover minimal_antichain outside_selection failure_domain_union
  failed_state_exact sat_state_exact failure_state_exists};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int (length roots));
\<close>
end
