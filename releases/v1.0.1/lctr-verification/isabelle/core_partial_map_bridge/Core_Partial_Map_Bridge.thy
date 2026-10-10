theory Core_Partial_Map_Bridge
  imports Main
begin

definition map_graph where "map_graph A f x y \<longleftrightarrow> x\<in>A \<and> f x=y"
definition compose where "compose r s x z \<longleftrightarrow> (\<exists>y. r x y \<and> s y z)"

lemma map_graph_domain: "(\<exists>y. map_graph A f x y) \<longleftrightarrow> x\<in>A"
  by (auto simp: map_graph_def)

lemma map_graph_value: "x\<in>A \<Longrightarrow> (map_graph A f x y \<longleftrightarrow> f x=y)"
  by (simp add: map_graph_def)

lemma general_composition_domain:
  "(\<exists>z. compose r s x z) \<longleftrightarrow> (\<exists>y. r x y \<and> (\<exists>z. s y z))"
  by (auto simp: compose_def)

lemma partial_map_composition:
  "compose (map_graph A f) (map_graph B g) x z \<longleftrightarrow>
    x\<in>A \<and> f x\<in>B \<and> g(f x)=z"
  by (auto simp: compose_def map_graph_def)

lemma composition_functional:
  "compose (map_graph A f) (map_graph B g) x z \<Longrightarrow>
   compose (map_graph A f) (map_graph B g) x w \<Longrightarrow> z=w"
  by (simp add: partial_map_composition)

lemma empty_domain_composition:
  "A={} \<Longrightarrow> \<not> compose (map_graph A f) (map_graph B g) x z"
  by (simp add: partial_map_composition)

lemma noninjective_composition_control:
  "compose (map_graph UNIV (\<lambda>_::bool. ())) (map_graph UNIV id) False () \<and>
   compose (map_graph UNIV (\<lambda>_::bool. ())) (map_graph UNIV id) True () \<and> False\<noteq>True"
  by (simp add: partial_map_composition)

ML \<open>
val roots = @{thms map_graph_domain map_graph_value general_composition_domain
 partial_map_composition composition_functional empty_domain_composition noninjective_composition_control};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
