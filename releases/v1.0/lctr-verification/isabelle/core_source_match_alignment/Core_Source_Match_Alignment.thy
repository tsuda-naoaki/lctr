theory Core_Source_Match_Alignment
  imports "../core_source_match/Core_Source_Match"
begin

lemma l1_iff_injective:
  "(\<forall>u. \<forall>a\<in>(f u) ` (D u). \<exists>!s. s\<in>D u \<and> f u s=a) =
    (\<forall>u. inj_on (f u) (D u))"
  by (simp only: Core_Source_Match.l1_iff_injective)
lemmas arrival_recovery = Core_Source_Match.arrival_recovery
lemma recover_srcMatch:
  assumes inj: "inj_on (f v) (D v)" and dom: "recovery D f u a\<in>D v"
  shows "recovery D f v (src_match D f u v a)=recovery D f u a"
  unfolding src_match_def
  by (rule recover_arrival[where D=D and f=f and u=v, OF inj dom])
lemmas same_source_native_match = Core_Source_Match.same_source_native_match
lemmas srcGraph_iff_same_recovery = Core_Source_Match.src_graph_iff_same_recovery
lemmas source_match_inverse_graph = Core_Source_Match.source_match_inverse_graph
lemma recovery_injective:
  "inj_on (recovery D f u) ((f u) ` (D u))"
proof (rule inj_onI)
  fix a b
  assume a: "a\<in>(f u) ` (D u)" and b: "b\<in>(f u) ` (D u)"
    and eq: "recovery D f u a=recovery D f u b"
  show "a=b" using
    arrival_recovery[where D=D and f=f and u=u and a=a, OF a]
    arrival_recovery[where D=D and f=f and u=u and a=b, OF b] eq by metis
qed
lemmas source_match_functional = Core_Source_Match.source_match_functional
lemmas source_match_injective = Core_Source_Match.source_match_injective
definition word_kinds where "word_kinds word = map fst word"
definition word_positions where "word_positions u word = u # map snd word"
lemma sourceWord_encoding:
  "word_kinds [(Src,v)]=[Src] \<and> word_positions u [(Src,v)]=[u,v]"
  by (simp add: word_kinds_def word_positions_def)
lemmas sourceWord_action = Core_Source_Match.source_word_action
lemmas equal_recovery_orbit = Core_Source_Match.equal_recovery_orbit
lemmas mutual_arrival_order_separation = Core_Source_Match.mutual_arrival_order_separation
lemma equal_display_not_source_match:
  "()=() \<and> \<not>src_graph (\<lambda>u::bool. {u}) (\<lambda>_ _. ()) False True () ()"
  by (simp add: Core_Source_Match.equal_display_not_source_match)

ML \<open>
val roots = @{thms l1_iff_injective arrival_recovery recover_srcMatch same_source_native_match srcGraph_iff_same_recovery source_match_inverse_graph recovery_injective source_match_functional source_match_injective sourceWord_encoding sourceWord_action equal_recovery_orbit mutual_arrival_order_separation equal_display_not_source_match};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
