theory Core_Cycle_Count_Input
  imports Main
begin

record ('p,'d) cycle_source =
  phase :: "nat \<Rightarrow> 'p"
  display :: "nat \<Rightarrow> 'd"

definition update where "update (k::nat)=k+1"
definition state where "state s k=(k,phase s k,display s k)"

lemma counter_update: "update k=k+1" by (simp add: update_def)
lemma counter_distinction: "update k=update j \<longleftrightarrow> k=j" by (simp add: update_def)
lemma phase_display_correspondence: "state s k=(k,phase s k,display s k)" by (simp add: state_def)
lemma updated_correspondence: "state s (update k)=(k+1,phase s (k+1),display s (k+1))"
  by (simp add: state_def update_def)
lemma repeated_display_allowed:
  "\<exists>s::(unit,unit) cycle_source. display s 0=display s 1 \<and> state s 0\<noteq>state s 1"
  by (simp add: state_def)

ML \<open>
val roots = @{thms counter_update counter_distinction phase_display_correspondence
  updated_correspondence repeated_display_allowed};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = List.app (fn th => writeln ("LCTR_ROOT_STATEMENT=" ^ Thm.string_of_thm @{context} th)) roots;
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
