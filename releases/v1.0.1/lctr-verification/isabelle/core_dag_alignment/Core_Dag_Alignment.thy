theory Core_Dag_Alignment
  imports "../core_dag_recursion/Core_Dag_Recursion"
begin

lemmas finite_dag_deterministic_state_fold = Core_Dag_Recursion.native_predecessor_state_fold
lemmas empty_vertices_allow_empty_states = Core_Dag_Recursion.empty_vertices_empty_states
lemmas cyclic_update_can_have_no_solution = Core_Dag_Recursion.cycle_can_have_no_solution
lemmas cyclic_update_can_have_multiple_solutions = Core_Dag_Recursion.cycle_can_have_multiple_solutions

lemma edge_orientation_control:
  "(\<lambda>x::bool. Some x) =
    state_update UNIV
      (\<lambda>x f. if x then \<not> incoming_values {(False,True)} x f False else False)
      (\<lambda>x. Some x)"
  by (rule ext) (simp add: state_update_def incoming_values_def)

ML \<open>
val roots = @{thms finite_dag_deterministic_state_fold empty_vertices_allow_empty_states cyclic_update_can_have_no_solution cyclic_update_can_have_multiple_solutions edge_orientation_control};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
