theory Core_SMT_Boolean_Rules
  imports Main
begin
lemma bool_eq_false: "(t = False) = (~ t)" by simp
lemma ite_false_cond: "(if False then x else y) = y" by simp
ML \<open>
  val roots = @{thms bool_eq_false ite_false_cond};
  if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
