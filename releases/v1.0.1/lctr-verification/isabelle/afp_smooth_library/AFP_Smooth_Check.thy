theory AFP_Smooth_Check imports Smooth begin
ML \<open>
val roots = @{thms higher_differentiable_on_compose higher_differentiable_on_real_Suc
 higher_differentiable_on_imp_continuous_on higher_differentiable_on_subset};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
