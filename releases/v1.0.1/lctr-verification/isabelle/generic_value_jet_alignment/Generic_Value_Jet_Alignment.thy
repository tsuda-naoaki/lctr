theory Generic_Value_Jet_Alignment
  imports "LCTR_Generic_Value_Jet_Lifts.Generic_Value_Jet_Lifts"
    "LCTR_Value_Jet_Analytic_Realization.Value_Jet_Analytic_Realization"
begin
lemmas jetAt_eventual_eq = Zero_Completed_Jet_Germs.zjet_germ
lemmas domain_realization = Value_Jet_Analytic_Realization.domain_realization
lemmas lift_unique = Value_Jet_Lift_Algebra.lift_unique
lemmas lift_identity = Value_Jet_Lift_Algebra.lift_identity
lemmas lift_left_inverse = Generic_Value_Jet_Lifts.generic_lift_left_inverse
lemmas lift_bijective = Generic_Value_Jet_Lifts.generic_lift_bijective
lemmas lift_composition = Generic_Value_Jet_Lifts.generic_lift_composition
lemmas relation_image = Value_Jet_Lift_Algebra.relation_image
lemmas value_jet_relation_image = Generic_Value_Jet_Lifts.generic_value_jet_relation_image
lemmas empty_value_chart_control = Zero_Completed_Jet_Germs.empty_value_chart_control
ML \<open>
val roots = @{thms jetAt_eventual_eq domain_realization lift_unique lift_identity
  lift_left_inverse lift_bijective lift_composition relation_image
  value_jet_relation_image empty_value_chart_control};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
