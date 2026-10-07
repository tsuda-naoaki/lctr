theory Core_Joint_Condition_Routes
 imports "LCTR_Core_Joint_Law_Evaluation.Core_Joint_Law_Evaluation"
 "LCTR_Core_Continuum_Datum.Core_Continuum_Datum"
 "LCTR_Core_Differential_Failure.Core_Differential_Failure"
begin
type_synonym ('i,'l,'v,'r,'w) joint_side = "(('i\<times>'l)\<Rightarrow>'v)\<times>('r\<Rightarrow>'w)"
context native_joint_law
begin
lemma joint_descent_route:
 assumes r: "r\<in>rel_indices" and dom: "A\<subseteq>source_product"
 and sat: "source_saturated A (rel_carrier r)(source_relation r)"
 and t: "t\<in>real_time" and x: "x\<in>source_product"
 and same: "source_projection x=joint_curve(order_inverse t)" and v: "v\<in>rel_carrier r"
 shows "(t,v)\<in>real_relation r \<longleftrightarrow> (x,v)\<in>source_relation r"
 using joint_source_membership[OF dom source_typed[OF r] sat inverse_typed[OF t] x same v] t
 by (simp add: real_relation_def)

lemma common_time_route:
 assumes i: "i\<in>J"
 shows "\<exists>sigma. observer_real C D B (R i)(Bind i)(source_order i)sigma"
proof -
 interpret o: observer_linear C D B "R i" "Bind i" "source_order i"
  by (rule linear[OF i])
 interpret common: common_native_time C D B "R i" "R base" "Bind i" "Bind base"
  "source_order i" "source_order base"
  by unfold_locales (use common[OF i base_member] source[OF i base_member] in auto)
 from common.embedding_transfers[OF base_time.order_iff]
 obtain sigma where sigma: "(\<forall>x\<in>o.OrderTime. \<forall>y\<in>o.OrderTime.
  (o.order_lt x y \<longleftrightarrow> sigma x<sigma y)) \<and>
  (\<forall>q\<in>o.OrderTime. sigma q=rho(common.order_map q))" ..
 have "observer_real C D B (R i)(Bind i)(source_order i)sigma"
  by unfold_locales (rule conjunct1[OF sigma])
 then show ?thesis by (rule exI[where x=sigma])
qed
lemma individual_trajectory_route:
 "q\<in>common_domain \<Longrightarrow> i\<in>J \<Longrightarrow> joint_curve q i=individual_curve i q"
 by (rule native_joint_components)

context
 fixes obs :: "'r\<Rightarrow>real\<Rightarrow>'w" and A :: "'a set"
 and Oidx :: "'a\<Rightarrow>bool\<Rightarrow>('i\<times>'l)set" and Ridx :: "'a\<Rightarrow>bool\<Rightarrow>'r set"
 and H :: "'a\<Rightarrow>real set"
 and E :: "'a\<Rightarrow>(real\<times>('i,'l,'v,'r,'w)joint_side)set"
 and S :: "'a\<Rightarrow>((real\<times>('i,'l,'v,'r,'w)joint_side)\<times>('i,'l,'v,'r,'w)joint_side)set"
 and allowed :: "real set\<Rightarrow>bool"
 and faithful :: "('a\<Rightarrow>((real\<times>('i,'l,'v,'r,'w)joint_side)\<times>('i,'l,'v,'r,'w)joint_side)carrier_reindex)\<Rightarrow>bool"
begin
abbreviation selected_joint_family where
 "selected_joint_family \<equiv> joint_family obs A Oidx Ridx H E S allowed faithful"
lemma joint_law_route:
 "selected_law_family.failure {()}(\<lambda>_. selected_joint_family)() \<longleftrightarrow>
  \<not>all_conditions selected_joint_family"
 by (rule joint_failure_exact)
lemma joint_law_minimal_route:
 "\<not>all_conditions selected_joint_family \<longleftrightarrow>
 (\<exists>i. selected_law_family.minimal_class {()}(\<lambda>_. selected_joint_family)()i)"
 by (rule joint_minimal_failure_cover)
lemma selected_joint_law_exact:
 "()\<in>Dsel \<Longrightarrow> fst(selected_joint_family,data())=selected_joint_family" by simp
lemma joint_differential_route:
 "()\<in>Dsel \<Longrightarrow>
 (selected_differential.failure Dsel (\<lambda>_. selected_joint_family) data all_conditions () \<longleftrightarrow>
 all_conditions selected_joint_family \<and> \<not>(\<forall>i. Core_Differential_Failure.condition(data())i))"
 by (simp add: selected_differential.failure_def selected_differential.lawReady_def
  selected_differential.selectedCondition_def)
lemma joint_differential_minimal_route:
 "selected_differential.failure Dsel (\<lambda>_. selected_joint_family) data all_conditions () \<longleftrightarrow>
 (\<exists>i. selected_differential.minimalFailure Dsel (\<lambda>_. selected_joint_family) data all_conditions ()i)"
 by (rule selected_differential.failure_cover)
lemma joint_differential_requires_same_law:
 "selected_differential.failure Dsel (\<lambda>_. selected_joint_family) data all_conditions () \<Longrightarrow>
 all_conditions selected_joint_family"
 by (simp add: selected_differential.failure_def selected_differential.lawReady_def)
lemma joint_differential_missing_domain:
 "()\<notin>Dsel \<Longrightarrow>
 \<not>selected_differential.failure Dsel (\<lambda>_. selected_joint_family) data all_conditions ()"
 by (simp add: selected_differential.failure_def selected_differential.lawReady_def)
end
end
context packet_evaluation
begin
lemma record_resolution_route:
 "approx_ready f e s 2 \<Longrightarrow>
 (fa s 2 \<longleftrightarrow> packet_tolerance p 2<cell_width(packet_maps p)(packet_indices p)(packet_cells p))"
 by (rule width_failure)
lemma object_discernibility_route:
 "approx_ready f e s 4 \<Longrightarrow>
 (fa s 4 \<longleftrightarrow> packet_tolerance p 4<scalar(packet_scalars p 2))"
 using actual_failure[where i=4] by (simp add: actual_def first_defect_def not_le)
end

ML \<open>
val roots = @{thms native_joint_law.joint_descent_route native_joint_law.common_time_route
 native_joint_law.individual_trajectory_route packet_evaluation.record_resolution_route
 packet_evaluation.object_discernibility_route native_joint_law.joint_law_route
 native_joint_law.joint_law_minimal_route native_joint_law.selected_joint_law_exact
 native_joint_law.joint_differential_route native_joint_law.joint_differential_minimal_route
 native_joint_law.joint_differential_requires_same_law native_joint_law.joint_differential_missing_domain};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
