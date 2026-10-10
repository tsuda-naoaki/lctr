theory Core_Law_Component_Charts
 imports "LCTR_Core_Native_Law_Components.Core_Native_Law_Components"
 "LCTR_Core_Local_Charts.Core_Local_Charts"
begin
locale native_component_chart =
 native_law_context C D B R Bind source_order rho indices val_carriers observable
 for C :: "'c set" and D :: "'d set" and B :: "'b set"
 and R :: "('c\<times>'d\<times>'b)set"
 and Bind :: "(('c\<times>'d\<times>'b)\<times>('c\<times>'d\<times>'b))set"
 and source_order :: "('c\<times>'c)set" and rho :: "'c set set\<Rightarrow>real"
 and indices :: "'q set" and val_carriers :: "'q\<Rightarrow>'v set"
 and observable :: "'q\<Rightarrow>'b set\<Rightarrow>'v" +
 fixes a :: "('q,'v) native_component_input" and Charts :: "'i set"
 and TD :: "'i\<Rightarrow>real set" and TT :: "'i\<Rightarrow>'theta set"
 and ID :: "'i\<Rightarrow>('q\<Rightarrow>'v)set" and IT :: "'i\<Rightarrow>'nin set"
 and OD :: "'i\<Rightarrow>('q\<Rightarrow>'v)set" and OT :: "'i\<Rightarrow>'nout set"
 and tc :: "'i\<Rightarrow>real\<Rightarrow>'theta"
 and ic :: "'i\<Rightarrow>('q\<Rightarrow>'v)\<Rightarrow>'nin"
 and oc :: "'i\<Rightarrow>('q\<Rightarrow>'v)\<Rightarrow>'nout"
 assumes component: "component_input_typed a"
 and atlas: "coordinate_atlas (evaluation_times a) Charts TD TT ID IT OD OT tc ic oc
   (input_value(generated a)) (output_value(generated a))"
begin
sublocale chart: coordinate_atlas "evaluation_times a" Charts TD TT ID IT OD OT tc ic oc
 "input_value(generated a)" "output_value(generated a)"
 by (rule atlas)
lemma same_law_values:
 "input_value(generated a)t=restrict(\<lambda>q. curve q t)(in_indices a) \<and>
  output_value(generated a)t=restrict(\<lambda>q. curve q t)(out_indices a)"
 by (rule generated_value_components)
lemma native_coordinate_bijective:
 "i\<in>Charts \<Longrightarrow> bij_betw(tc i)(chart.joint i)(chart.numeric i)"
 by (rule chart.time_coordinate_bijective)
lemma native_side_curve:
 assumes i: "i\<in>Charts" and t: "t\<in>chart.joint i"
 shows "input_value(generated a)t\<in>ID i \<and> output_value(generated a)t\<in>OD i \<and>
  fst(chart.curve i(tc i t))=ic i(input_value(generated a)t) \<and>
  snd(chart.curve i(tc i t))=oc i(output_value(generated a)t)"
 using chart.side_curve_generated[OF i t] t unfolding chart.joint_def by simp
lemma native_input_curve:
 "i\<in>Charts \<Longrightarrow> t\<in>chart.joint i \<Longrightarrow>
  input_value(generated a)t\<in>ID i \<and> fst(chart.curve i(tc i t))=ic i(input_value(generated a)t)"
 using native_side_curve by blast
lemma native_output_curve:
 "i\<in>Charts \<Longrightarrow> t\<in>chart.joint i \<Longrightarrow>
  output_value(generated a)t\<in>OD i \<and> snd(chart.curve i(tc i t))=oc i(output_value(generated a)t)"
 using native_side_curve by blast
lemma every_law_evaluation_covered:
 assumes t: "t\<in>evaluation_times a"
 shows "\<exists>i\<in>Charts. t\<in>chart.joint i \<and>
  input_value(generated a)t\<in>ID i \<and> output_value(generated a)t\<in>OD i \<and>
  fst(chart.curve i(tc i t))=ic i(input_value(generated a)t) \<and>
  snd(chart.curve i(tc i t))=oc i(output_value(generated a)t)"
 using chart.joint_domain_coverage[OF t] native_side_curve by blast
end
ML \<open>
val roots = @{thms native_component_chart.same_law_values native_component_chart.native_coordinate_bijective
 native_component_chart.native_side_curve native_component_chart.native_input_curve
 native_component_chart.native_output_curve native_component_chart.every_law_evaluation_covered};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
