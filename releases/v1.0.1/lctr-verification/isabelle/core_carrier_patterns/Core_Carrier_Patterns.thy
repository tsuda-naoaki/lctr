theory Core_Carrier_Patterns
 imports "LCTR_Chapter02_Isabelle_Bridge.Chapter02_Isabelle_Bridge"
begin

record ('z,'s,'t,'l) carrier_input =
 selected_indices :: "'z set"
 local_carrier :: "'s \<Rightarrow> role \<Rightarrow> 'l set"
 scene_at :: "'z \<Rightarrow> 's"
 tracked_at :: "'z \<Rightarrow> 't"
 component_at :: "'z \<Rightarrow> role \<Rightarrow> 'l"
 correspondence_entered :: "'s \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> bool"
 detector_retains :: "'s \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> bool"
 observer_receives :: "'s \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> bool"
 observer_combines :: "'s \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> bool"
 abstracted_from :: "'t \<Rightarrow> 's \<Rightarrow> 'l \<Rightarrow> bool"

definition valid_carrier_input where
 "valid_carrier_input a \<longleftrightarrow> (\<forall>z\<in>selected_indices a.
   (\<forall>r. component_at a z r \<in> local_carrier a (scene_at a z) r) \<and>
   correspondence_entered a (scene_at a z)
     (component_at a z Clock)(component_at a z Body)(component_at a z Detector) \<and>
   detector_retains a (scene_at a z)
     (component_at a z Clock)(component_at a z Body)(component_at a z Detector) \<and>
   observer_receives a (scene_at a z)
     (component_at a z Clock)(component_at a z Detector)(component_at a z Body)(component_at a z Observer) \<and>
   observer_combines a (scene_at a z)
     (component_at a z Clock)(component_at a z Detector)(component_at a z Body)(component_at a z Observer) \<and>
   abstracted_from a (tracked_at a z)(scene_at a z)(component_at a z Body))"

definition role_at where "role_at a r z = role_instance id (component_at a) r z"
definition role_domain where
 "role_domain a r = image (role_at a (role_of_realization r)) (selected_indices a)"
definition body_pair where "body_pair a z = (tracked_at a z, role_at a Body z)"

record ('z,'l,'c,'d,'o,'m) physical_carriers =
 realize_clock :: "('z,'l) role_instance \<Rightarrow> 'c"
 realize_detector :: "('z,'l) role_instance \<Rightarrow> 'd"
 realize_observer :: "('z,'l) role_instance \<Rightarrow> 'o"
 communication_couples :: "'m \<Rightarrow> 'o \<Rightarrow> 'o \<Rightarrow> bool"

fun realize_tagged ::
 "('z,'l,'c,'d,'o,'m) physical_carriers \<Rightarrow>
  realization_role \<Rightarrow> ('z,'l) role_instance \<Rightarrow> ('c + ('d + 'o))" where
 "realize_tagged p RClock x = Inl (realize_clock p x)"
| "realize_tagged p RDetector x = Inr (Inl (realize_detector p x))"
| "realize_tagged p RObserver x = Inr (Inr (realize_observer p x))"
definition carrier_at where
 "carrier_at a p r z = realize_tagged p r (role_at a (role_of_realization r) z)"

datatype comparison_role_type = CClock | CDetector
fun comparison_role where "comparison_role CClock=RClock" | "comparison_role CDetector=RDetector"
datatype comparison_choice = Shared | Separated
fun comparison_condition where
 "comparison_condition Shared x y = (x=y)"
| "comparison_condition Separated x y = (x\<noteq>y)"
datatype observer_choice = ObserverShared | Distributed
fun observer_condition where
 "observer_condition p ObserverShared x y = (x=y)"
| "observer_condition p Distributed x y =
   (x\<noteq>y \<and> (\<exists>m. communication_couples p m x y))"

record ('z,'l,'t,'c,'d,'o) carrier_assembly =
 assembled_clock :: "'c \<times> 'c"
 assembled_detector :: "'d \<times> 'd"
 assembled_observer :: "'o \<times> 'o"
 assembled_body :: "bool \<Rightarrow> 't \<times> ('z,'l) role_instance"
definition assemble where
 "assemble a p ix =
  \<lparr>assembled_clock=(realize_clock p (role_at a Clock (ix False)),realize_clock p (role_at a Clock (ix True))),
   assembled_detector=(realize_detector p (role_at a Detector (ix False)),realize_detector p (role_at a Detector (ix True))),
   assembled_observer=(realize_observer p (role_at a Observer (ix False)),realize_observer p (role_at a Observer (ix True))),
   assembled_body=(\<lambda>k. body_pair a (ix k))\<rparr>"

lemma realization_domain_exact:
 "x\<in>role_domain a r \<longleftrightarrow>
  (\<exists>i\<in>selected_indices a. role_at a (role_of_realization r) i=x)"
 by (auto simp: role_domain_def)
lemma role_index_preserved:
 "ri_zeta(role_at a r i)=i \<and> ri_role(role_at a r i)=r"
 by (simp add: role_at_def role_instance_def)
lemma body_pair_distinct:
 "i\<noteq>j \<Longrightarrow> body_pair a i \<noteq> body_pair a j"
 by (auto simp: body_pair_def role_at_def role_instance_def)
lemma body_abstraction_retained:
 "valid_carrier_input a \<Longrightarrow> i\<in>selected_indices a \<Longrightarrow>
  abstracted_from a (fst(body_pair a i))(scene_at a i)(component_at a i Body)"
 by (auto simp: valid_carrier_input_def body_pair_def)
lemma carrier_condition_from_specified_values:
 assumes at: "\<And>k. carrier_at a p (comparison_role r)(ix k)=v k"
 and choice: "comparison_condition ch (v False)(v True)"
 shows "comparison_condition ch
  (carrier_at a p (comparison_role r)(ix False))
  (carrier_at a p (comparison_role r)(ix True))"
 using choice by (simp only: at)
lemma comparison_inl:
 "comparison_condition ch (Inl x)(Inl y) \<longleftrightarrow> comparison_condition ch x y"
 by (cases ch) simp_all
lemma comparison_inr:
 "comparison_condition ch (Inr x)(Inr y) \<longleftrightarrow> comparison_condition ch x y"
 by (cases ch) simp_all
lemma role_typed_combination:
 assumes distinct: "ix False\<noteq>ix True"
 and at: "\<And>r k. carrier_at a p (comparison_role r)(ix k)=v r k"
 and choice: "\<And>r. comparison_condition (ch r)(v r False)(v r True)"
 and obs: "observer_condition p och
  (realize_observer p(role_at a Observer(ix False)))
  (realize_observer p(role_at a Observer(ix True)))"
 shows
 "comparison_condition (ch CClock)(fst(assembled_clock(assemble a p ix)))(snd(assembled_clock(assemble a p ix))) \<and>
  comparison_condition (ch CDetector)(fst(assembled_detector(assemble a p ix)))(snd(assembled_detector(assemble a p ix))) \<and>
  observer_condition p och(fst(assembled_observer(assemble a p ix)))(snd(assembled_observer(assemble a p ix))) \<and>
  (\<forall>k. assembled_body(assemble a p ix)k=body_pair a(ix k)) \<and>
  assembled_body(assemble a p ix)False\<noteq>assembled_body(assemble a p ix)True"
proof -
 have c: "comparison_condition (ch CClock)
  (carrier_at a p RClock(ix False))(carrier_at a p RClock(ix True))"
  using carrier_condition_from_specified_values[OF at choice, where r=CClock] by simp
 have d: "comparison_condition (ch CDetector)
  (carrier_at a p RDetector(ix False))(carrier_at a p RDetector(ix True))"
  using carrier_condition_from_specified_values[OF at choice, where r=CDetector] by simp
 show ?thesis using c d obs body_pair_distinct[OF distinct, where a=a]
  by (simp add: assemble_def carrier_at_def comparison_inl comparison_inr)
qed
lemma body_independent_of_realization:
 "assembled_body(assemble a p ix)=assembled_body(assemble a q ix)"
 by (simp add: assemble_def)
lemma carrier_condition_locality:
 assumes same: "\<And>k. carrier_at a p (comparison_role r)(ix k)=carrier_at a p (comparison_role r)(jx k)"
 shows "comparison_condition ch (carrier_at a p (comparison_role r)(ix False))(carrier_at a p (comparison_role r)(ix True))
  \<longleftrightarrow> comparison_condition ch (carrier_at a p (comparison_role r)(jx False))(carrier_at a p (comparison_role r)(jx True))"
 by (simp only: same)
lemma no_distribution_without_communication:
 "(\<And>m. \<not>communication_couples p m x y) \<Longrightarrow> \<not>observer_condition p Distributed x y"
 by simp
lemma physical_identity_does_not_merge_roles:
 "i\<noteq>j \<Longrightarrow> role_at a r i\<noteq>role_at a r j"
 by (simp add: role_at_def role_instance_eq_iff_index_eq)

lemma domain_has_role_and_selected_index:
 "x\<in>role_domain a r \<Longrightarrow>
  ri_role x=role_of_realization r \<and> ri_zeta x\<in>selected_indices a \<and> ri_role x\<noteq>Body"
 by (auto simp: role_domain_def role_at_def role_instance_def realization_role_not_body)
lemma role_component_retains_scene_type:
 "valid_carrier_input a \<Longrightarrow> z\<in>selected_indices a \<Longrightarrow>
  ri_component(role_at a r z)\<in>local_carrier a(scene_at a z)r"
 by (auto simp: valid_carrier_input_def role_at_def role_instance_def)
lemma bool_two_positions: "UNIV = {False,True}"
 by auto
ML \<open>
val roots = @{thms realization_domain_exact role_index_preserved body_pair_distinct body_abstraction_retained carrier_condition_from_specified_values role_typed_combination body_independent_of_realization carrier_condition_locality no_distribution_without_communication physical_identity_does_not_merge_roles};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = if null (Thm_Deps.all_oracles @{thms comparison_inl comparison_inr domain_has_role_and_selected_index role_component_retains_scene_type bool_two_positions}) then () else error "Unexpected helper oracle dependency";
\<close>
end
