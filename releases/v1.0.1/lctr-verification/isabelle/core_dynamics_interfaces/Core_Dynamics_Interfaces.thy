theory Core_Dynamics_Interfaces
 imports "LCTR_Core_Operational_Configuration.Core_Operational_Configuration" "HOL-Library.FuncSet"
begin

definition quotient_roles where "quotient_roles={SClock,SBody}"
lemma quotient_role_membership: "r\<in>quotient_roles \<longleftrightarrow> r=SClock \<or> r=SBody"
 by (simp add: quotient_roles_def)

definition evaluations where "evaluations input={ev. fst ev=input}"
definition make_evaluation where "make_evaluation input observer object=(input,observer,object)"
lemma complete_eval_fields: "make_evaluation input observer object=(input,observer,object)"
 by (simp add: make_evaluation_def)
lemma complete_eval_roundtrip:
 "ev\<in>evaluations input \<Longrightarrow> make_evaluation input (fst(snd ev)) (snd(snd ev))=ev"
 by (cases ev) (auto simp: evaluations_def make_evaluation_def)
definition exact_evaluation where "exact_evaluation exact_input ev=exact_input(fst ev)"
lemma exact_eval_iff:
 "ev\<in>evaluations input \<Longrightarrow> exact_evaluation exact_input ev=exact_input input"
 by (simp add: evaluations_def exact_evaluation_def)

definition extended where "extended D P e=(\<exists>w\<in>D. e=w \<and> P w)"
lemma extended_bounded_identity: "extended D P e=(\<exists>w\<in>D. e=w \<and> P w)"
 by (simp only: extended_def)
lemma extended_on_domain: "e\<in>D \<Longrightarrow> extended D P e=P e"
 by (auto simp: extended_def)
lemma extended_outside_domain: "e\<notin>D \<Longrightarrow> \<not>extended D P e"
 by (auto simp: extended_def)

record ('r,'s,'v) reception_data =
 arrival_family :: "'r \<Rightarrow> ('s,'v) partial_arrival"
 local_relation :: "('r \<Rightarrow> 'v) set"
 source_tuple_relation :: "('r \<Rightarrow> 's) set"

definition actual_images where
 "actual_images arr r=image (arrival_value(arr r)) (arrival_domain(arr r))"
definition valid_reception where
 "valid_reception S V x =
  ((\<forall>r. arrival_domain(arrival_family x r)\<subseteq>S r \<and>
    actual_images (arrival_family x) r\<subseteq>V r) \<and>
   local_relation x\<subseteq>PiE UNIV (actual_images (arrival_family x)) \<and>
   source_tuple_relation x\<subseteq>PiE UNIV S)"

definition pack_reception where
 "pack_reception p =
  \<lparr>arrival_family=fst p,local_relation=fst(snd p),source_tuple_relation=snd(snd p)\<rparr>"
definition unpack_reception where
 "unpack_reception (x::('r,'s,'v)reception_data) =
  (arrival_family x,local_relation x,source_tuple_relation x)"

lemma reception_pack_roundtrip: "pack_reception(unpack_reception x)=x"
 by (simp add: pack_reception_def unpack_reception_def)
lemma reception_unpack_roundtrip: "unpack_reception(pack_reception p)=p"
 by (simp add: pack_reception_def unpack_reception_def)
lemma arrival_image_exact:
 "a\<in>actual_images arr r \<longleftrightarrow> (\<exists>t\<in>arrival_domain(arr r). arrival_value(arr r)t=a)"
 by (auto simp: actual_images_def)
lemma local_relation_typed:
 assumes valid: "valid_reception S V x" and inside: "a\<in>local_relation x"
 shows "\<forall>r. \<exists>t\<in>arrival_domain(arrival_family x r). arrival_value(arrival_family x r)t=a r"
proof (intro allI)
 fix r
 have inc: "local_relation x\<subseteq>PiE UNIV (actual_images (arrival_family x))"
  using valid by (simp add: valid_reception_def)
 have tuple: "a\<in>PiE UNIV (actual_images (arrival_family x))"
  by (rule subsetD[OF inc inside])
 have at_role: "a r\<in>actual_images (arrival_family x) r"
  using tuple by (auto simp: PiE_def Pi_def)
 show "\<exists>t\<in>arrival_domain(arrival_family x r). arrival_value(arrival_family x r)t=a r"
  using at_role by (simp only: arrival_image_exact)
qed
lemma source_relation_typed:
 "valid_reception S V x \<Longrightarrow> s\<in>source_tuple_relation x \<Longrightarrow> \<forall>r. s r\<in>S r"
 by (auto simp: valid_reception_def PiE_def Pi_def)

ML \<open>
val roots = @{thms quotient_role_membership complete_eval_fields complete_eval_roundtrip exact_eval_iff
 extended_bounded_identity extended_on_domain extended_outside_domain
 reception_pack_roundtrip reception_unpack_roundtrip arrival_image_exact local_relation_typed source_relation_typed};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
