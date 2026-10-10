theory Core_Representation_Failure_Stages
 imports LCTR_Core_Representation_Stages.Core_Representation_Stages
 LCTR_Core_Representation_Failure.Core_Representation_Failure
begin

context representation_base
begin
definition local_condition where "local_condition \<longleftrightarrow> first \<and> (\<forall>i. inc_trans_on(L i)clt)"
definition global_condition where "global_condition \<longleftrightarrow> first \<and> inc_trans_on C clt"
theorem local_condition_exact: "local_condition \<longleftrightarrow> second"
 by (simp add: local_condition_def second_def)
theorem global_condition_exact: "second \<Longrightarrow> (global_condition \<longleftrightarrow> third)"
 by (simp add: global_condition_def second_def third_def)
theorem local_condition_on_formed_input: "first \<Longrightarrow> (local_condition \<longleftrightarrow> (\<forall>i. inc_trans_on(L i)clt))"
 by (simp add: local_condition_def)
theorem global_condition_on_formed_input: "first \<Longrightarrow> (global_condition \<longleftrightarrow> inc_trans_on C clt)"
 by (simp add: global_condition_def)

definition repr_condition :: "token\<Rightarrow>bool" where
 "repr_condition t=(if fst t=1 then
  (if snd t=1 then first else if snd t=2 then local_condition else global_condition) else True)"
theorem condition_values:
 "(repr_condition(repr_token 1) \<longleftrightarrow> first) \<and>
  (repr_condition(repr_token 2) \<longleftrightarrow> local_condition) \<and>
  (repr_condition(repr_token 3) \<longleftrightarrow> global_condition)"
 by (simp add: repr_condition_def repr_token_def)
lemma repr_indices_three: "repr_indices={1,2,3}"
 by (auto simp: repr_indices_def)

sublocale N: native_representation "\<lambda>x::unit. True" "\<lambda>x t. True" "\<lambda>x t. True" "\<lambda>x. repr_condition"
 by unfold_locales (simp_all add: repr_condition_def cmp_token_def)

theorem generated_stage_one: "repr_generated repr_condition 1 \<longleftrightarrow> first"
 by (simp add: repr_generated_def repr_indices_three repr_condition_def repr_token_def)
theorem generated_stage_two: "repr_generated repr_condition 2 \<longleftrightarrow> second"
 by (simp add: repr_generated_def repr_indices_three repr_condition_def repr_token_def local_condition_def second_def)
theorem generated_stage_three: "repr_generated repr_condition 3 \<longleftrightarrow> third"
 by (auto simp: repr_generated_def repr_indices_three repr_condition_def repr_token_def
  local_condition_def global_condition_def second_def third_def)

theorem native_stage_failure_one: "()\<in>N.region 1 \<longleftrightarrow> \<not>first"
 using N.native_generation_boundary[where x="()" and i=1]
 by (simp add: repr_indices_three repr_generated_def repr_condition_def repr_token_def)
theorem native_stage_failure_two: "()\<in>N.region 2 \<longleftrightarrow> first \<and> \<not>second"
 using N.native_generation_boundary[where x="()" and i=2]
 by (auto simp: repr_indices_three repr_generated_def repr_condition_def repr_token_def local_condition_def second_def)
theorem native_stage_failure_three: "()\<in>N.region 3 \<longleftrightarrow> second \<and> \<not>third"
 using N.native_generation_boundary[where x="()" and i=3]
 by (simp add: repr_indices_three generated_stage_two generated_stage_three)
theorem native_failure_domain: "()\<in>N.failure_domain \<longleftrightarrow> \<not>third"
 by (auto simp: N.failure_domain_def repr_indices_three repr_condition_def repr_token_def
  local_condition_def global_condition_def second_def third_def)
theorem native_failure_signature:
 assumes h: "\<not>third"
 shows "(\<exists>!i. i\<in>repr_indices \<and> (\<forall>j\<in>repr_indices. N.signature () j=N.basis i j)) \<and>
  sum(N.signature ())repr_indices=1"
 by (rule N.signature_one_hot) (use h native_failure_domain in simp)
theorem native_second_failure_witness:
 "first \<Longrightarrow> (()\<in>N.region 2 \<longleftrightarrow> (\<exists>i. \<not>inc_trans_on(L i)clt))"
 by (simp add: native_stage_failure_two second_def)
theorem native_third_failure_witness:
 "second \<Longrightarrow> (()\<in>N.region 3 \<longleftrightarrow> \<not>inc_trans_on C clt)"
 by (simp add: native_stage_failure_three third_def)
theorem native_second_failure_triple:
 "first \<Longrightarrow> (()\<in>N.region 2 \<longleftrightarrow>
  (\<exists>i. \<exists>x\<in>L i. \<exists>y\<in>L i. \<exists>z\<in>L i.
    inc_on(L i)clt x y \<and> inc_on(L i)clt y z \<and> \<not>inc_on(L i)clt x z))"
 by (simp add: native_second_failure_witness inc_trans_on_def)
theorem native_third_failure_triple:
 "second \<Longrightarrow> (()\<in>N.region 3 \<longleftrightarrow>
  (\<exists>x\<in>C. \<exists>y\<in>C. \<exists>z\<in>C.
    inc_on C clt x y \<and> inc_on C clt y z \<and> \<not>inc_on C clt x z))"
 by (simp add: native_third_failure_witness inc_trans_on_def)
theorem native_first_failure_four_points:
 "()\<in>N.region 1 \<longleftrightarrow>
  (\<exists>a\<in>native_carrier D f. \<exists>a'\<in>native_carrier D f.
   \<exists>b\<in>native_carrier D f. \<exists>b'\<in>native_carrier D f.
   (a,a')\<in>native_equiv D f tr adm \<and> (b,b')\<in>native_equiv D f tr adm \<and>
   \<not>(pullback recover_tag r a b \<longleftrightarrow> pullback recover_tag r a' b'))"
 by (simp only: native_stage_failure_one first_def ord_desc_def) blast
end

ML \<open>
val roots = @{thms representation_base.local_condition_exact representation_base.global_condition_exact
 representation_base.local_condition_on_formed_input representation_base.global_condition_on_formed_input
 representation_base.condition_values representation_base.generated_stage_one representation_base.generated_stage_two
 representation_base.generated_stage_three representation_base.native_stage_failure_one
 representation_base.native_stage_failure_two representation_base.native_stage_failure_three
 representation_base.native_failure_domain representation_base.native_failure_signature
 representation_base.native_second_failure_witness representation_base.native_third_failure_witness
 representation_base.native_second_failure_triple representation_base.native_third_failure_triple
 representation_base.native_first_failure_four_points};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
