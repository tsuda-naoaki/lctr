theory Core_Pair_Input_Bridge
 imports "LCTR_Core_Configuration_Comparison.Core_Configuration_Comparison"
begin

definition carrier_typed where
 "carrier_typed A B R = (\<forall>x y. R x y \<longrightarrow> x\<in>A \<and> y\<in>B)"
definition extend_relation where
 "extend_relation A B r x y = (x\<in>A \<and> y\<in>B \<and> r x y)"
definition restrict_relation where
 "restrict_relation A B R x y = (x\<in>A \<and> y\<in>B \<and> R x y)"

lemma joint_input_typed: "carrier_typed A B (extend_relation A B r)"
 by (simp add: carrier_typed_def extend_relation_def)
lemma joint_input_roundtrip:
 "x\<in>A \<Longrightarrow> y\<in>B \<Longrightarrow>
 restrict_relation A B (extend_relation A B r) x y = r x y"
 by (simp add: restrict_relation_def extend_relation_def)
lemma restriction_exact:
 "extend_relation A B (restrict_relation A B R) x y = (x\<in>A \<and> y\<in>B \<and> R x y)"
 by (auto simp: extend_relation_def restrict_relation_def)
lemma restriction_identity_iff:
 "(\<forall>x y. extend_relation A B (restrict_relation A B R) x y = R x y) = carrier_typed A B R"
 by (auto simp: restriction_exact carrier_typed_def)
lemma empty_source_image_excludes_joint: "\<not>extend_relation {} B r x y"
 by (simp add: extend_relation_def)
lemma empty_target_image_excludes_joint: "\<not>extend_relation A {} r x y"
 by (simp add: extend_relation_def)
lemma missing_carrier_control:
 "\<not>carrier_typed {False} (UNIV::unit set) (\<lambda>_ _. True)"
proof
 assume h: "carrier_typed {False} (UNIV::unit set) (\<lambda>_ _. True)"
 have "True\<in>{False}" using h unfolding carrier_typed_def by blast
 then show False by simp
qed

definition native_joint where
 "native_joint Xi Xj R = extend_relation (PiE UNIV Xi) (PiE UNIV Xj) R"
lemma native_joint_carrier:
 "carrier_typed (PiE UNIV Xi) (PiE UNIV Xj) (native_joint Xi Xj R)"
 by (simp add: native_joint_def joint_input_typed)

locale exact_configuration_comparison_seed = configuration_comparison_seed raw src adm joint
 for raw :: "('z,'s,'t,'l,'c,'d,'o,'m,'v,'rc,'rd,'rb)raw_input"
 and src :: "('cs,'dt,'bt,'cl,'dl,'z,'v,'rc,'rd,'rb)source_data"
 and adm :: "'v\<Rightarrow>'v\<Rightarrow>bool"
 and joint :: "'v\<Rightarrow>'v\<Rightarrow>(bool\<Rightarrow>('rc+'rd))\<Rightarrow>(bool\<Rightarrow>('rc+'rd))\<Rightarrow>bool" +
 assumes joint_carrier: "adm i j \<Longrightarrow> carrier_typed (PiE UNIV (images i)) (PiE UNIV (images j)) (joint i j)"

ML \<open>
val roots = @{thms joint_input_typed joint_input_roundtrip restriction_exact restriction_identity_iff
 empty_source_image_excludes_joint empty_target_image_excludes_joint missing_carrier_control native_joint_carrier};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
