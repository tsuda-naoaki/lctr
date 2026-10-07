theory Core_Raw_Comparison_Entry
 imports "LCTR_Core_Configuration_Comparison.Core_Configuration_Comparison"
begin

lemma guarded_step_iff: "(P \<and> (P \<longrightarrow> Q)) \<longleftrightarrow> P \<and> Q"
 by blast

context configuration_comparison_seed
begin
abbreviation raw_trC where "raw_trC u v a b \<equiv> component(joint u v) False (Inl a)(Inl b)"
abbreviation raw_trD where "raw_trD u v a b \<equiv> component(joint u v) True (Inr a)(Inr b)"
abbreviation residual_seven where
 "residual_seven cs ds \<equiv>
 paired_comparison.stage_L3 DC fC raw_trC adm DD fD raw_trD adm cs ds \<and>
 paired_comparison.stage_L4 DC fC raw_trC adm DD fD raw_trD adm cs ds \<and>
 paired_comparison.stage_L5 DC fC DD fD localRel sourceRel \<and>
 paired_comparison.saturated DC fC raw_trC adm DD fD raw_trD adm localRel \<and>
 native_comparison.irreducible_mixed_identity DC fC raw_trC adm \<and>
 native_comparison.irreducible_mixed_identity DD fD raw_trD adm"
abbreviation raw_G where
 "raw_G \<equiv> native_comparison.pure_loop_identity DC fC raw_trC adm \<and>
 native_comparison.pure_loop_identity DD fD raw_trD adm"
definition full_stage_seven where
 "full_stage_seven cs ds \<longleftrightarrow> L1 \<and> L2 \<and> residual_seven cs ds"
definition guarded_G where
 "guarded_G cs ds \<longleftrightarrow> (full_stage_seven cs ds \<longrightarrow> raw_G)"
definition raw_operative where
 "raw_operative cs ds \<longleftrightarrow> full_stage_seven cs ds \<and> guarded_G cs ds"

lemma full_master_condition:
 "raw_operative cs ds \<longleftrightarrow> full_stage_seven cs ds \<and> guarded_G cs ds"
 by (rule raw_operative_def)

lemma operative_iff_residual:
 "raw_operative cs ds \<longleftrightarrow> L1 \<and> L2 \<and>
 paired_comparison.residual_operative DC fC raw_trC adm DD fD raw_trD adm cs ds localRel sourceRel"
proof -
 have entry: "L1 \<Longrightarrow> L2 \<Longrightarrow>
 (paired_comparison.residual_operative DC fC raw_trC adm DD fD raw_trD adm cs ds localRel sourceRel
 \<longleftrightarrow> residual_seven cs ds \<and> raw_G)"
 proof -
  assume h1: L1 and h2: L2
  interpret c: configuration_comparison raw src adm joint
   by unfold_locales (use valid admissible_nodes h1 h2 in auto)
  have tc: "c.trC = raw_trC" by (intro ext) (simp only: c.trC_def)
  have td: "c.trD = raw_trD" by (intro ext) (simp only: c.trD_def)
  show ?thesis
   using c.pair.residual_operative_def[of cs ds localRel sourceRel]
   by (simp only: tc td; blast)
 qed
 show ?thesis
  unfolding raw_operative_def guarded_G_def full_stage_seven_def using entry by blast
qed

lemma failed_entry_blocks:
 "\<not>L1 \<or> \<not>L2 \<Longrightarrow> \<not>raw_operative cs ds"
 by (auto simp: raw_operative_def full_stage_seven_def)

lemma guardedG_before_entry:
 "\<not>full_stage_seven cs ds \<Longrightarrow> guarded_G cs ds"
 by (simp add: guarded_G_def)

lemma full_conditions_generate:
 assumes h: "raw_operative cs ds"
 shows "L1 \<and> L2 \<and> (\<exists>!out.
 paired_comparison.valid_output DC fC raw_trC adm DD fD raw_trD adm cs ds localRel out)"
proof -
 have h1: L1 and h2: L2 using h operative_iff_residual by blast+
 interpret c: configuration_comparison raw src adm joint
  by unfold_locales (use valid admissible_nodes h1 h2 in auto)
 have tc: "c.trC = raw_trC" by (intro ext) (simp only: c.trC_def)
 have td: "c.trD = raw_trD" by (intro ext) (simp only: c.trD_def)
 have residual: "c.pair.residual_operative cs ds localRel sourceRel"
  using h operative_iff_residual[of cs ds] by (simp only: tc td; blast)
 have out: "\<exists>!out. c.pair.valid_output cs ds localRel out"
  by (rule c.pair.unique_generated_output[OF residual])
 show ?thesis using h1 h2 out by (simp only: tc td; blast)
qed

lemma entered_residual:
 "raw_operative cs ds \<Longrightarrow> L1 \<Longrightarrow> L2 \<Longrightarrow>
 paired_comparison.residual_operative DC fC raw_trC adm DD fD raw_trD adm cs ds localRel sourceRel"
 using operative_iff_residual by blast
end

ML \<open>
val roots = @{thms guarded_step_iff configuration_comparison_seed.full_master_condition
 configuration_comparison_seed.operative_iff_residual
 configuration_comparison_seed.failed_entry_blocks
 configuration_comparison_seed.guardedG_before_entry
 configuration_comparison_seed.full_conditions_generate
 configuration_comparison_seed.entered_residual};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
