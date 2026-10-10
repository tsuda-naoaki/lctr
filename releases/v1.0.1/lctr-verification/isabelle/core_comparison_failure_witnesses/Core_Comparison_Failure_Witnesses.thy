theory Core_Comparison_Failure_Witnesses
 imports "LCTR_Core_Comparison_Stage.Core_Comparison_Stage"
         "LCTR_Core_Pair_Transport_Factorization.Core_Pair_Transport_Factorization"
begin

lemma unique_failure_cases:
 "(\<not>(\<exists>!a. P a)) \<longleftrightarrow>
  (\<not>(\<exists>a. P a)) \<or> (\<exists>a b. P a \<and> P b \<and> a\<noteq>b)"
 by blast

lemma source_collision:
 "(\<not>(\<forall>i. \<forall>a\<in>f i ` D i. \<exists>!s. s\<in>D i \<and> f i s=a)) \<longleftrightarrow>
  (\<exists>i x y. x\<in>D i \<and> y\<in>D i \<and> x\<noteq>y \<and> f i x=f i y)"
 by (simp only: l1_iff_injective) (auto simp: inj_on_def)

lemma factorization_failure:
 "(\<not>(\<exists>!p. factorization_valid I X Y R p)) \<longleftrightarrow>
  (\<not>(\<exists>p. factorization_valid I X Y R p))"
 using existence_unique_iff by blast

lemma set_equality_failure:
 "B\<noteq>C \<longleftrightarrow> (\<exists>a. (a\<in>B \<and> a\<notin>C) \<or> (a\<in>C \<and> a\<notin>B))"
 by blast

context native_comparison
begin

abbreviation witness_action where
 "witness_action \<equiv> typed_actions.action (regions D f) {e. admitted adm e}
   initial terminal (cmp_act D f tr)"

lemma unrealizable_witness:
 "(\<not>realizable s) \<longleftrightarrow>
  (\<exists>a\<in>specified s. \<not>(\<exists>b. loop_action s a b))"
 unfolding realizable_def by blast

lemma unrealizable_no_realization:
 "\<not>realizable s \<Longrightarrow>
  \<not>(\<exists>g. (\<forall>a\<in>specified s. g a\<in>regions D f (base s)) \<and>
   (\<forall>a\<in>specified s. loop_action s a (g a)))"
 using realizable_iff_total_realization by blast

lemma specified_nonfixed:
 "realizable s \<Longrightarrow>
  ((\<not>id_on_specified s) \<longleftrightarrow> (\<exists>a\<in>specified s. realize s a\<noteq>a))"
 using specified_identity_iff by blast

lemma mixed_nonfixed:
 "(\<not>irreducible_mixed_identity) \<longleftrightarrow>
  (\<exists>u es. irreducible u u es \<and> \<not>source_only es \<and> \<not>transport_only es \<and>
   (\<exists>a b. witness_action u es u a b \<and> a\<noteq>b))"
 unfolding irreducible_mixed_identity_def by blast

lemma pure_nonfixed:
 "(\<not>pure_loop_identity) \<longleftrightarrow>
  (\<exists>u es. transport_only es \<and> (\<exists>a b. witness_action u es u a b \<and> a\<noteq>b))"
 unfolding pure_loop_identity_def by blast

end

context paired_comparison
begin

lemma pullback_mismatch:
 "(\<not>stage_L5 localRel sourceRel) \<longleftrightarrow>
  (\<exists>p\<in>synchronized. \<not>(snd p\<in>localRel(fst p) \<longleftrightarrow>
   (recovery DC fC (fst p) (fst(snd p)), recovery DD fD (fst p) (snd(snd p)))\<in>sourceRel))"
 unfolding stage_L5_def by blast

lemma unsaturated_witness:
 "(\<not>saturated localRel) \<longleftrightarrow>
  (\<exists>p\<in>synchronized. \<exists>q\<in>synchronized. same p q \<and>
   \<not>(snd p\<in>localRel(fst p) \<longleftrightarrow> snd q\<in>localRel(fst q)))"
 unfolding saturated_def by blast

lemma unsaturated_no_pullback:
 "\<not>saturated localRel \<Longrightarrow>
  \<not>(\<exists>target. \<forall>p\<in>synchronized.
    projection p\<in>target \<longleftrightarrow> snd p\<in>localRel(fst p))"
 using saturation_necessary_for_pullback by blast

end

ML \<open>
val roots = @{thms unique_failure_cases source_collision factorization_failure
 native_comparison.unrealizable_witness native_comparison.unrealizable_no_realization
 native_comparison.specified_nonfixed set_equality_failure paired_comparison.pullback_mismatch
 paired_comparison.unsaturated_witness paired_comparison.unsaturated_no_pullback
 native_comparison.mixed_nonfixed native_comparison.pure_nonfixed};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>

end
