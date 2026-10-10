theory Refinement_Ambiguity_Controls
  imports LCTR_Dynamics_Refinement_Alignment.Dynamics_Refinement_Alignment
begin

definition test_order :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  "test_order i x y = (if i then (\<not>x \<or> y) else x=y)"

interpretation P: presentations "UNIV::bool set" "UNIV::unit set"
  "\<lambda>_::bool. UNIV::bool set" "\<lambda>_::bool. UNIV::unit set"
  "\<lambda>_::bool. id::bool\<Rightarrow>bool" "\<lambda>_::bool. id::unit\<Rightarrow>unit"
  test_order "\<lambda>_::bool. {}"
  by unfold_locales auto

lemma test_orders_partial:
  "part_on UNIV (test_order False) \<and> part_on UNIV (test_order True)"
  unfolding part_on_def pre_on_def test_order_def by auto

lemma forward_arrow: "P.arrow False True id id"
  unfolding P.arrow_def test_order_def by auto

lemma bijective_forward:
  "bij_betw (id::bool\<Rightarrow>bool) UNIV UNIV \<and>
   bij_betw (id::unit\<Rightarrow>unit) UNIV UNIV"
  by simp

lemma no_reverse_arrow: "\<not>(\<exists>f g. P.arrow True False f g)"
proof
  assume "\<exists>f g. P.arrow True False f g"
  then obtain f g where a: "P.arrow True False f g" by blast
  have cf: "f False=False" and ct: "f True=True"
    using a unfolding P.arrow_def by auto
  have mono: "\<forall>x\<in>UNIV. \<forall>y\<in>UNIV.
    test_order True x y \<longrightarrow> test_order False (f x) (f y)"
    using a unfolding P.arrow_def by iprover
  have "test_order False (f False) (f True)"
    using mono[rule_format, of False True] by (simp add: test_order_def)
  then show False by (simp add: test_order_def cf ct)
qed

lemma no_structural_iso: "\<not>(\<exists>f g h l. P.structural_iso False True f g h l)"
proof
  assume "\<exists>f g h l. P.structural_iso False True f g h l"
  then obtain f g h l where h: "P.structural_iso False True f g h l" by blast
  have "P.arrow True False h l" by (rule P.structural_iso_backward[OF h])
  then show False using no_reverse_arrow by blast
qed

lemma both_admissible:
  "native_admissible UNIV UNIV Id Id Id {} (id::bool\<Rightarrow>bool) (id::unit\<Rightarrow>unit)
     {(x,y). test_order False x y} {} \<and>
   native_admissible UNIV UNIV Id Id Id {} (id::bool\<Rightarrow>bool) (id::unit\<Rightarrow>unit)
     {(x,y). test_order True x y} {}"
  unfolding native_admissible_def test_order_def by auto

lemma ambiguity_control:
  "P.arrow False True id id \<and>
   bij_betw (id::bool\<Rightarrow>bool) UNIV UNIV \<and>
   bij_betw (id::unit\<Rightarrow>unit) UNIV UNIV \<and>
   \<not>(\<exists>f g h l. P.structural_iso False True f g h l)"
  using forward_arrow bijective_forward no_structural_iso by simp

ML \<open>
val roots = @{thms test_orders_partial forward_arrow bijective_forward
  no_reverse_arrow no_structural_iso both_admissible ambiguity_control};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
