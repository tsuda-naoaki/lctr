theory Core_Source_Recovery
 imports Main
begin
type_synonym 's clock_token = "'s \<times> nat"
definition within_le where "within_le (k::nat) l \<longleftrightarrow> k\<le>l"
definition family_le where
 "family_le (x::'s clock_token)y \<longleftrightarrow> fst x=fst y \<and> snd x\<le>snd y"
record 'a detector_token =
 token_identity :: 'a
 token_sequence :: nat
definition detector_le where
 "detector_le x y \<longleftrightarrow> x=y \<or> token_sequence x<token_sequence y"
record ('t,'a) partial_arrival =
 arrival_domain :: "'t set"
 arrival_value :: "'t \<Rightarrow> 'a"
definition unique_recoverable where
 "unique_recoverable A a \<longleftrightarrow>
  (\<exists>x\<in>arrival_domain A. arrival_value A x=a) \<and>
  (\<forall>x\<in>arrival_domain A. \<forall>y\<in>arrival_domain A.
    arrival_value A x=a \<longrightarrow> arrival_value A y=a \<longrightarrow> x=y)"
definition recovered where
 "recovered A a=(THE x. x\<in>arrival_domain A \<and> arrival_value A x=a)"
lemma singleton_fiber_recovery:
 "unique_recoverable A a \<Longrightarrow> \<exists>!x. x\<in>arrival_domain A \<and> arrival_value A x=a"
 by (auto simp: unique_recoverable_def)
lemma recovered_spec:
 assumes u: "unique_recoverable A a"
 shows "recovered A a\<in>arrival_domain A \<and> arrival_value A (recovered A a)=a"
 unfolding recovered_def by (rule theI') (rule singleton_fiber_recovery[OF u])
lemma recover_eq_original:
 assumes x: "x\<in>arrival_domain A" and u: "unique_recoverable A (arrival_value A x)"
 shows "recovered A (arrival_value A x)=x"
 using recovered_spec[OF u] u x unfolding unique_recoverable_def by blast
lemma unique_tagged_representation: "\<exists>!p::'s clock_token. p=x"
 by simp
lemma c_within_source_partial_order:
 "(\<forall>k. within_le k k) \<and>
  (\<forall>a b c. within_le a b \<longrightarrow> within_le b c \<longrightarrow> within_le a c) \<and>
  (\<forall>a b. within_le a b \<longrightarrow> within_le b a \<longrightarrow> a=b)"
 by (auto simp: within_le_def)
lemma fixed_source_order_correspondence:
 "family_le(j,k)(j,l) \<longleftrightarrow> within_le k l"
 by (simp add: family_le_def within_le_def)
lemma equal_display_does_not_identify_tokens:
 "(j,k)\<noteq>(j',l) \<Longrightarrow> display(j,k)=display(j',l) \<Longrightarrow> (j,k)\<noteq>(j',l)"
 by simp
lemma d_partial_order:
 "(\<forall>x::'a detector_token. detector_le x x) \<and>
  (\<forall>x y z::'a detector_token. detector_le x y \<longrightarrow> detector_le y z \<longrightarrow> detector_le x z) \<and>
  (\<forall>x y::'a detector_token. detector_le x y \<longrightarrow> detector_le y x \<longrightarrow> x=y)"
 by (auto simp: detector_le_def)
lemma d_equal_index_incomparable:
 "x\<noteq>y \<Longrightarrow> token_sequence x=token_sequence y \<Longrightarrow>
  \<not>detector_le x y \<and> \<not>detector_le y x"
 by (auto simp: detector_le_def)
lemma record_cells_partition_criterion:
 assumes "\<And>x. finite(W x)" "\<And>x. W x\<noteq>{}" "\<And>x. x\<in>W x"
  "\<And>x y. y\<in>W x \<longleftrightarrow> W y=W x"
 shows "(\<forall>x. x\<in>W x) \<and> (\<forall>x. W x\<noteq>{}) \<and>
  (\<forall>x y z. z\<in>W x \<longrightarrow> z\<in>W y \<longrightarrow> W x=W y)"
proof (intro conjI allI impI)
 fix x show "x\<in>W x" by (rule assms(3))
next
 fix x show "W x\<noteq>{}" by (rule assms(2))
next
 fix x y z assume zx: "z\<in>W x" and zy: "z\<in>W y"
 show "W x=W y" using assms(4)[where x=x and y=z] assms(4)[where x=y and y=z] zx zy by simp
qed
lemma c_family_partial_order:
 "(\<forall>x::'s clock_token. family_le x x) \<and>
  (\<forall>x y z::'s clock_token. family_le x y \<longrightarrow> family_le y z \<longrightarrow> family_le x z) \<and>
  (\<forall>x y::'s clock_token. family_le x y \<longrightarrow> family_le y x \<longrightarrow> x=y)"
 by (auto simp: family_le_def prod_eq_iff)
lemma c_distinct_sources_incomparable:
 "fst x\<noteq>fst y \<Longrightarrow> \<not>family_le x y \<and> \<not>family_le y x"
 by (auto simp: family_le_def)
lemma fiber_eq_singleton_recovery:
 assumes u: "unique_recoverable A a"
 shows "{x\<in>arrival_domain A. arrival_value A x=a}={recovered A a}"
 using recovered_spec[OF u] u unfolding unique_recoverable_def by blast
lemma c_recovery_preserves_source_index:
 "x\<in>arrival_domain A \<Longrightarrow> unique_recoverable A(arrival_value A x) \<Longrightarrow>
  fst(recovered A(arrival_value A x))=fst x"
 by (simp add: recover_eq_original)
record ('p,'v) body_token =
 object_position :: 'p
 body_payload :: 'v
lemma b_recovery_preserves_object_position:
 "x\<in>arrival_domain A \<Longrightarrow> unique_recoverable A(arrival_value A x) \<Longrightarrow>
  object_position(recovered A(arrival_value A x))=object_position x"
 by (simp add: recover_eq_original)

lemma positive_c_distinct_sources_same_nat:
 "(False,7::nat)\<noteq>(True,7::nat)" by simp
definition constant_display :: "bool clock_token \<Rightarrow> unit" where
 "constant_display x=()"
lemma positive_constant_display_preserves_token_identity:
 "(False,1::nat)\<noteq>(True,1::nat)" by simp
definition d0 where "d0=\<lparr>token_identity=False,token_sequence=5\<rparr>"
definition d1 where "d1=\<lparr>token_identity=True,token_sequence=5\<rparr>"
lemma positive_d_distinct_tokens_same_seq: "d0\<noteq>d1"
 by (simp add: d0_def d1_def)
lemma positive_d_equal_seq_incomparable: "\<not>detector_le d0 d1 \<and> \<not>detector_le d1 d0"
 by (simp add: detector_le_def d0_def d1_def)
definition empty_arrival :: "(nat,unit) partial_arrival" where
 "empty_arrival=\<lparr>arrival_domain={},arrival_value=(\<lambda>_. ())\<rparr>"
lemma positive_empty_arrival_domain_allowed:
 "\<not>(\<exists>x\<in>arrival_domain empty_arrival. True)"
 by (simp add: empty_arrival_def)
definition two_source_one_arrival :: "(bool,unit) partial_arrival" where
 "two_source_one_arrival=\<lparr>arrival_domain=UNIV,arrival_value=(\<lambda>_. ())\<rparr>"
lemma two_source_one_arrival_not_uniquely_recoverable:
 "\<not>unique_recoverable two_source_one_arrival ()"
 by (simp add: unique_recoverable_def two_source_one_arrival_def;
  rule exI[where x=False]; rule exI[where x=True]; simp)
fun overlapping_cells where
 "overlapping_cells False={False,True}" | "overlapping_cells True={True}"
lemma missing_class_condition_allows_overlap:
 "(\<forall>x. x\<in>overlapping_cells x) \<and>
  (\<forall>x. overlapping_cells x\<noteq>{}) \<and>
  (\<exists>x y z. z\<in>overlapping_cells x \<and> z\<in>overlapping_cells y \<and>
    overlapping_cells x\<noteq>overlapping_cells y)"
proof -
 have self: "\<forall>x. x\<in>overlapping_cells x" by (rule allI, case_tac x) simp_all
 have nonempty: "\<forall>x. overlapping_cells x\<noteq>{}" by (rule allI, case_tac x) simp_all
 have witness: "True\<in>overlapping_cells False \<and> True\<in>overlapping_cells True \<and>
  overlapping_cells False\<noteq>overlapping_cells True" by simp
 show ?thesis using self nonempty witness by blast
qed
lemma empty_arrival_has_no_recoverable_value:
 "\<forall>a. \<not>unique_recoverable empty_arrival a"
 by (simp add: empty_arrival_def unique_recoverable_def)

ML \<open>
val roots = @{thms unique_tagged_representation c_within_source_partial_order fixed_source_order_correspondence equal_display_does_not_identify_tokens d_partial_order d_equal_index_incomparable record_cells_partition_criterion c_family_partial_order c_distinct_sources_incomparable singleton_fiber_recovery fiber_eq_singleton_recovery c_recovery_preserves_source_index b_recovery_preserves_object_position positive_c_distinct_sources_same_nat positive_constant_display_preserves_token_identity positive_d_distinct_tokens_same_seq positive_d_equal_seq_incomparable positive_empty_arrival_domain_allowed two_source_one_arrival_not_uniquely_recoverable missing_class_condition_allows_overlap empty_arrival_has_no_recoverable_value};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = if null (Thm_Deps.all_oracles @{thms recovered_spec recover_eq_original}) then () else error "Unexpected helper oracle dependency";
\<close>
end
