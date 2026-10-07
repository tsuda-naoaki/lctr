theory Core_Affine_Frequency
  imports Main
begin

record 'q count_window =
  count_start :: nat
  count_end :: nat
  lower :: 'q
  upper :: 'q

definition admissible where
  "admissible r x = (count_start x < count_end x \<and> r (lower x) (upper x))"
definition count_difference :: "'q count_window \<Rightarrow> 'k::linordered_field" where
  "count_difference x = of_nat (count_end x - count_start x)"

lemma count_difference_positive:
  "admissible r x \<Longrightarrow> 0 < (count_difference x :: 'k::linordered_field)"
  by (simp add: admissible_def count_difference_def)

definition hz_number :: "'k::linordered_field \<Rightarrow> 'k \<Rightarrow> 'k" where
  "hz_number value unit = value / unit"
definition hz_unit :: "'k::linordered_field \<Rightarrow> nat \<Rightarrow> 'k" where
  "hz_unit standard n = standard / of_nat n"

lemma hz_number_positive:
  "0 < value \<Longrightarrow> 0 < unit \<Longrightarrow> 0 < hz_number value unit"
  by (simp add: hz_number_def)

lemma standard_normalization:
  assumes standard: "0 < standard" and count: "0 < n"
  shows "0 < hz_unit standard n \<and> hz_number standard (hz_unit standard n) = of_nat n"
  using assms by (simp add: hz_unit_def hz_number_def)

locale affine_frequency =
  fixes act :: "'p::linorder \<Rightarrow> 'k::linordered_field \<Rightarrow> 'p"
    and diff :: "'p \<Rightarrow> 'p \<Rightarrow> 'k"
  assumes zero_action: "act a 0 = a"
    and diff_spec: "act a z = b \<longleftrightarrow> z = diff b a"
    and strict_sign: "a < b \<longleftrightarrow> 0 < diff b a"
begin

lemma difference_reflexive: "diff a a = 0"
  using zero_action diff_spec by metis

lemma difference_zero_iff: "diff b a = 0 \<longleftrightarrow> a=b"
  using zero_action diff_spec difference_reflexive by metis

lemma difference_nonnegative: "a \<le> b \<longleftrightarrow> 0 \<le> diff b a"
  using strict_sign[of a b] difference_zero_iff[of b a]
  by (auto simp: le_less)

definition coordinate_difference where
  "coordinate_difference rho x = diff (rho (upper x)) (rho (lower x))"
definition frequency where
  "frequency rho x = count_difference x / coordinate_difference rho x"
definition period where
  "period rho x = inverse (frequency rho x)"

lemma coordinate_difference_positive:
  assumes strict: "\<And>a b. r a b \<longleftrightarrow> rho a < rho b"
    and window: "admissible r x"
  shows "0 < coordinate_difference rho x"
  using window strict strict_sign
  unfolding admissible_def coordinate_difference_def by blast

lemma frequency_positive:
  assumes strict: "\<And>a b. r a b \<longleftrightarrow> rho a < rho b"
    and window: "admissible r x"
  shows "0 < frequency rho x"
  unfolding frequency_def
  by (rule divide_pos_pos[OF count_difference_positive[OF window]
    coordinate_difference_positive[OF strict window]])

lemma period_positive_and_product:
  assumes strict: "\<And>a b. r a b \<longleftrightarrow> rho a < rho b"
    and window: "admissible r x"
  shows "0 < period rho x \<and> frequency rho x * period rho x = 1"
  using frequency_positive[OF strict window] by (simp add: period_def)

lemma window_constant_value_unique:
  assumes nonempty: "W \<noteq> {}"
    and valid_windows: "\<And>x. x \<in> W \<Longrightarrow> admissible r x"
    and invariant: "\<And>x y. x \<in> W \<Longrightarrow> y \<in> W \<Longrightarrow> frequency rho x = frequency rho y"
  shows "\<exists>!value. \<forall>x\<in>W. frequency rho x = value"
proof -
  obtain x where x: "x\<in>W" using nonempty by blast
  show ?thesis
  proof (rule ex1I[of _ "frequency rho x"])
    show "\<forall>y\<in>W. frequency rho y = frequency rho x" using invariant x by blast
    fix nu
    assume "\<forall>y\<in>W. frequency rho y = nu"
    then show "nu = frequency rho x" using x by simp
  qed
qed

lemma period_window_invariance:
  "admissible r x \<Longrightarrow> admissible r y \<Longrightarrow>
    frequency rho x = frequency rho y \<Longrightarrow> period rho x = period rho y"
  by (simp add: period_def)

end

lemma zero_count_invalidates_product:
  "(0 / d) * inverse (0 / d) \<noteq> (1 :: 'k::linordered_field)"
  by simp

ML \<open>
val roots = @{thms affine_frequency.difference_reflexive
  affine_frequency.difference_zero_iff affine_frequency.difference_nonnegative
  count_difference_positive affine_frequency.coordinate_difference_positive
  affine_frequency.frequency_positive affine_frequency.period_positive_and_product
  affine_frequency.window_constant_value_unique affine_frequency.period_window_invariance
  hz_number_positive standard_normalization
  zero_count_invalidates_product};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int (length roots));
val _ = Export.export @{theory} (Path.binding0 (Path.basic "root-propositions.txt"))
  [XML.Text (cat_lines (map (fn th =>
    Pretty.pure_string_of (Syntax.pretty_term @{context} (Thm.prop_of th)) ^ "\n") roots))];
\<close>
end
