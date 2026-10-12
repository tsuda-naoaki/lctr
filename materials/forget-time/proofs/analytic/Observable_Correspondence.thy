theory Observable_Correspondence
  imports "HOL-Probability.Conditional_Expectation"
begin

theorem separating_observables:
  assumes sep: "\<And>x y. x\<in>V \<Longrightarrow> y\<in>V \<Longrightarrow>
      (\<forall>f\<in>A. f x = f y) \<Longrightarrow> x=y"
    and x: "x\<in>V" and y: "y\<in>V"
  shows "(\<forall>f\<in>A. f x = f y) \<longleftrightarrow> x=y"
  using sep[OF x y] by auto

theorem all_selection_correspondence:
  fixes f g :: "'a \<Rightarrow> real"
  assumes fm[measurable]: "integrable M f" and gm[measurable]: "integrable M g"
  shows "(\<forall>A\<in>sets M. (\<integral>x\<in>A. f x \<partial>M) = (\<integral>x\<in>A. g x \<partial>M))
      \<longleftrightarrow> (AE x in M. f x=g x)"
proof
  assume h: "\<forall>A\<in>sets M. (\<integral>x\<in>A. f x \<partial>M) = (\<integral>x\<in>A. g x \<partial>M)"
  show "AE x in M. f x=g x"
    by (rule density_unique_real[OF fm gm]) (use h in auto)
next
  assume h: "AE x in M. f x=g x"
  show "\<forall>A\<in>sets M. (\<integral>x\<in>A. f x \<partial>M) = (\<integral>x\<in>A. g x \<partial>M)"
  proof (intro ballI)
    fix A assume A[measurable]: "A\<in>sets M"
    show "(\<integral>x\<in>A. f x \<partial>M) = (\<integral>x\<in>A. g x \<partial>M)"
      unfolding set_lebesgue_integral_def
      apply (rule Bochner_Integration.integral_cong_AE)
        apply measurable
       apply measurable
      using h by eventually_elim simp
  qed
qed

context sigma_finite_subalgebra
begin

theorem restricted_selection_correspondence:
  fixes d :: "'a \<Rightarrow> real"
  assumes dint: "integrable M d"
  shows "(\<forall>A\<in>sets F. (\<integral>x\<in>A. d x \<partial>M)=0)
    \<longleftrightarrow> (AE x in M. real_cond_exp M F d x=0)"
proof
  assume h: "\<forall>A\<in>sets F. (\<integral>x\<in>A. d x \<partial>M)=0"
  show "AE x in M. real_cond_exp M F d x=0"
    by (rule real_cond_exp_charact[where g="\<lambda>_.0", OF _ dint]) (use h in auto)
next
  assume h: "AE x in M. real_cond_exp M F d x=0"
  show "\<forall>A\<in>sets F. (\<integral>x\<in>A. d x \<partial>M)=0"
  proof (intro ballI)
    fix A assume A[measurable]: "A\<in>sets F"
    have Am[measurable]: "A\<in>sets M"
      using A subalg by (auto simp: subalgebra_def)
    have cm[measurable]: "real_cond_exp M F d \<in> borel_measurable M"
      by (rule borel_measurable_cond_exp2)
    have im[measurable]: "(indicator A :: 'a\<Rightarrow>real) \<in> borel_measurable M"
      using Am by measurable
    have "(\<integral>x\<in>A. d x \<partial>M) = (\<integral>x\<in>A. real_cond_exp M F d x \<partial>M)"
      by (rule real_cond_exp_intA[OF dint A])
    also have "... = (\<integral>x\<in>A. (0::real) \<partial>M)"
      unfolding set_lebesgue_integral_def
      apply (rule Bochner_Integration.integral_cong_AE)
        apply (rule borel_measurable_scaleR[OF im cm])
       apply (simp only: scaleR_zero_right)
       apply measurable
      using h by eventually_elim simp
    finally show "(\<integral>x\<in>A. d x \<partial>M)=0" by simp
  qed
qed

end

end
