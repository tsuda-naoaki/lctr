theory Core_Failure_Multiplicity
  imports LCTR_Core_First_Failure_Report.Core_First_Failure_Report
begin

definition boundary_support where
  "boundary_support V b = {i\<in>approximation_indices. \<exists>l. least_outside V l \<and> b l i}"
definition signature_support where
  "signature_support b = {i\<in>approximation_indices. b i}"
definition masked_signature where
  "masked_signature b l i = (i\<in>approximation_indices \<and> b l i)"

lemma least_outside_unique:
  "least_outside V a \<Longrightarrow> least_outside V l \<Longrightarrow> a=l"
  by (auto simp: least_outside_def intro: antisym)

lemma support_at_boundary:
  assumes least: "least_outside V l"
  shows "boundary_support V b=signature_support (b l)"
proof (rule set_eqI)
  fix i
  show "(i\<in>boundary_support V b)=(i\<in>signature_support (b l))"
  proof
    assume h: "i\<in>boundary_support V b"
    then obtain a where ii: "i\<in>approximation_indices"
      and ha: "least_outside V a" and bi: "b a i"
      by (auto simp: boundary_support_def)
    have eq: "a=l" by (rule least_outside_unique[OF ha least])
    show "i\<in>signature_support (b l)" using ii bi eq
      by (simp add: signature_support_def)
  next
    assume h: "i\<in>signature_support (b l)"
    have witness: "\<exists>a. least_outside V a \<and> b a i"
      by (rule exI[of _ l]) (use h least in \<open>simp add: signature_support_def\<close>)
    show "i\<in>boundary_support V b" using h witness
      by (simp add: signature_support_def boundary_support_def)
  qed
qed

lemma no_boundary_no_support:
  "\<not>(\<exists>l. least_outside V l) \<Longrightarrow> boundary_support V b={}"
  by (auto simp: boundary_support_def)

lemma support_card_bound: "card (boundary_support V b)\<le>9"
proof -
  have finite: "finite approximation_indices" by (simp add: approximation_indices_def)
  have sub: "boundary_support V b\<subseteq>approximation_indices"
    by (auto simp: boundary_support_def)
  have "card (boundary_support V b)\<le>card approximation_indices"
    by (rule card_mono[OF finite sub])
  then show ?thesis by (simp add: approximation_indices_def)
qed

datatype boundary_class = BoundaryAbsent | BoundaryUnique | BoundaryParallel
definition classify :: "nat\<Rightarrow>boundary_class" where
  "classify n = (if n=0 then BoundaryAbsent else if n=1 then BoundaryUnique else BoundaryParallel)"
definition boundary_case where "boundary_case V b=classify (card (boundary_support V b))"

lemma classification_exact:
  "(classify n=BoundaryAbsent) = (n=0) \<and>
   (classify n=BoundaryUnique) = (n=1) \<and>
   (classify n=BoundaryParallel) = (2\<le>n)"
  by (auto simp: classify_def split: if_splits)

lemma finite_boundary_support: "finite (boundary_support V b)"
  by (simp add: boundary_support_def approximation_indices_def)

lemma absent_exact:
  "(boundary_case V b=BoundaryAbsent) =
    (boundary_data V (masked_signature b)\<subseteq>UNIV\<times>{\<lambda>_. False})"
proof -
  have class_eq: "(boundary_case V b=BoundaryAbsent) = (boundary_support V b={})"
    using classification_exact[of "card (boundary_support V b)"] finite_boundary_support[of V b]
    by (simp add: boundary_case_def)
  have empty: "(boundary_support V b={}) =
    (boundary_data V (masked_signature b)\<subseteq>UNIV\<times>{\<lambda>_. False})"
  proof
    assume no: "boundary_support V b={}"
    show "boundary_data V (masked_signature b)\<subseteq>UNIV\<times>{\<lambda>_. False}"
    proof
      fix p assume p: "p\<in>boundary_data V (masked_signature b)"
      have zero: "snd p=(\<lambda>_. False)"
      proof (rule ext)
        fix i
        show "snd p i=False"
          using p no by (auto simp: boundary_data_def boundary_support_def masked_signature_def)
      qed
      show "p\<in>UNIV\<times>{\<lambda>_. False}" using zero by (cases p) simp
    qed
  next
    assume sub: "boundary_data V (masked_signature b)\<subseteq>UNIV\<times>{\<lambda>_. False}"
    show "boundary_support V b={}"
    proof (rule equals0I)
      fix i assume i: "i\<in>boundary_support V b"
      then obtain l where ii: "i\<in>approximation_indices"
        and least: "least_outside V l" and bi: "b l i"
        by (auto simp: boundary_support_def)
      have mem: "(l,masked_signature b l)\<in>boundary_data V (masked_signature b)"
        using least by (simp add: boundary_data_def)
      have zero: "masked_signature b l=(\<lambda>_. False)"
        using subsetD[OF sub mem] by simp
      have at: "masked_signature b l i=False" using fun_cong[OF zero, of i] by simp
      show False using at ii bi by (simp add: masked_signature_def)
    qed
  qed
  show ?thesis using class_eq empty by simp
qed

lemma unique_exact:
  "(boundary_case V b=BoundaryUnique) = (card (boundary_support V b)=1)"
  using classification_exact[of "card (boundary_support V b)"] by (simp add: boundary_case_def)

lemma parallel_exact:
  "(boundary_case V b=BoundaryParallel) = (2\<le>card (boundary_support V b))"
  using classification_exact[of "card (boundary_support V b)"] by (simp add: boundary_case_def)

lemma classified_nonzero_has_boundary:
  assumes nonzero: "boundary_case V b\<noteq>BoundaryAbsent"
  shows "\<exists>l. least_outside V l"
proof (rule ccontr)
  assume no: "\<not>(\<exists>l. least_outside V l)"
  have "boundary_support V b={}" by (rule no_boundary_no_support[OF no])
  then show False using nonzero by (simp add: boundary_case_def classify_def)
qed

lemma parallel_boundary_card:
  assumes par: "boundary_case V b=BoundaryParallel"
  shows "\<exists>l. least_outside V l \<and> 2\<le>card (signature_support (b l))"
proof -
  have nonzero: "boundary_case V b\<noteq>BoundaryAbsent" using par by simp
  obtain l where least: "least_outside V l"
    using classified_nonzero_has_boundary[OF nonzero] by blast
  have card: "2\<le>card (signature_support (b l))"
    using par parallel_exact[of V b] support_at_boundary[OF least, of b] by simp
  show ?thesis using least card by blast
qed

lemma quantitative_signature_support:
  "signature_support (excess_signature d e)=exceeded approximation_indices d e"
  by (auto simp: signature_support_def excess_signature_def exceeded_def)

lemma quantitative_parallel_at_boundary:
  assumes least: "least_outside {x. valid approximation_indices (d x) e} l"
    and par: "boundary_case {x. valid approximation_indices (d x) e}
      (\<lambda>x. excess_signature (d x) e)=BoundaryParallel"
  shows "2\<le>card (signature_support (excess_signature (d l) e))"
  using parallel_exact[of "{x. valid approximation_indices (d x) e}" "\<lambda>x. excess_signature (d x) e"]
    support_at_boundary[OF least, of "\<lambda>x. excess_signature (d x) e"] par by simp

definition multiplicity_report where
  "multiplicity_report s V b = (structural_case s,boundary_case V b)"

lemma multiplicity_components:
  "fst (multiplicity_report s V b)=
    (if card (failed_set s)=0 then NoFailure else if card (failed_set s)=1 then SingleFailure else ParallelFailure)
    \<and> snd (multiplicity_report s V b)=classify (card (boundary_support V b))"
  by (simp add: multiplicity_report_def structural_case_def boundary_case_def)

lemma multiplicity_depends_on_two_cardinalities:
  "card (failed_set s)=card (failed_set t) \<Longrightarrow>
    card (boundary_support V b)=card (boundary_support W c) \<Longrightarrow>
    multiplicity_report s V b=multiplicity_report t W c"
  by (simp add: multiplicity_report_def structural_case_def boundary_case_def)

lemma parallel_structural_card:
  "fst (multiplicity_report s V b)=ParallelFailure \<Longrightarrow> 2\<le>card (failed_set s)"
  by (simp add: multiplicity_report_def parallel_structural_positions)

lemma present_zero_boundary_is_absent:
  "boundary_data {x::nat. x<1} (\<lambda>_. (\<lambda>i::nat. False))\<noteq>{} \<and>
    boundary_case {x::nat. x<1} (\<lambda>_. (\<lambda>i::nat. False))=BoundaryAbsent"
proof
  show "boundary_data {x::nat. x<1} (\<lambda>_. (\<lambda>i::nat. False))\<noteq>{}"
    by (simp only: boundary_presence_different_from_zero_signature) simp
  show "boundary_case {x::nat. x<1} (\<lambda>_. (\<lambda>i::nat. False))=BoundaryAbsent"
    by (simp add: boundary_case_def boundary_support_def classify_def)
qed

ML \<open>
val roots = @{thms support_at_boundary no_boundary_no_support support_card_bound classification_exact
  absent_exact unique_exact parallel_exact classified_nonzero_has_boundary parallel_boundary_card
  quantitative_signature_support quantitative_parallel_at_boundary multiplicity_components
  multiplicity_depends_on_two_cardinalities parallel_structural_card present_zero_boundary_is_absent};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
