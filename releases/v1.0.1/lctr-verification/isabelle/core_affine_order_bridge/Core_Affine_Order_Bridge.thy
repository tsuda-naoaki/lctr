theory Core_Affine_Order_Bridge
  imports LCTR_Core_Affine_Realization.Core_Affine_Realization
begin
context affine_realization
begin
lemma difference_nonnegative_closure:
  assumes a: "a\<in>P" and b: "b\<in>P"
  shows "(lt a b \<or> a=b) = (0\<le>diff b a)"
  using strict_sign[OF a b] difference_zero_iff[OF a b]
  by (auto simp: le_less)
end
ML \<open>
val roots = @{thms affine_realization.difference_nonnegative_closure};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
