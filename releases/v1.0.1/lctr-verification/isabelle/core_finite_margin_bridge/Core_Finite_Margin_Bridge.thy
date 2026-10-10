theory Core_Finite_Margin_Bridge
  imports LCTR_Core_Continuum_Encoding.Core_Continuum_Encoding
begin

lemma arith_elim_gt: "((t::real) > s) = (~ (s >= t))" by (simp only: not_le)
lemma arith_elim_leq: "((t::real) <= s) = (s >= t)" by simp
lemma arith_elim_lt: "((t::real) < s) = (~ (t >= s))" by (simp only: not_le)
lemma arith_eq_elim_real: "((t::real) = s) = (t >= s & t <= s)" by auto

lemma finite_margin: "margin (ereal a) (ereal b) = ereal (a-b)"
  by (simp add: margin_def)
lemma finite_excess:
  "excess (ereal a) (ereal b) = ereal (if a-b<0 then -(a-b) else 0)"
  unfolding excess_def using finite_margin[of a b]
  by (cases "a-b<0") (simp_all add: max_def)
lemma bool_defect_real: "real_of_ereal (bool_defect b) = (if b then 0 else 1)"
  by (cases b) (simp_all add: bool_defect_def)
lemma half_real: "real_of_ereal half = (1/2::real)" by (simp add: half_def)

lemma reject_reverse_margin: "~ (((0::real)-1 >= 0) = ((0::real)<=1))" by simp
lemma reject_zero_threshold_robust:
  "~ (((0::real) - (if True then 0 else 1) > 0) = True)" by simp
lemma reject_unit_threshold:
  "~ (((if False then (0::real) else 1) <= 1) = False)" by simp

ML \<open>
val roots = @{thms arith_elim_gt arith_elim_leq arith_elim_lt arith_eq_elim_real
  finite_margin finite_excess bool_defect_real half_real reject_reverse_margin
  reject_zero_threshold_robust reject_unit_threshold};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
