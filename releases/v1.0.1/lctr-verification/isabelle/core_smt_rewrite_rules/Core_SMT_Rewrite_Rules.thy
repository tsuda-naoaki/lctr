theory Core_SMT_Rewrite_Rules
  imports Main
begin

lemma arith_elim_gt: "((t::int) > s) = (~ (s >= t))" by presburger
lemma arith_elim_leq: "((t::int) <= s) = (s >= t)" by simp
lemma arith_elim_lt: "((t::int) < s) = (~ (t >= s))" by presburger
lemma arith_eq_elim_int: "((t::int) = s) = (t >= s & t <= s)" by auto
lemma arith_geq_ite_lift:
  "((if c then (t::int) else s) >= r) = (if c then t >= r else s >= r)"
  by (cases c) simp_all
lemma arith_geq_norm1_int: "((t::int) >= s) = (t - s >= 0)" by presburger
lemma arith_geq_tighten: "(~ ((t::int) >= s)) = (s >= t + 1)" by presburger
lemma arith_leq_ite_lift:
  "((if c then (t::int) else s) <= r) = (if c then t <= r else s <= r)"
  by (cases c) simp_all
lemma arith_leq_norm: "((t::int) <= s) = (~ (t >= s + 1))" by presburger
lemma bool_double_not_elim: "(~ (~ t)) = t" by simp
lemma bool_eq_true: "(t = True) = t" by simp
lemma bool_impl_false1: "(t --> False) = (~ t)" by simp
lemma eq_refl: "(t = t) = True" by simp
lemma eq_symm: "(t = s) = (s = t)" by auto
lemma ite_eq:
  "(if c then ((if c then x else y) = x) else ((if c then x else y) = y)) = True"
  by (cases c) simp_all
lemma ite_not_cond: "(if ~ c then x else y) = (if c then y else x)"
  by (cases c) simp_all
lemma ite_then_true: "(if c then True else x) = (c | x)" by (cases c) simp_all

lemma reject_non_strict_tighten: "~ ((~ ((0::int) >= 0)) = ((0::int) >= 0))" by simp
lemma reject_swapped_ite_eq:
  "~ (if True then ((if True then (0::int) else 1) = 1)
     else ((if True then (0::int) else 1) = 0))" by simp

ML \<open>
  val roots = @{thms arith_elim_gt arith_elim_leq arith_elim_lt arith_eq_elim_int
    arith_geq_ite_lift arith_geq_norm1_int arith_geq_tighten arith_leq_ite_lift
    arith_leq_norm bool_double_not_elim bool_eq_true bool_impl_false1 eq_refl
    eq_symm ite_eq ite_not_cond ite_then_true reject_non_strict_tighten reject_swapped_ite_eq};
  if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
