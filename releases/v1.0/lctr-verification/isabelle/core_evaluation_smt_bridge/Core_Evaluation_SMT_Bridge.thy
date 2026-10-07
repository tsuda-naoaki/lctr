theory Core_Evaluation_SMT_Bridge
  imports LCTR_Core_Evaluation.Core_Evaluation
begin

fun encode :: "eval_state => int" where
  "encode Unformed = 0" | "encode Unevaluable = 1" | "encode Sat = 2" | "encode Failed = 3"
definition smt_state where
  "smt_state f e p c = (if ~ (f & p) then (0::int) else if ~ e then 1 else if c then 2 else 3)"
definition wrong_prior_state where
  "wrong_prior_state f e c = (if ~ f then Unformed else if ~ e then Unevaluable else if c then Sat else Failed)"
definition wrong_prior_code where
  "wrong_prior_code f e c = (if ~ f then (0::int) else if ~ e then 1 else if c then 2 else 3)"
definition wrong_order_state where
  "wrong_order_state f e p c = (if ~ e then Unevaluable else if ~ (f & p) then Unformed else if c then Sat else Failed)"
definition wrong_order_code where
  "wrong_order_code f e p c = (if ~ e then (1::int) else if ~ (f & p) then 0 else if c then 2 else 3)"

lemma encode_injective: "inj encode"
  by (rule injI) (case_tac x; case_tac y; simp)
lemma encode_eq_iff: "(encode x = encode y) = (x = y)"
  using encode_injective by (simp add: inj_eq)
lemma encode_image: "(EX s. encode s = n) = (n = 0 | n = 1 | n = 2 | n = 3)"
proof
  assume "EX s. encode s = n"
  then obtain s where "encode s = n" by blast
  then show "n = 0 | n = 1 | n = 2 | n = 3" by (cases s) auto
next
  assume "n = 0 | n = 1 | n = 2 | n = 3"
  then show "EX s. encode s = n" by (metis encode.simps)
qed
lemma state_commutes: "encode (local_state f e p c) = smt_state f e p c"
  unfolding local_state_def smt_state_def by (auto split: if_splits)

lemma failed_iff_transfer:
  "((local_state f e p c = Failed) = (f & e & p & ~ c)) =
   ((smt_state f e p c = 3) = (f & e & p & ~ c))"
  using encode_eq_iff[of "local_state f e p c" Failed] state_commutes by auto
lemma sat_iff_transfer:
  "((local_state f e p c = Sat) = (f & e & p & c)) =
   ((smt_state f e p c = 2) = (f & e & p & c))"
  using encode_eq_iff[of "local_state f e p c" Sat] state_commutes by auto
lemma missing_formation_transfer:
  "(~ f --> local_state f e p c = Unformed) = (~ f --> smt_state f e p c = 0)"
  unfolding local_state_def smt_state_def by auto
lemma upstream_nonsat_transfer:
  "(~ p --> local_state f e p c = Unformed) = (~ p --> smt_state f e p c = 0)"
  unfolding local_state_def smt_state_def by auto
lemma unevaluable_iff_transfer:
  "((local_state f e p c = Unevaluable) = (f & p & ~ e)) =
   ((smt_state f e p c = 1) = (f & p & ~ e))"
  unfolding local_state_def smt_state_def by auto
lemma unformed_iff_transfer:
  "((local_state f e p c = Unformed) = (~ (f & p))) =
   ((smt_state f e p c = 0) = (~ (f & p)))"
  unfolding local_state_def smt_state_def by auto
lemma wrong_prior_transfer:
  "(local_state f e p c = wrong_prior_state f e c) = (smt_state f e p c = wrong_prior_code f e c)"
  unfolding local_state_def smt_state_def wrong_prior_state_def wrong_prior_code_def
  by (auto split: if_splits)
lemma wrong_order_transfer:
  "(local_state f e p c = wrong_order_state f e p c) = (smt_state f e p c = wrong_order_code f e p c)"
  unfolding local_state_def smt_state_def wrong_order_state_def wrong_order_code_def
  by (auto split: if_splits)
lemma reject_ignored_predecessor:
  "local_state True True False False ~= wrong_prior_state True True False"
  by (simp add: local_state_def wrong_prior_state_def)
lemma reject_early_evaluation:
  "local_state False False True True ~= wrong_order_state False False True True"
  by (simp add: local_state_def wrong_order_state_def)

ML \<open>
  val roots = @{thms encode_injective encode_eq_iff encode_image state_commutes
    failed_iff_transfer sat_iff_transfer missing_formation_transfer upstream_nonsat_transfer
    unevaluable_iff_transfer unformed_iff_transfer wrong_prior_transfer wrong_order_transfer
    reject_ignored_predecessor reject_early_evaluation};
  if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
