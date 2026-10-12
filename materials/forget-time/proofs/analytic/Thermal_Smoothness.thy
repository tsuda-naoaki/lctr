theory Thermal_Smoothness
  imports Thermal_Measure
begin

datatype real_expression = RConst real | RQ | RP
  | RAdd real_expression real_expression | RMul real_expression real_expression
  | RExp real_expression

fun evaluate :: "real_expression \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "evaluate (RConst c) q p=c"
| "evaluate RQ q p=q"
| "evaluate RP q p=p"
| "evaluate (RAdd a b) q p=evaluate a q p+evaluate b q p"
| "evaluate (RMul a b) q p=evaluate a q p*evaluate b q p"
| "evaluate (RExp a) q p=exp(evaluate a q p)"

fun differentiate :: "bool \<Rightarrow> real_expression \<Rightarrow> real_expression" where
  "differentiate b (RConst c)=RConst 0"
| "differentiate b RQ=RConst (if b then 1 else 0)"
| "differentiate b RP=RConst (if b then 0 else 1)"
| "differentiate b (RAdd x y)=RAdd (differentiate b x) (differentiate b y)"
| "differentiate b (RMul x y)=RAdd (RMul (differentiate b x) y) (RMul x (differentiate b y))"
| "differentiate b (RExp x)=RMul (RExp x) (differentiate b x)"

lemma evaluate_q_derivative:
  "DERIV (\<lambda>x. evaluate e x p) q :> evaluate (differentiate True e) q p"
  by (induction e) (auto intro!: derivative_eq_intros simp: algebra_simps)

lemma evaluate_p_derivative:
  "DERIV (evaluate e q) p :> evaluate (differentiate False e) q p"
  by (induction e) (auto intro!: derivative_eq_intros simp: algebra_simps)

lemma evaluate_continuous:
  "continuous_on UNIV (\<lambda>s. evaluate e (fst s) (snd s))"
  by (induction e) (auto intro!: continuous_intros)

definition partial :: "bool \<Rightarrow> (real \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "partial b f q p=(if b then deriv (\<lambda>x. f x p) q else deriv (f q) p)"

lemma partial_evaluate:
  "partial b (evaluate e)=evaluate(differentiate b e)"
  unfolding partial_def
  by (rule ext)+ (cases b; simp add: DERIV_imp_deriv[OF evaluate_q_derivative] DERIV_imp_deriv[OF evaluate_p_derivative])

fun mixed_partial :: "bool list \<Rightarrow> (real \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "mixed_partial [] f=f"
| "mixed_partial (b#bs) f=mixed_partial bs (partial b f)"

fun mixed_expression :: "bool list \<Rightarrow> real_expression \<Rightarrow> real_expression" where
  "mixed_expression [] e=e"
| "mixed_expression (b#bs) e=mixed_expression bs (differentiate b e)"

lemma mixed_partial_evaluate:
  "mixed_partial bs (evaluate e)=evaluate(mixed_expression bs e)"
  by (induction bs arbitrary: e) (simp_all add: partial_evaluate)

definition density_expression :: real_expression where
  "density_expression=RMul (RConst (1/pi))
    (RExp (RMul (RConst (-1)) (RMul (RExp (RMul (RConst 2) (RMul RQ RQ))) (RMul RP RP))))"

lemma density_evaluate:
  "evaluate density_expression=thermal_density"
  by (rule ext)+ (simp add: density_expression_def thermal_density_def power2_eq_square)

theorem density_all_mixed_derivatives:
  "continuous_on UNIV (\<lambda>s. mixed_partial bs thermal_density (fst s) (snd s))"
  "DERIV (\<lambda>x. mixed_partial bs thermal_density x p) q
    :> partial True (mixed_partial bs thermal_density) q p"
  "DERIV (mixed_partial bs thermal_density q) p
    :> partial False (mixed_partial bs thermal_density) q p"
  unfolding density_evaluate[symmetric] mixed_partial_evaluate partial_evaluate
  by (rule evaluate_continuous, rule evaluate_q_derivative, rule evaluate_p_derivative)

end
