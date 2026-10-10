theory Core_Comparison_Definition_Interfaces
  imports "LCTR_Core_Comparison_Scope.Core_Comparison_Scope"
begin

definition indicator :: "bool \<Rightarrow> nat" where "indicator P = (if P then 1 else 0)"
definition member_indicator where "member_indicator A x = indicator (x\<in>A)"
lemma indicator_true: "P \<Longrightarrow> indicator P = 1" by (simp add: indicator_def)
lemma indicator_false: "\<not>P \<Longrightarrow> indicator P = 0" by (simp add: indicator_def)
lemma membership_indicator: "member_indicator A x = indicator (x\<in>A)"
  by (simp add: member_indicator_def)

definition input_ready :: "token\<Rightarrow>bool" where "input_ready t = True"
definition raw where "raw local gluing t =
  (if fst t=0 \<and> snd t\<in>cmp_indices then condition local gluing (snd t) else True)"
lemma raw_exact:
  "i\<in>cmp_indices \<Longrightarrow> raw local gluing (cmp_token i) = condition local gluing i"
  by (simp add: raw_def cmp_token_def)
lemma raw_local:
  "i\<in>{1..7::nat} \<Longrightarrow> raw local gluing (cmp_token i) = local i"
  by (simp add: raw_def cmp_token_def cmp_indices_def condition_def)
lemma raw_gluing: "raw local gluing (cmp_token 8) = gluing"
  by (simp add: raw_def cmp_token_def cmp_indices_def condition_def)
lemma readiness: "input_ready (cmp_token i) \<and> input_ready (cmp_token i)"
  by (simp add: input_ready_def)
lemma first_prefix_empty: "prefix (raw local gluing) 1"
  by (simp add: prefix_def cmp_indices_def)

lemma failed_exact:
  assumes i: "i\<in>cmp_indices"
  shows "(run input_ready input_ready (raw local gluing) 40 (cmp_token i)=Failed) =
    (prefix (raw local gluing) i \<and> \<not>condition local gluing i)"
proof -
  interpret N: native_comparison input_ready input_ready "raw local gluing"
    by standard (simp add: input_ready_def)
  show ?thesis using N.R.comparison_failed_prefix[OF i] raw_exact[OF i]
    by (simp add: first_def)
qed
lemma failed_token_membership:
  "i\<in>cmp_indices \<Longrightarrow>
   (cmp_token i\<in>failed_set (run input_ready input_ready (raw local gluing) 40)) =
   (prefix (raw local gluing) i \<and> \<not>condition local gluing i)"
  by (simp add: failed_set_def cmp_typed failed_exact)
lemma failure_domain_partition:
  "(\<not>operative local gluing) =
   (\<exists>!i. i\<in>cmp_indices \<and> run input_ready input_ready (raw local gluing) 40 (cmp_token i)=Failed)"
  by (rule native_first_failure_unique) (simp add: input_ready_def, rule raw_exact, assumption)
lemma signature_indicator:
  assumes i: "i\<in>cmp_indices"
  shows "native_comparison.signature input_ready input_ready (raw local gluing) i =
   member_indicator (failed_set (run input_ready input_ready (raw local gluing) 40)) (cmp_token i)"
proof -
  interpret N: native_comparison input_ready input_ready "raw local gluing"
    by standard (simp add: input_ready_def)
  show ?thesis using i
    by (simp add: N.signature_def member_indicator_def indicator_def failed_set_def cmp_typed)
qed
lemma signature_binary:
  "(if s (cmp_token i)=Failed then 1 else 0::nat)=0 \<or>
   (if s (cmp_token i)=Failed then 1 else 0::nat)=1"
  by simp

ML \<open>
val roots = @{thms indicator_true indicator_false membership_indicator raw_exact raw_local raw_gluing
  readiness first_prefix_empty failed_exact failed_token_membership failure_domain_partition
  signature_indicator signature_binary};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
