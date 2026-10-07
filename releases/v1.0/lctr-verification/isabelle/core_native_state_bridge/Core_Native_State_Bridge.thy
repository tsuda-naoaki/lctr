theory Core_Native_State_Bridge
  imports LCTR_Core_Native_Specification.Core_Native_Specification
begin

definition native_specs where "native_specs E L t = spec_carrier (kind t) E L"
definition native_res where "native_res x y i = restriction (kind y) i"

lemma native_predecessors_typed:
  "argument_edges edges (native_specs E L) native_res \<subseteq>
    (Sigma tokens (native_specs E L)) \<times> (Sigma tokens (native_specs E L))"
proof (rule argument_edges_typed[OF edges_typed])
  fix x y i
  assume xy: "(y,x)\<in>edges" and i: "i\<in>native_specs E L x"
  have k: "kind y\<longrightarrow>kind x" using xy edge_kind by blast
  show "native_res x y i\<in>native_specs E L y"
    using k i by (cases "kind x"; cases "kind y")
      (auto simp: native_res_def native_specs_def spec_carrier_def restriction_def)
qed

lemma native_lift_agrees:
  assumes rec: "s=eval_update (argument_edges edges (native_specs E L) native_res) f e c s"
  shows "(\<lambda>x. if x\<in>Sigma tokens (native_specs E L) then Some (s x) else None) =
    native_eval_update (Sigma tokens (native_specs E L))
      (argument_edges edges (native_specs E L) native_res) f e c
      (\<lambda>x. if x\<in>Sigma tokens (native_specs E L) then Some (s x) else None)"
  by (rule native_lift_recursion[OF rec native_predecessors_typed])

lemma canonical_recursion_unique:
  "\<exists>!s. s = native_eval_update (Sigma tokens (native_specs E L))
    (argument_edges edges (native_specs E L) native_res) f e c s"
  by (rule concrete_native_argument_unique)

lemma gate_and_state_cases:
  "((f\<and>e) = (f\<and>e)) \<and> ((f\<and>p) = (f\<and>p)) \<and>
   ((p\<and>(f\<and>e)) = (p\<and>f\<and>e)) \<and>
   (local_state f e p c=Unformed \<longleftrightarrow> \<not>(f\<and>p)) \<and>
   (local_state f e p c=Unevaluable \<longleftrightarrow> (f\<and>p)\<and>\<not>e) \<and>
   (local_state f e p c=Sat \<longleftrightarrow> (p\<and>(f\<and>e))\<and>c) \<and>
   (local_state f e p c=Failed \<longleftrightarrow> (p\<and>(f\<and>e))\<and>\<not>c)"
  by (auto simp: local_state_def)

lemma state_section_recursion:
  assumes rec: "s = eval_update (argument_edges edges (native_specs E L) native_res) f e c s"
    and ev: "ev\<in>E" and l: "l\<in>L"
  shows "(\<lambda>t. s (arg_at ev l t)) = eval_update edges
    (\<lambda>t. f (arg_at ev l t)) (\<lambda>t. e (arg_at ev l t))
    (\<lambda>t. c (arg_at ev l t)) (\<lambda>t. s (arg_at ev l t))"
proof -
  have typed: "\<And>t. spec_at (kind t) ev l\<in>native_specs E L t"
    using ev l by (auto simp: native_specs_def spec_carrier_def spec_at_def)
  have coh: "\<And>x y. (y,x)\<in>edges \<Longrightarrow>
      native_res x y (spec_at (kind x) ev l)=spec_at (kind y) ev l"
    unfolding native_res_def by (rule restriction_coherent) (use edge_kind in blast)
  note result = coherent_section_recursion[OF rec typed coh]
  show ?thesis using result by (simp add: arg_at_def)
qed

definition strict_arg where "strict_arg ev t = (t,Inl ev)"
lemma strict_argument_recovery:
  "\<not>kind t \<Longrightarrow> arg_at ev l t = strict_arg ev t"
  by (simp add: arg_at_def strict_arg_def spec_at_def)
lemma strict_state_scale_independent:
  "\<not>kind t \<Longrightarrow> s (arg_at ev l t)=s (arg_at ev m t)"
  by (simp add: strict_argument_recovery)

definition strict_failed where
  "strict_failed s ev = {t\<in>tokens. \<not>kind t \<and> s (strict_arg ev t)=Some Failed}"
lemma strict_failed_typed:
  "strict_failed s ev \<subseteq> {t\<in>tokens. \<not>kind t}"
  by (auto simp: strict_failed_def)
lemma strict_failed_recovery:
  "strict_failed s ev = {t\<in>tokens. s (arg_at ev l t)=Some Failed} \<inter> {t\<in>tokens. \<not>kind t}"
  by (auto simp: strict_failed_def strict_argument_recovery)
lemma strict_failed_scale_independent:
  "{t\<in>tokens. s (arg_at ev l t)=Some Failed} \<inter> {t\<in>tokens. \<not>kind t} =
   {t\<in>tokens. s (arg_at ev m t)=Some Failed} \<inter> {t\<in>tokens. \<not>kind t}"
  by (simp only: strict_failed_recovery[symmetric])

lemma missing_input_unformed: "local_state False e p c=Unformed"
  by (simp add: local_state_def)
lemma off_domain_not_failed:
  assumes rec: "s=eval_update G f e c s"
    and typed: "\<And>x. f x \<Longrightarrow> e x \<Longrightarrow> (\<forall>y. (y,x)\<in>G \<longrightarrow> s y=Sat) \<Longrightarrow> D x"
    and outside: "\<not>D x"
  shows "s x\<noteq>Failed"
proof
  assume failed: "s x=Failed"
  have domain: "D x"
  proof (rule failed_requires_native_domain[OF rec _ failed])
    fix y
    assume fy: "f y" and ey: "e y" and prior: "\<forall>z. (z,y)\<in>G \<longrightarrow> s z=Sat"
    show "D y" by (rule typed[OF fy ey prior])
  qed
  show False using outside domain by contradiction
qed

ML \<open>
val roots = @{thms canonical_recursion_unique gate_and_state_cases state_section_recursion
  strict_argument_recovery strict_state_scale_independent strict_failed_typed strict_failed_recovery
  strict_failed_scale_independent missing_input_unformed off_domain_not_failed};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
