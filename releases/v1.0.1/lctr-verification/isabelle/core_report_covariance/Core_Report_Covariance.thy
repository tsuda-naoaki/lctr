theory Core_Report_Covariance
  imports "../core_audit_report/Core_Audit_Report"
begin

definition function_map where "function_map c s = s \<circ> inv c"
definition state_map where
  "state_map c r = \<lparr>group_states=group_states r,
    condition_states=function_map c (condition_states r),
    indeterminate_tokens=c ` indeterminate_tokens r,
    indeterminate_signature=function_map c (indeterminate_signature r),
    undefined_reasons=Core_Audit_Tags.reason_map c ` undefined_reasons r\<rparr>"
definition diagnostic_map where
  "diagnostic_map c d b r = \<lparr>
    failed_position=Core_Audit_Tags.tagged_map (image c) c (failed_position r),
    failure_signature_value=Core_Audit_Tags.tagged_map (function_map c) c (failure_signature_value r),
    approximation_boundary=Core_Audit_Tags.tagged_map b c (approximation_boundary r),
    structural_burden=Core_Audit_Tags.tagged_map (map_prod (image d) (image d)) c (structural_burden r)\<rparr>"
definition report_map where
  "report_map data c d b r = \<lparr>report_data=data (report_data r),
    report_states=state_map c (report_states r),
    report_diagnostics=diagnostic_map c d b (report_diagnostics r)\<rparr>"

lemma function_transport:
  assumes bc: "bij c" and st: "\<And>a. t (c a)=s a"
  shows "function_map c s=t"
proof (rule ext)
  fix x
  have "t (c (inv c x))=s (inv c x)" by (rule st)
  then show "function_map c s x=t x"
    by (simp add: function_map_def surj_f_inv_f[OF bij_is_surj[OF bc]])
qed

lemma all_bij:
  "bij c \<Longrightarrow> (\<forall>y. P y) = (\<forall>x. P (c x))"
  using bij_is_surj unfolding surj_def by metis
lemma fiber_image:
  "bij c \<Longrightarrow> (\<And>a. t (c a)=s a) \<Longrightarrow> c ` {a. s a=q}={b. t b=q}"
  using bij_is_surj unfolding surj_def by force
lemma reason_image:
  assumes bc: "bij c" and st: "\<And>a. t (c a)=s a"
  shows "Core_Audit_Tags.reason_map c ` all_reasons s=all_reasons t"
proof -
  interpret T: Core_Audit_Tags.tag_transport UNIV UNIV UNIV UNIV c "inv c" id id
    by standard (auto simp: inv_f_f[OF bij_is_inj[OF bc]] surj_f_inv_f[OF bij_is_surj[OF bc]])
  show ?thesis unfolding all_reasons_def by (rule T.reasons_transport) (simp add: st)
qed
lemma local_reason_image:
  assumes bc: "bij c" and st: "\<And>a. t (c a)=s a"
  shows "Core_Audit_Tags.reason_map c ` local_reasons s G=local_reasons t (c ` G)"
proof -
  interpret T: Core_Audit_Tags.tag_transport UNIV UNIV UNIV UNIV c "inv c" id id
    by standard (auto simp: inv_f_f[OF bij_is_inj[OF bc]] surj_f_inv_f[OF bij_is_surj[OF bc]])
  show ?thesis unfolding local_reasons_def by (rule T.group_reasons_transport) (auto simp: st)
qed
lemma tagged_image:
  "Core_Audit_Tags.tagged_map v c (Core_Audit_Tags.tagged y R)=
    Core_Audit_Tags.tagged (v y) (Core_Audit_Tags.reason_map c ` R)"
  by (simp add: Core_Audit_Tags.tagged_map_def Core_Audit_Tags.tagged_def)

lemma group_values:
  "Core_Audit_State_Transport.priority ` (pair_input s ` Core_Audit_Groups.group_tokens i)=
    Core_Audit_State_Transport.priority ` (s ` {a. fst (Core_Structural_Burden.rep_token a)=i})"
proof -
  have eq: "Core_Structural_Burden.abs_token ` Core_Audit_Groups.group_tokens i =
    {a. fst (Core_Structural_Burden.rep_token a)=i}"
  proof (rule set_eqI, rule iffI)
    fix a assume "a\<in>Core_Structural_Burden.abs_token ` Core_Audit_Groups.group_tokens i"
    then obtain x where x: "x\<in>Core_Audit_Groups.group_tokens i" and a: "a=Core_Structural_Burden.abs_token x" by blast
    show "a\<in>{a. fst (Core_Structural_Burden.rep_token a)=i}"
      using x report_token_inverse by (auto simp: a Core_Audit_Groups.group_tokens_def)
  next
    fix a assume a: "a\<in>{a. fst (Core_Structural_Burden.rep_token a)=i}"
    have mem: "Core_Structural_Burden.rep_token a\<in>Core_Audit_Groups.group_tokens i"
      using a report_token_typed[of a] by (simp add: Core_Audit_Groups.group_tokens_def)
    show "a\<in>Core_Structural_Burden.abs_token ` Core_Audit_Groups.group_tokens i"
      using imageI[OF mem, where f=Core_Structural_Burden.abs_token]
      by (simp add: Core_Structural_Burden.rep_token_inverse)
  qed
  show ?thesis by (simp only: pair_input_def image_image eq[symmetric])
qed
lemma group_states_transport:
  assumes bc: "bij c"
    and series: "\<And>a. fst (Core_Structural_Burden.rep_token (c a))=fst (Core_Structural_Burden.rep_token a)"
    and st: "\<And>a. t (c a)=s a"
  shows "Core_Audit_Groups.group_status (pair_input t) i=Core_Audit_Groups.group_status (pair_input s) i"
proof -
  have gi: "c ` {a. fst (Core_Structural_Burden.rep_token a)=i}={a. fst (Core_Structural_Burden.rep_token a)=i}"
    by (rule fiber_image[where c=c and s="\<lambda>a. fst (Core_Structural_Burden.rep_token a)" and t="\<lambda>a. fst (Core_Structural_Burden.rep_token a)", OF bc series])
  have vals: "t ` {a. fst (Core_Structural_Burden.rep_token a)=i}=s ` {a. fst (Core_Structural_Burden.rep_token a)=i}"
  proof -
    have "t ` (c ` {a. fst (Core_Structural_Burden.rep_token a)=i})=s ` {a. fst (Core_Structural_Burden.rep_token a)=i}"
      by (simp only: image_image st)
    then show ?thesis by (simp only: gi)
  qed
  have gv: "Core_Audit_State_Transport.priority ` (pair_input t ` Core_Audit_Groups.group_tokens i)=
    Core_Audit_State_Transport.priority ` (pair_input s ` Core_Audit_Groups.group_tokens i)"
    by (simp only: group_values vals)
  show ?thesis using gv
    by (simp add: Core_Audit_Groups.group_status_def Core_Audit_Groups.group_priority_def image_image)
qed
lemma state_report_transport:
  assumes bc: "bij c"
    and series: "\<And>a. fst (Core_Structural_Burden.rep_token (c a))=fst (Core_Structural_Burden.rep_token a)"
    and st: "\<And>a. t (c a)=s a"
  shows "state_map c (state_report s)=state_report t"
proof -
  have gs: "\<And>i. Core_Audit_Groups.group_status (pair_input t) i=Core_Audit_Groups.group_status (pair_input s) i"
    by (rule group_states_transport[where c=c and s=s and t=t, OF bc series st])
  have cond: "function_map c s=t" by (rule function_transport[where c=c and s=s and t=t, OF bc st])
  have isig: "function_map c (\<lambda>a. s a=Core_Audit_State_Transport.Indeterminate)=(\<lambda>a. t a=Core_Audit_State_Transport.Indeterminate)"
    by (rule function_transport[OF bc]) (simp add: st)
  have itok: "c ` {a. s a=Core_Audit_State_Transport.Indeterminate}={a. t a=Core_Audit_State_Transport.Indeterminate}"
    by (rule fiber_image[where c=c and s=s and t=t, OF bc st])
  have rea: "Core_Audit_Tags.reason_map c ` all_reasons s=all_reasons t"
    by (rule reason_image[where c=c and s=s and t=t, OF bc st])
  show ?thesis by (simp add: state_map_def state_report_def gs cond isig itok rea)
qed

lemma approximation_group_image:
  "bij c \<Longrightarrow> (\<And>a. fst (Core_Structural_Burden.rep_token (c a))=fst (Core_Structural_Burden.rep_token a)) \<Longrightarrow>
    c ` approximation_group=approximation_group"
  unfolding approximation_group_def by (rule fiber_image)
lemma burden_report_transport:
  assumes bc: "bij c" and bd: "bij d"
    and edges: "\<And>a z. Core_Structural_Burden.edge a z=Core_Structural_Burden.edge (c a) (c z)"
    and targets: "\<And>a. d (Core_Structural_Burden.StructTok a)=Core_Structural_Burden.StructTok (c a)"
    and st: "\<And>a. t (c a)=s a"
  shows "map_prod (image d) (image d) (Core_Structural_Burden.report (failed s) roots)=
    Core_Structural_Burden.report (failed t) (map_option (image c) roots)"
proof -
  have ff: "c ` failed s=failed t" unfolding failed_def
    by (rule fiber_image[where c=c and s=s and t=t, OF bc st])
  show ?thesis by (simp add: Core_Structural_Burden.report_def
    Core_Structural_Burden.native_burden_covariance[where c=c and d=d, OF bc bd edges targets]
    Core_Structural_Burden.boundary_burden_covariance[where c=c and d=d, OF bc bd edges targets] ff)
qed
lemma diagnostic_report_transport:
  assumes bc: "bij c" and bd: "bij d" and bb: "bij b"
    and series: "\<And>a. fst (Core_Structural_Burden.rep_token (c a))=fst (Core_Structural_Burden.rep_token a)"
    and edges: "\<And>a z. Core_Structural_Burden.edge a z=Core_Structural_Burden.edge (c a) (c z)"
    and targets: "\<And>a. d (Core_Structural_Burden.StructTok a)=Core_Structural_Burden.StructTok (c a)"
    and st: "\<And>a. t (c a)=s a"
  shows "diagnostic_map c d b (diagnostics s boundary roots)=
    diagnostics t (b boundary) (map_option (image c) roots)"
proof -
  have sig: "function_map c (failure_signature s)=failure_signature t"
    by (rule function_transport[OF bc]) (simp add: failure_signature_def st)
  show ?thesis unfolding diagnostic_map_def diagnostics_def
    by (simp add: tagged_image reason_image[where c=c and s=s and t=t, OF bc st] local_reason_image[where c=c and s=s and t=t, OF bc st]
      approximation_group_image[OF bc series] sig failed_def fiber_image[where c=c and s=s and t=t, OF bc st]
      burden_report_transport[where c=c and d=d and s=s and t=t, OF bc bd edges targets st, unfolded failed_def])
qed
lemma assembled_report_transport:
  assumes bdata: "bij data" and bc: "bij c" and bd: "bij d" and bb: "bij b"
    and series: "\<And>a. fst (Core_Structural_Burden.rep_token (c a))=fst (Core_Structural_Burden.rep_token a)"
    and edges: "\<And>a z. Core_Structural_Burden.edge a z=Core_Structural_Burden.edge (c a) (c z)"
    and targets: "\<And>a. d (Core_Structural_Burden.StructTok a)=Core_Structural_Burden.StructTok (c a)"
    and st: "\<And>a. t (c a)=s a"
  shows "report_map data c d b (assemble input s boundary roots)=
    assemble (data input) t (b boundary) (map_option (image c) roots)"
  by (simp add: report_map_def assemble_def state_report_transport[where c=c and s=s and t=t, OF bc series st]
    diagnostic_report_transport[where c=c and d=d and b=b and s=s and t=t, OF bc bd bb series edges targets st])

lemma native_predecessors:
  "Core_Finite_Audit.predPass v (Core_Structural_Burden.rep_token a) =
    (\<forall>z. Core_Structural_Burden.edge z a \<longrightarrow> v (Core_Structural_Burden.rep_token z)=Core_Finite_Audit.SAT)"
proof (unfold Core_Finite_Audit.predPass_def, rule iffI)
  assume h: "\<forall>y\<in>Core_Finite_Audit.tokens. Core_Finite_Audit.edge y (Core_Structural_Burden.rep_token a) \<longrightarrow> v y=Core_Finite_Audit.SAT"
  show "\<forall>z. Core_Structural_Burden.edge z a \<longrightarrow> v (Core_Structural_Burden.rep_token z)=Core_Finite_Audit.SAT"
    using h report_token_typed by (auto simp: report_edge_exact)
next
  assume h: "\<forall>z. Core_Structural_Burden.edge z a \<longrightarrow> v (Core_Structural_Burden.rep_token z)=Core_Finite_Audit.SAT"
  show "\<forall>y\<in>Core_Finite_Audit.tokens. Core_Finite_Audit.edge y (Core_Structural_Burden.rep_token a) \<longrightarrow> v y=Core_Finite_Audit.SAT"
  proof (intro ballI impI)
    fix y assume y: "y\<in>Core_Finite_Audit.tokens" and e: "Core_Finite_Audit.edge y (Core_Structural_Burden.rep_token a)"
    show "v y=Core_Finite_Audit.SAT"
      using h[rule_format, of "Core_Structural_Burden.abs_token y"] e
      by (simp add: report_edge_exact report_token_inverse[OF y])
  qed
qed
lemma predecessors_transport:
  assumes bc: "bij c"
    and edges: "\<And>a z. Core_Structural_Burden.edge a z=Core_Structural_Burden.edge (c a) (c z)"
    and states: "\<And>a. v1 (Core_Structural_Burden.rep_token (c a))=v0 (Core_Structural_Burden.rep_token a)"
  shows "Core_Finite_Audit.predPass v1 (Core_Structural_Burden.rep_token (c a))=
    Core_Finite_Audit.predPass v0 (Core_Structural_Burden.rep_token a)"
  unfolding native_predecessors by (subst all_bij[OF bc]) (simp only: edges[symmetric] states)
lemma run_transport:
  assumes bc: "bij c"
    and edges: "\<And>a z. Core_Structural_Burden.edge a z=Core_Structural_Burden.edge (c a) (c z)"
    and forms: "\<And>a. f1 (c a)=f0 a" and evals: "\<And>a. e1 (c a)=e0 a" and conds: "\<And>a. q1 (c a)=q0 a"
  shows "Core_Finite_Audit.run (pair_input f1) (pair_input e1) (pair_input q1) n (Core_Structural_Burden.rep_token (c a))=
    Core_Finite_Audit.run (pair_input f0) (pair_input e0) (pair_input q0) n (Core_Structural_Burden.rep_token a)"
proof (induction n arbitrary: a)
  case 0 show ?case by (simp only: Core_Finite_Audit.run_zero[OF report_token_typed])
next
  case (Suc n)
  have pt: "Core_Finite_Audit.predPass (Core_Finite_Audit.run (pair_input f1) (pair_input e1) (pair_input q1) n) (Core_Structural_Burden.rep_token (c a))=
    Core_Finite_Audit.predPass (Core_Finite_Audit.run (pair_input f0) (pair_input e0) (pair_input q0) n) (Core_Structural_Burden.rep_token a)"
    by (rule predecessors_transport[where c=c]; (rule bc | rule edges | rule Suc.IH))
  show ?case by (simp only: Core_Finite_Audit.run_suc[OF report_token_typed]
    Core_Finite_Audit.step_def pt[unfolded pair_input_def]
    pair_input_def Core_Structural_Burden.rep_token_inverse forms evals conds)
qed
lemma native_output_transport:
  assumes bc: "bij c"
    and edges: "\<And>a z. Core_Structural_Burden.edge a z=Core_Structural_Burden.edge (c a) (c z)"
    and forms: "\<And>a. f1 (c a)=f0 a" and evals: "\<And>a. e1 (c a)=e0 a" and conds: "\<And>a. q1 (c a)=q0 a"
  shows "report_output f1 e1 q1 (c a)=report_output f0 e0 q0 a"
proof -
  have rt: "\<And>a. Core_Finite_Audit.run (pair_input f1) (pair_input e1) (pair_input q1) 40 (Core_Structural_Burden.rep_token (c a))=
      Core_Finite_Audit.run (pair_input f0) (pair_input e0) (pair_input q0) 40 (Core_Structural_Burden.rep_token a)"
    by (rule run_transport[where c=c]; (rule bc | rule edges | rule forms | rule evals | rule conds))
  have pt: "Core_Finite_Audit.predPass (Core_Finite_Audit.run (pair_input f1) (pair_input e1) (pair_input q1) 40) (Core_Structural_Burden.rep_token (c a))=
    Core_Finite_Audit.predPass (Core_Finite_Audit.run (pair_input f0) (pair_input e0) (pair_input q0) 40) (Core_Structural_Burden.rep_token a)"
    by (rule predecessors_transport[where c=c]; (rule bc | rule edges | rule rt))
  show ?thesis unfolding report_output_def Core_Finite_Audit.auditOutput_def
    by (simp only: rt pt)
qed
lemma native_report_covariance:
  assumes bdata: "bij data" and bc: "bij c" and bd: "bij d" and bb: "bij b"
    and series: "\<And>a. fst (Core_Structural_Burden.rep_token (c a))=fst (Core_Structural_Burden.rep_token a)"
    and edges: "\<And>a z. Core_Structural_Burden.edge a z=Core_Structural_Burden.edge (c a) (c z)"
    and targets: "\<And>a. d (Core_Structural_Burden.StructTok a)=Core_Structural_Burden.StructTok (c a)"
    and forms: "\<And>a. f1 (c a)=f0 a" and evals: "\<And>a. e1 (c a)=e0 a" and conds: "\<And>a. q1 (c a)=q0 a"
  shows "report_map data c d b (native_report input f0 e0 q0 boundary roots)=
    native_report (data input) f1 e1 q1 (b boundary) (map_option (image c) roots)"
  unfolding native_report_def
  apply (rule assembled_report_transport[where data=data and c=c and d=d and b=b, OF bdata bc bd bb series edges targets])
  by (rule native_output_transport[where c=c]; (rule bc | rule edges | rule forms | rule evals | rule conds))
lemma induced_report_equiv_unique:
  assumes bdata: "bij data" and bc: "bij c" and bd: "bij d" and bb: "bij b" and be: "bij e"
    and hd: "\<And>r. report_data (e r)=data (report_data r)"
    and hs: "\<And>r. report_states (e r)=state_map c (report_states r)"
    and hg: "\<And>r. report_diagnostics (e r)=diagnostic_map c d b (report_diagnostics r)"
  shows "e=report_map data c d b"
  by (rule ext; rule audit_report.equality) (simp_all add: report_map_def hd hs hg)

ML \<open>
val roots = @{thms function_transport state_report_transport approximation_group_image burden_report_transport diagnostic_report_transport assembled_report_transport native_output_transport native_report_covariance induced_report_equiv_unique};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
