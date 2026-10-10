theory Core_Audit_Data
  imports "../core_audit_report/Core_Audit_Report"
begin

definition input_series :: "nat \<Rightarrow> nat" where "input_series b=b+3"
fun branch_formed :: "('a+'r) \<Rightarrow> bool" where
  "branch_formed (Inl x)=True" | "branch_formed (Inr r)=False"
definition approximation_token where
  "approximation_token i = Core_Structural_Burden.abs_token (3,i+1)"
definition evidence_at where
  "evidence_at strict approximation scale t =
    (if fst (Core_Structural_Burden.rep_token t)=3
     then approximation scale (snd (Core_Structural_Burden.rep_token t)-1) else strict t)"
definition evidence_typed where
  "evidence_typed E strict approximation =
    ((\<forall>t. fst (Core_Structural_Burden.rep_token t)\<noteq>3 \<longrightarrow> strict t\<in>E t) \<and>
     (\<forall>scale i. i<9 \<longrightarrow> approximation scale i\<in>E (approximation_token i)))"

record ('i,'e,'h,'t,'l) certificate =
  input_id :: 'i
  evidence_id :: 'e
  content_hash :: 'h
  transform_trace :: 't
  evidence_location :: 'l
record ('contract,'input,'evidence,'scale_data) core_data =
  core_contract :: 'contract
  core_input :: 'input
  core_evidence :: 'evidence
  core_scale_data :: 'scale_data
record ('core,'i,'e,'h,'t,'l) audit_data =
  data_core :: 'core
  data_certificate :: "('i,'e,'h,'t,'l) certificate"
record ('core,'scale,'boundary) evaluation_contract =
  formed :: "'core \<Rightarrow> 'scale \<Rightarrow> Core_Audit_Report.report_token \<Rightarrow> bool"
  evaluable :: "'core \<Rightarrow> 'scale \<Rightarrow> Core_Audit_Report.report_token \<Rightarrow> bool"
  condition :: "'core \<Rightarrow> 'scale \<Rightarrow> Core_Audit_Report.report_token \<Rightarrow> bool"
  boundary_value :: "'core \<Rightarrow> 'boundary"
  boundary_roots :: "'core \<Rightarrow> Core_Audit_Report.report_token set option"
definition readout where
  "readout contract data scale = Core_Audit_Report.native_report data
    (formed contract (data_core data) scale) (evaluable contract (data_core data) scale)
    (condition contract (data_core data) scale) (boundary_value contract (data_core data))
    (boundary_roots contract (data_core data))"

lemma input_series_exact:
  "(\<exists>b<3. input_series b=i) \<longleftrightarrow> i=3 \<or> i=4 \<or> i=5"
  unfolding input_series_def by presburger
lemma formed_branch_exact:
  "branch_formed x \<longleftrightarrow> (\<exists>y. x=Inl y)"
  by (cases x) auto
lemma unformed_branch_exact:
  "\<not>branch_formed x \<longleftrightarrow> (\<exists>reason. x=Inr reason)"
  by (cases x) auto
lemma approximation_token_rep:
  "i<9 \<Longrightarrow> Core_Structural_Burden.rep_token (approximation_token i)=(3,i+1)"
  unfolding approximation_token_def
  by (rule Core_Audit_Report.report_token_inverse)
    (simp add: Core_Finite_Audit.tokens_def Core_Finite_Audit.count_def)
lemma approximation_evidence_selected:
  "i<9 \<Longrightarrow> evidence_at strict approximation scale (approximation_token i)=approximation scale i"
  by (simp add: evidence_at_def approximation_token_rep)
lemma strict_evidence_scale_independent:
  "fst (Core_Structural_Burden.rep_token t)\<noteq>3 \<Longrightarrow>
    evidence_at strict approximation a t=evidence_at strict approximation b t"
  by (simp add: evidence_at_def)
lemma evidence_at_typed:
  assumes ty: "evidence_typed E strict approximation"
  shows "evidence_at strict approximation scale t\<in>E t"
proof (cases "fst (Core_Structural_Burden.rep_token t)=3")
  case False
  then show ?thesis using ty by (simp add: evidence_at_def evidence_typed_def)
next
  case True
  obtain b where rep0: "Core_Structural_Burden.rep_token t=(3,b)" and lo: "0<b" and hi: "b\<le>9"
    using Core_Audit_Report.report_token_typed[of t] True
    by (cases "Core_Structural_Burden.rep_token t")
      (auto simp: Core_Finite_Audit.tokens_def Core_Finite_Audit.count_def)
  let ?i="b-1"
  have b: "b=?i+1" using lo by arith
  have i: "?i<9" using lo hi by arith
  have rep: "Core_Structural_Burden.rep_token t=(3,?i+1)" by (simp only: rep0 b[symmetric])
  have t: "t=approximation_token ?i"
    using Core_Structural_Burden.rep_token_inverse[of t]
    by (simp add: approximation_token_def rep)
  show ?thesis using ty i by (simp add: t approximation_evidence_selected evidence_typed_def)
qed
lemma readout_data_exact:
  "Core_Audit_Report.report_data (readout contract data scale)=data"
  by (simp add: readout_def Core_Audit_Report.report_preserves_data)
lemma readout_certificate_exact:
  "data_certificate (Core_Audit_Report.report_data (readout contract data scale))=data_certificate data"
  by (simp add: readout_data_exact)
lemma certificate_fields_retained:
  "input_id (data_certificate (Core_Audit_Report.report_data (readout contract data scale)))=input_id (data_certificate data) \<and>
    evidence_id (data_certificate (Core_Audit_Report.report_data (readout contract data scale)))=evidence_id (data_certificate data) \<and>
    content_hash (data_certificate (Core_Audit_Report.report_data (readout contract data scale)))=content_hash (data_certificate data) \<and>
    transform_trace (data_certificate (Core_Audit_Report.report_data (readout contract data scale)))=transform_trace (data_certificate data) \<and>
    evidence_location (data_certificate (Core_Audit_Report.report_data (readout contract data scale)))=evidence_location (data_certificate data)"
  by (simp add: readout_data_exact)
lemma certificate_does_not_change_computation:
  "Core_Audit_Report.report_states (readout contract \<lparr>data_core=core,data_certificate=a\<rparr> scale)=
    Core_Audit_Report.report_states (readout contract \<lparr>data_core=core,data_certificate=b\<rparr> scale) \<and>
   Core_Audit_Report.report_diagnostics (readout contract \<lparr>data_core=core,data_certificate=a\<rparr> scale)=
    Core_Audit_Report.report_diagnostics (readout contract \<lparr>data_core=core,data_certificate=b\<rparr> scale)"
  by (simp add: readout_def Core_Audit_Report.native_report_def Core_Audit_Report.assemble_def)
lemma different_certificates_remain_distinct:
  assumes ne: "a\<noteq>b"
  shows "readout contract \<lparr>data_core=core,data_certificate=a\<rparr> scale \<noteq>
    readout contract \<lparr>data_core=core,data_certificate=b\<rparr> scale"
proof
  assume eq: "readout contract \<lparr>data_core=core,data_certificate=a\<rparr> scale =
    readout contract \<lparr>data_core=core,data_certificate=b\<rparr> scale"
  have "a=b" using arg_cong[OF eq, of "\<lambda>r. data_certificate (Core_Audit_Report.report_data r)"]
    by (simp add: readout_data_exact)
  then show False using ne by contradiction
qed
lemma typed_report_unique:
  "\<exists>!r. Core_Audit_Report.generated data
    (formed contract (data_core data) scale) (evaluable contract (data_core data) scale)
    (condition contract (data_core data) scale) (boundary_value contract (data_core data))
    (boundary_roots contract (data_core data)) r"
  by (rule Core_Audit_Report.native_report_unique)

ML \<open>
val roots = @{thms input_series_exact formed_branch_exact unformed_branch_exact approximation_evidence_selected strict_evidence_scale_independent readout_data_exact readout_certificate_exact certificate_fields_retained certificate_does_not_change_computation different_certificates_remain_distinct typed_report_unique};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
