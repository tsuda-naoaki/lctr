theory Core_Typed_Report_Covariance
  imports "../core_audit_data/Core_Audit_Data"
    "../support/core_report_equivalences/Core_Report_Equivalences"
begin

definition certificate_map where
  "certificate_map i e h t l p =
    \<lparr>input_id=i (input_id p), evidence_id=e (evidence_id p),
     content_hash=h (content_hash p), transform_trace=t (transform_trace p),
     evidence_location=l (evidence_location p)\<rparr>"
definition core_map where
  "core_map k x v s p =
    \<lparr>core_contract=k (core_contract p), core_input=x (core_input p),
     core_evidence=v (core_evidence p), core_scale_data=s (core_scale_data p)\<rparr>"
definition data_map where
  "data_map cm pm a =
    \<lparr>data_core=cm (data_core a), data_certificate=pm (data_certificate a)\<rparr>"

lemma certificate_map_left:
  assumes "bij i" "bij e" "bij h" "bij t" "bij l"
  shows "certificate_map (inv i) (inv e) (inv h) (inv t) (inv l)
    (certificate_map i e h t l (p::('i,'e,'h,'t,'l) certificate))=p"
  by (cases p) (simp add: certificate_map_def inv_f_f bij_is_inj assms)
lemma certificate_map_right:
  assumes "bij i" "bij e" "bij h" "bij t" "bij l"
  shows "certificate_map i e h t l
    (certificate_map (inv i) (inv e) (inv h) (inv t) (inv l)
      (p::('i,'e,'h,'t,'l) certificate))=p"
  by (cases p) (simp add: certificate_map_def surj_f_inv_f bij_is_surj assms)
lemma certificate_map_bij:
  assumes "bij i" "bij e" "bij h" "bij t" "bij l"
  shows "bij (certificate_map i e h t l ::
    ('i,'e,'h,'t,'l) certificate \<Rightarrow> ('j,'f,'g,'u,'m) certificate)"
proof (rule bijI)
  show "inj (certificate_map i e h t l ::
    ('i,'e,'h,'t,'l) certificate \<Rightarrow> ('j,'f,'g,'u,'m) certificate)"
    by (rule injI) (metis certificate_map_left[OF assms])
  show "surj (certificate_map i e h t l ::
    ('i,'e,'h,'t,'l) certificate \<Rightarrow> ('j,'f,'g,'u,'m) certificate)"
    using certificate_map_right[OF assms] unfolding surj_def by metis
qed
lemma core_map_left:
  assumes "bij k" "bij x" "bij v" "bij s"
  shows "core_map (inv k) (inv x) (inv v) (inv s)
    (core_map k x v s (p::('k,'x,'v,'s) core_data))=p"
  by (cases p) (simp add: core_map_def inv_f_f bij_is_inj assms)
lemma core_map_right:
  assumes "bij k" "bij x" "bij v" "bij s"
  shows "core_map k x v s (core_map (inv k) (inv x) (inv v) (inv s)
    (p::('k,'x,'v,'s) core_data))=p"
  by (cases p) (simp add: core_map_def surj_f_inv_f bij_is_surj assms)
lemma core_map_bij:
  assumes "bij k" "bij x" "bij v" "bij s"
  shows "bij (core_map k x v s ::
    ('k,'x,'v,'s) core_data \<Rightarrow> ('j,'y,'w,'r) core_data)"
proof (rule bijI)
  show "inj (core_map k x v s ::
    ('k,'x,'v,'s) core_data \<Rightarrow> ('j,'y,'w,'r) core_data)"
    by (rule injI) (metis core_map_left[OF assms])
  show "surj (core_map k x v s ::
    ('k,'x,'v,'s) core_data \<Rightarrow> ('j,'y,'w,'r) core_data)"
    using core_map_right[OF assms] unfolding surj_def by metis
qed
lemma data_map_left:
  assumes "bij cm" "bij pm"
  shows "data_map (inv cm) (inv pm)
    (data_map cm pm (a::('c,'i,'e,'h,'t,'l) audit_data))=a"
  by (cases a) (simp add: data_map_def inv_f_f bij_is_inj assms)
lemma data_map_right:
  assumes "bij cm" "bij pm"
  shows "data_map cm pm (data_map (inv cm) (inv pm)
    (a::('c,'i,'e,'h,'t,'l) audit_data))=a"
  by (cases a) (simp add: data_map_def surj_f_inv_f bij_is_surj assms)
lemma data_map_bij:
  assumes "bij cm" "bij pm"
  shows "bij (data_map cm pm ::
    ('c,'i,'e,'h,'t,'l) audit_data \<Rightarrow> ('d,'j,'f,'g,'u,'m) audit_data)"
proof (rule bijI)
  show "inj (data_map cm pm ::
    ('c,'i,'e,'h,'t,'l) audit_data \<Rightarrow> ('d,'j,'f,'g,'u,'m) audit_data)"
    by (rule injI) (metis data_map_left[OF assms])
  show "surj (data_map cm pm ::
    ('c,'i,'e,'h,'t,'l) audit_data \<Rightarrow> ('d,'j,'f,'g,'u,'m) audit_data)"
    using data_map_right[OF assms] unfolding surj_def by metis
qed

locale component_maps =
  fixes k :: "'k \<Rightarrow> 'j" and x :: "'x \<Rightarrow> 'y"
    and v :: "'v \<Rightarrow> 'w" and s :: "'s \<Rightarrow> 'r"
    and i :: "'i \<Rightarrow> 'ii" and e :: "'e \<Rightarrow> 'ee"
    and h :: "'h \<Rightarrow> 'hh" and t :: "'t \<Rightarrow> 'tt"
    and l :: "'l \<Rightarrow> 'll"
  assumes bk: "bij k" and bx: "bij x" and bv: "bij v" and bs: "bij s"
    and bi: "bij i" and be: "bij e" and bh: "bij h" and bt: "bij t" and bl: "bij l"
begin
abbreviation cm :: "('k,'x,'v,'s) core_data \<Rightarrow> ('j,'y,'w,'r) core_data"
  where "cm \<equiv> core_map k x v s"
abbreviation pm :: "('i,'e,'h,'t,'l) certificate \<Rightarrow> ('ii,'ee,'hh,'tt,'ll) certificate"
  where "pm \<equiv> certificate_map i e h t l"
abbreviation dm :: "(('k,'x,'v,'s) core_data,'i,'e,'h,'t,'l) audit_data \<Rightarrow>
  (('j,'y,'w,'r) core_data,'ii,'ee,'hh,'tt,'ll) audit_data"
  where "dm \<equiv> data_map cm pm"
lemma cm_bij: "bij cm" by (rule core_map_bij[OF bk bx bv bs])
lemma pm_bij: "bij pm" by (rule certificate_map_bij[OF bi be bh bt bl])
lemma dm_bij: "bij dm" by (rule data_map_bij[OF cm_bij pm_bij])

lemma certificate_correspondence_exact:
  "data_certificate (dm a)=pm (data_certificate a)"
  by (simp add: data_map_def)
lemma data_equivalence_injective: "inj dm"
  by (rule bij_is_inj[OF dm_bij])

lemma typed_readout_covariance:
  fixes left :: "(('k,'x,'v,'s) core_data,'a,'b) evaluation_contract"
    and right :: "(('j,'y,'w,'r) core_data,'z,'c) evaluation_contract"
  assumes scale: "bij sc" and tokens: "bij c" and structures: "bij d" and boundary: "bij b"
    and series: "\<And>a. fst (Core_Structural_Burden.rep_token (c a))=fst (Core_Structural_Burden.rep_token a)"
    and edges: "\<And>a z. Core_Structural_Burden.edge a z=Core_Structural_Burden.edge (c a) (c z)"
    and targets: "\<And>a. d (Core_Structural_Burden.StructTok a)=Core_Structural_Burden.StructTok (c a)"
    and forms: "\<And>core ell a. formed right (cm core) (sc ell) (c a)=formed left core ell a"
    and evals: "\<And>core ell a. evaluable right (cm core) (sc ell) (c a)=evaluable left core ell a"
    and conds: "\<And>core ell a. condition right (cm core) (sc ell) (c a)=condition left core ell a"
    and bounds: "\<And>core. boundary_value right (cm core)=b (boundary_value left core)"
    and roots: "\<And>core. boundary_roots right (cm core)=map_option (image c) (boundary_roots left core)"
  shows "report_map dm c d b (readout left a ell)=readout right (dm a) (sc ell)"
proof -
  have result: "report_map dm c d b
    (native_report a (formed left (data_core a) ell) (evaluable left (data_core a) ell)
      (condition left (data_core a) ell) (boundary_value left (data_core a)) (boundary_roots left (data_core a))) =
    native_report (dm a) (formed right (cm (data_core a)) (sc ell))
      (evaluable right (cm (data_core a)) (sc ell))
      (condition right (cm (data_core a)) (sc ell))
      (b (boundary_value left (data_core a))) (map_option (image c) (boundary_roots left (data_core a)))"
    by (rule native_report_covariance[where data=dm and c=c and d=d and b=b,
        OF dm_bij tokens structures boundary series edges targets])
      (rule forms, rule evals, rule conds)
  show ?thesis using result by (simp add: readout_def data_map_def bounds roots)
qed

lemma report_equivalence_unique_with_component_maps:
  assumes bc: "bij c" and bd: "bij d" and bb: "bij b" and bf: "bij f"
    and hd: "\<And>r. report_data (f r)=dm (report_data r)"
    and hs: "\<And>r. report_states (f r)=state_map c (report_states r)"
    and hg: "\<And>r. report_diagnostics (f r)=diagnostic_map c d b (report_diagnostics r)"
  shows "f=report_map dm c d b"
  by (rule induced_report_equiv_unique[where data=dm, OF dm_bij bc bd bb bf hd hs hg])

lemma transformed_certificate_fields:
  "input_id (data_certificate (report_data (readout right (dm a) ell)))=i (input_id (data_certificate a)) \<and>
   evidence_id (data_certificate (report_data (readout right (dm a) ell)))=e (evidence_id (data_certificate a)) \<and>
   content_hash (data_certificate (report_data (readout right (dm a) ell)))=h (content_hash (data_certificate a)) \<and>
   transform_trace (data_certificate (report_data (readout right (dm a) ell)))=t (transform_trace (data_certificate a)) \<and>
   evidence_location (data_certificate (report_data (readout right (dm a) ell)))=l (evidence_location (data_certificate a))"
  by (simp add: readout_data_exact data_map_def certificate_map_def)
end

ML \<open>
val roots = @{thms component_maps.certificate_correspondence_exact component_maps.data_equivalence_injective component_maps.typed_readout_covariance component_maps.report_equivalence_unique_with_component_maps component_maps.transformed_certificate_fields};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
