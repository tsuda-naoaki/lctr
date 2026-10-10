theory Core_Report_Equivalences
  imports "../../core_report_covariance/Core_Report_Covariance"
begin

lemma function_map_left:
  "bij c \<Longrightarrow> function_map (inv c) (function_map c f)=f"
  by (rule ext) (simp add: function_map_def inv_inv_eq inv_f_f bij_is_inj)
lemma reason_set_left:
  assumes bc: "bij c"
  shows "Core_Audit_Tags.reason_map (inv c) ` (Core_Audit_Tags.reason_map c ` R)=R"
proof -
  have point: "\<And>p. Core_Audit_Tags.reason_map (inv c) (Core_Audit_Tags.reason_map c p)=p"
    by (simp add: Core_Audit_Tags.reason_map_def inv_f_f[OF bij_is_inj[OF bc]] split: prod.splits)
  show ?thesis by (simp add: image_image point)
qed
lemma tagged_map_left:
  assumes bc: "bij c" and vi: "\<And>y. vi (v y)=y"
  shows "Core_Audit_Tags.tagged_map vi (inv c) (Core_Audit_Tags.tagged_map v c x)=x"
  by (cases x) (simp_all add: Core_Audit_Tags.tagged_map_def vi reason_set_left[OF bc])
lemma state_map_left:
  assumes bc: "bij c"
  shows "state_map (inv c) (state_map c (r::state_report))=r"
  by (cases r) (simp add: state_map_def function_map_left[OF bc]
    image_inv_f_f[OF bij_is_inj[OF bc]] reason_set_left[OF bc])
lemma diagnostic_map_left:
  assumes bc: "bij c" and bd: "bij d" and bb: "bij b"
  shows "diagnostic_map (inv c) (inv d) (inv b) (diagnostic_map c d b (r::'b diagnostic_report))=r"
proof -
  have si: "\<And>S. inv c ` (c ` S)=S" by (rule image_inv_f_f[OF bij_is_inj[OF bc]])
  have fi: "\<And>f. function_map (inv c) (function_map c f)=f" by (rule function_map_left[OF bc])
  have bi: "\<And>y. inv b (b y)=y" by (rule inv_f_f[OF bij_is_inj[OF bb]])
  have di: "\<And>p. map_prod (image (inv d)) (image (inv d)) (map_prod (image d) (image d) p)=p"
  proof -
    fix p
    show "map_prod (image (inv d)) (image (inv d)) (map_prod (image d) (image d) p)=p"
      by (cases p) (simp add: image_inv_f_f[OF bij_is_inj[OF bd]])
  qed
  show ?thesis by (cases r)
    (simp add: diagnostic_map_def
      tagged_map_left[where c=c and vi="image (inv c)" and v="image c", OF bc si]
      tagged_map_left[where c=c and vi="function_map (inv c)" and v="function_map c", OF bc fi]
      tagged_map_left[where c=c and vi="inv b" and v=b, OF bc bi]
      tagged_map_left[where c=c and vi="map_prod (image (inv d)) (image (inv d))"
        and v="map_prod (image d) (image d)", OF bc di])
qed
lemma report_map_left_inverse:
  assumes bdata: "bij data" and bc: "bij c" and bd: "bij d" and bb: "bij b"
  shows "report_map (inv data) (inv c) (inv d) (inv b)
    (report_map data c d b (r::('d,'b) audit_report))=r"
  by (cases r) (simp add: report_map_def inv_f_f[OF bij_is_inj[OF bdata]]
    state_map_left[OF bc] diagnostic_map_left[OF bc bd bb])
lemma report_map_right_inverse:
  assumes bdata: "bij data" and bc: "bij c" and bd: "bij d" and bb: "bij b"
  shows "report_map data c d b
    (report_map (inv data) (inv c) (inv d) (inv b) (r::('e,'c) audit_report))=r"
  using report_map_left_inverse[OF bij_imp_bij_inv[OF bdata] bij_imp_bij_inv[OF bc]
    bij_imp_bij_inv[OF bd] bij_imp_bij_inv[OF bb], of r]
  by (simp add: inv_inv_eq bdata bc bd bb)
lemma report_map_bijective:
  assumes bdata: "bij data" and bc: "bij c" and bd: "bij d" and bb: "bij b"
  shows "bij (report_map data c d b :: ('d,'b) audit_report \<Rightarrow> ('e,'c) audit_report)"
proof (rule bijI)
  show "inj (report_map data c d b :: ('d,'b) audit_report \<Rightarrow> ('e,'c) audit_report)"
    by (rule injI) (metis report_map_left_inverse[OF bdata bc bd bb])
  show "surj (report_map data c d b :: ('d,'b) audit_report \<Rightarrow> ('e,'c) audit_report)"
    using report_map_right_inverse[OF bdata bc bd bb]
    unfolding surj_def by metis
qed

ML \<open>
val roots = @{thms report_map_left_inverse report_map_right_inverse report_map_bijective};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
