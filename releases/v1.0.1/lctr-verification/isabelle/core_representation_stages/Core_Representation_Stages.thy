theory Core_Representation_Stages
 imports LCTR_Core_Exact_Structure.Core_Exact_Structure
begin

locale representation_base = native_comparison D f tr adm
 for D :: "'u\<Rightarrow>'s set" and f :: "'u\<Rightarrow>'s\<Rightarrow>'v"
 and tr :: "'u\<Rightarrow>'u\<Rightarrow>'v\<Rightarrow>'v\<Rightarrow>bool"
 and adm :: "'u\<Rightarrow>'u\<Rightarrow>bool" +
 fixes r :: "'s\<Rightarrow>'s\<Rightarrow>bool"
 assumes source_pre: "pre_on UNIV r"
 and source_anti: "\<And>x y. r x y \<Longrightarrow> r y x \<Longrightarrow> x=y"
begin
abbreviation C where "C \<equiv> exact_structure.canonical_carrier D f tr adm"
abbreviation L where "L \<equiv> exact_structure.local_carrier D f tr adm"
abbreviation cle where "cle \<equiv> exact_structure.canonical_le D f tr adm r"
abbreviation clt where "clt \<equiv> exact_structure.canonical_lt D f tr adm r"
abbreviation cp where "cp \<equiv> exact_structure.canonical_projection D f tr adm"
abbreviation chart where "chart \<equiv> exact_structure.local_chart D f tr adm r"
abbreviation lg where "lg \<equiv> exact_structure.local_global D f tr adm r"

definition first where
 "first \<longleftrightarrow> ord_desc (native_carrier D f) (native_equiv D f tr adm) (pullback recover_tag r)"
definition second where "second \<longleftrightarrow> first \<and> (\<forall>i. inc_trans_on(L i)clt)"
definition third where "third \<longleftrightarrow> second \<and> inc_trans_on C clt"
definition exact_gate where "exact_gate operative \<longleftrightarrow> operative \<and> third"

lemma exact_from_first:
 assumes h: first
 shows "exact_structure D f tr adm r"
proof -
 have desc: "ord_desc (native_carrier D f) (native_equiv D f tr adm) (pullback recover_tag r)"
  using h unfolding first_def .
 show ?thesis by unfold_locales (rule source_pre, rule source_anti, assumption, assumption, fact desc)
qed

theorem condition_hierarchy: "(third \<longrightarrow> second) \<and> (second \<longrightarrow> first)"
 by (simp add: second_def third_def)

theorem first_creates_actual_order:
 assumes h: first
 shows "part_on C cle"
proof -
 interpret E: exact_structure D f tr adm r by (rule exact_from_first[OF h])
 show ?thesis by (rule E.canonical_partial_order)
qed

theorem second_creates_actual_charts:
 assumes h: second
 shows "image(chart i)(regions D f i)=QuSet(L i)clt \<and>
  (\<forall>a\<in>regions D f i. \<forall>b\<in>regions D f i. chart i a=chart i b \<longleftrightarrow>
   \<not>clt(cp a)(cp b) \<and> \<not>clt(cp b)(cp a))"
proof -
 have h1: first and hi: "inc_trans_on(L i)clt" using h unfolding second_def by auto
 interpret E: exact_structure D f tr adm r by (rule exact_from_first[OF h1])
 show ?thesis using E.actual_local_chart_contract[OF hi] by blast
qed

theorem third_creates_actual_embeddings:
 assumes h: third
 shows "inj_on(lg i)(QuSet(L i)clt) \<and>
  (\<forall>a\<in>regions D f i. lg i (chart i a)=qproj C clt(cp a))"
proof -
 have h1: first and hi: "inc_trans_on(L i)clt" and hg: "inc_trans_on C clt"
  using h unfolding third_def second_def by auto
 interpret E: exact_structure D f tr adm r by (rule exact_from_first[OF h1])
 show ?thesis using E.local_global_injective[OF hi hg] E.local_global_chart_commutes[OF hi hg] by blast
qed

theorem exact_condition_expansion:
 "exact_gate operative \<longleftrightarrow> operative \<and> first \<and> (\<forall>i. inc_trans_on(L i)clt) \<and> inc_trans_on C clt"
 by (simp add: exact_gate_def third_def second_def)

theorem exact_preserves_comparison_gate:
 "exact_gate operative \<Longrightarrow> operative"
 by (simp add: exact_gate_def)

definition stage_one where "stage_one=(cle,clt,L)"
definition stage_two where "stage_two=(stage_one,chart,(\<lambda>i j. overlap_change(L i)(L j)clt))"
definition stage_three where "stage_three=(stage_two,qproj C clt,lg)"

theorem first_payload_retained:
 "second \<Longrightarrow> fst stage_two=stage_one"
 by (simp add: stage_two_def)
theorem second_payload_retained:
 "third \<Longrightarrow> fst stage_three=stage_two"
 by (simp add: stage_three_def)
theorem original_payload_retained:
 "third \<Longrightarrow> fst(fst stage_three)=stage_one"
 by (simp add: stage_three_def stage_two_def)
end

datatype three_point = Z | M | T
definition control_strict where "control_strict x y \<longleftrightarrow> x=Z \<and> y=T"
definition control_carrier where
 "control_carrier i={x. if i then x\<noteq>Z else x\<noteq>T}"

theorem control_local_strict_empty:
 assumes "x\<in>control_carrier i" "y\<in>control_carrier i"
 shows "\<not>control_strict x y"
 using assms by (cases i) (auto simp: control_carrier_def control_strict_def)

theorem control_domains_cover:
 "\<forall>x. \<exists>i. x\<in>control_carrier i"
proof
 fix x
 show "\<exists>i. x\<in>control_carrier i"
 proof (cases x)
  case Z
  show ?thesis by (rule exI[of _ False]) (simp add: Z control_carrier_def)
 next
  case M
  show ?thesis by (rule exI[of _ False]) (simp add: M control_carrier_def)
 next
  case T
  show ?thesis by (rule exI[of _ True]) (simp add: T control_carrier_def)
 qed
qed

theorem control_domains_overlap:
 "\<exists>x. x\<in>control_carrier False \<and> x\<in>control_carrier True"
 by (rule exI[of _ M]) (simp add: control_carrier_def)

lemma control_strict_partial: "strict_on UNIV control_strict"
 unfolding strict_on_def control_strict_def by auto

lemma control_local_inc: "inc_trans_on(control_carrier i)control_strict"
 using control_local_strict_empty
 unfolding inc_trans_on_def inc_on_def by blast

lemma control_global_not_inc: "\<not>inc_trans_on UNIV control_strict"
proof
 assume h: "inc_trans_on UNIV control_strict"
 have a: "inc_on UNIV control_strict Z M" and b: "inc_on UNIV control_strict M T"
  by (simp_all add: inc_on_def control_strict_def)
 have "inc_on UNIV control_strict Z T" using h a b unfolding inc_trans_on_def by blast
 then show False by (simp add: inc_on_def control_strict_def)
qed

theorem local_cover_does_not_force_global_inc:
 "(\<forall>x. \<exists>i. x\<in>control_carrier i) \<and>
  (\<forall>i. inc_trans_on(control_carrier i)control_strict) \<and>
  \<not>inc_trans_on UNIV control_strict"
 using control_domains_cover control_local_inc control_global_not_inc by blast

ML \<open>
val roots = @{thms representation_base.condition_hierarchy representation_base.first_creates_actual_order
 representation_base.second_creates_actual_charts representation_base.third_creates_actual_embeddings
 representation_base.exact_condition_expansion representation_base.exact_preserves_comparison_gate
 representation_base.first_payload_retained representation_base.second_payload_retained
 representation_base.original_payload_retained control_local_strict_empty control_domains_cover
 control_domains_overlap local_cover_does_not_force_global_inc};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
