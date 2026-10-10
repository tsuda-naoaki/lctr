theory Core_Record_Cells
 imports LCTR_Core_Exact_Structure.Core_Exact_Structure
 LCTR_Core_Affine_Frequency.Core_Affine_Frequency
begin

definition extrema where
 "extrema (S::'p::linorder set) e \<longleftrightarrow> fst e\<in>S \<and> snd e\<in>S \<and>
  (\<forall>p\<in>S. fst e\<le>p \<and> p\<le>snd e)"
definition has_ext where "has_ext S \<longleftrightarrow> (\<exists>e. extrema S e)"

theorem has_ext_iff:
 "has_ext S \<longleftrightarrow> S\<noteq>{} \<and> (\<exists>l\<in>S. \<exists>h\<in>S. \<forall>p\<in>S. l\<le>p \<and> p\<le>h)"
proof
 assume "has_ext S"
 then obtain e where e: "extrema S e" unfolding has_ext_def by blast
 then show "S\<noteq>{} \<and> (\<exists>l\<in>S. \<exists>h\<in>S. \<forall>p\<in>S. l\<le>p \<and> p\<le>h)"
  unfolding extrema_def by blast
next
 assume "S\<noteq>{} \<and> (\<exists>l\<in>S. \<exists>h\<in>S. \<forall>p\<in>S. l\<le>p \<and> p\<le>h)"
 then obtain l h where a: "l\<in>S" "h\<in>S" "\<forall>p\<in>S. l\<le>p \<and> p\<le>h" by blast
 have "extrema S (l,h)" using a by (simp add: extrema_def)
 then show "has_ext S" unfolding has_ext_def by blast
qed

theorem extrema_unique:
 assumes e: "extrema S e" and f: "extrema S f"
 shows "fst e=fst f \<and> snd e=snd f"
 using e f unfolding extrema_def by (meson antisym)
theorem extrema_ordered: "extrema S e \<Longrightarrow> fst e\<le>snd e"
 unfolding extrema_def by blast
theorem empty_has_no_extrema: "\<not>has_ext {}"
 by (simp add: has_ext_def extrema_def)

context affine_frequency
begin
definition affine_width where "affine_width e=diff(snd e)(fst e)"
definition span_on_domain where "span_on_domain S=affine_width(SOME e. extrema S e)"

theorem width_nonnegative:
 assumes e: "extrema S e"
 shows "0\<le>affine_width e"
 using extrema_ordered[OF e] difference_nonnegative[of "fst e" "snd e"]
 by (simp add: affine_width_def)
theorem width_witness_independent:
 "extrema S e \<Longrightarrow> extrema S f \<Longrightarrow> affine_width e=affine_width f"
 using extrema_unique unfolding affine_width_def by metis

theorem span_agrees_with_every_witness:
 assumes h: "has_ext S" and e: "extrema S e"
 shows "span_on_domain S=affine_width e"
proof -
 have chosen: "extrema S (SOME e. extrema S e)" using h unfolding has_ext_def by (rule someI_ex)
 show ?thesis unfolding span_on_domain_def by (rule width_witness_independent[OF chosen e])
qed

theorem singleton_width_zero:
 assumes e: "extrema {p} e"
 shows "affine_width e=0"
 using e difference_reflexive unfolding extrema_def affine_width_def by auto
end

locale record_representation = exact_structure D f tr adm r
 for D :: "'u\<Rightarrow>'s set" and f :: "'u\<Rightarrow>'s\<Rightarrow>'v"
 and tr :: "'u\<Rightarrow>'u\<Rightarrow>'v\<Rightarrow>'v\<Rightarrow>bool"
 and adm :: "'u\<Rightarrow>'u\<Rightarrow>bool" and r +
 fixes emb :: "(('u\<times>'v) set) set \<Rightarrow> 'p::linorder"
 assumes global_inc: "inc_trans_on canonical_carrier canonical_lt"
 and embedding: "\<And>a b. a\<in>QuSet canonical_carrier canonical_lt \<Longrightarrow>
  b\<in>QuSet canonical_carrier canonical_lt \<Longrightarrow>
  (emb a<emb b \<longleftrightarrow> qlt canonical_carrier canonical_lt a b)"
begin

theorem representation_injective:
 "inj_on emb (QuSet canonical_carrier canonical_lt)"
proof (rule inj_onI)
 fix a b assume a: "a\<in>QuSet canonical_carrier canonical_lt"
 and b: "b\<in>QuSet canonical_carrier canonical_lt" and eq: "emb a=emb b"
 have lin: "Order_Embedding_Isabelle.strict_linear_on (QuSet canonical_carrier canonical_lt)
  (qlt canonical_carrier canonical_lt)" by (rule actual_global_quotient_linear[OF global_inc])
 have total: "a\<noteq>b \<Longrightarrow> qlt canonical_carrier canonical_lt a b \<or> qlt canonical_carrier canonical_lt b a"
  using lin a b unfolding Order_Embedding_Isabelle.strict_linear_on_def by blast
 show "a=b" using total embedding[OF a b] embedding[OF b a] eq by auto
qed

definition arrival_class where "arrival_class i x=canonical_projection(i,f i x)"
definition order_class where "order_class i x=qproj canonical_carrier canonical_lt(arrival_class i x)"
definition record_value where "record_value i x=represented emb(arrival_class i x)"
definition cell_tokens where "cell_tokens W i x=W x\<inter>D i"
definition cell_image where "cell_image W i x=image(record_value i)(cell_tokens W i x)"

lemma order_class_typed:
 assumes x: "x\<in>D i"
 shows "order_class i x\<in>QuSet canonical_carrier canonical_lt"
proof -
 have arr: "(i,f i x)\<in>native_carrier D f" using x unfolding regions_def by blast
 have ca: "arrival_class i x\<in>canonical_carrier" unfolding arrival_class_def by (rule projection_maps[OF arr])
 show ?thesis using ca unfolding order_class_def QuSet_def by blast
qed

theorem record_value_factorization:
 "record_value i x=emb(order_class i x)"
 by (simp add: record_value_def represented_def order_class_def)

theorem record_value_kernel:
 assumes x: "x\<in>D i" and y: "y\<in>D j"
 shows "record_value i x=record_value j y \<longleftrightarrow> order_class i x=order_class j y"
 unfolding record_value_factorization
 by (rule inj_on_eq_iff[OF representation_injective order_class_typed[OF x] order_class_typed[OF y]])

theorem cell_image_membership:
 "p\<in>cell_image W i x \<longleftrightarrow> (\<exists>y\<in>D i. y\<in>W x \<and> record_value i y=p)"
 by (auto simp: cell_image_def cell_tokens_def)
theorem cell_image_nonempty:
 "cell_image W i x\<noteq>{} \<longleftrightarrow> cell_tokens W i x\<noteq>{}"
 by (simp add: cell_image_def)

definition associated_image where
 "associated_image W rel i x={p. \<exists>y\<in>D i. rel x y \<and> p\<in>cell_image W i y}"
theorem associated_image_nonempty:
 "associated_image W rel i x\<noteq>{} \<longleftrightarrow> (\<exists>y\<in>D i. rel x y \<and> cell_tokens W i y\<noteq>{})"
proof
 assume "associated_image W rel i x\<noteq>{}"
 then obtain p y where y: "y\<in>D i" "rel x y" "p\<in>cell_image W i y"
  unfolding associated_image_def by blast
 have "cell_image W i y\<noteq>{}" using y(3) by blast
 then have "cell_tokens W i y\<noteq>{}" by (rule cell_image_nonempty[THEN iffD1])
 then show "\<exists>y\<in>D i. rel x y \<and> cell_tokens W i y\<noteq>{}" using y(1,2) by blast
next
 assume "\<exists>y\<in>D i. rel x y \<and> cell_tokens W i y\<noteq>{}"
 then obtain y where y: "y\<in>D i" "rel x y" "cell_tokens W i y\<noteq>{}" by blast
 have "cell_image W i y\<noteq>{}" using y(3) by (rule cell_image_nonempty[THEN iffD2])
 then obtain p where "p\<in>cell_image W i y" by blast
 then show "associated_image W rel i x\<noteq>{}" using y(1,2) unfolding associated_image_def by blast
qed

definition c_order_class where
 "c_order_class DC fC trC admC rC i x=
  qproj(exact_structure.canonical_carrier DC fC trC admC)
   (exact_structure.canonical_lt DC fC trC admC rC)
   (exact_structure.canonical_projection DC fC trC admC(i,fC i x))"
definition separates where
 "separates DC fC trC admC rC W rel \<longleftrightarrow>
  (\<forall>i. \<forall>x\<in>DC i. \<forall>y\<in>DC i.
   c_order_class DC fC trC admC rC i x\<noteq>c_order_class DC fC trC admC rC i y \<longrightarrow>
   associated_image W rel i x\<noteq>{} \<and> associated_image W rel i y\<noteq>{} \<and>
   (\<forall>p. p\<in>associated_image W rel i x \<longrightarrow> p\<notin>associated_image W rel i y))"

theorem separation_exact_contract:
 "separates DC fC trC admC rC W rel \<longleftrightarrow>
  (\<forall>i. \<forall>x\<in>DC i. \<forall>y\<in>DC i.
   c_order_class DC fC trC admC rC i x\<noteq>c_order_class DC fC trC admC rC i y \<longrightarrow>
   associated_image W rel i x\<noteq>{} \<and> associated_image W rel i y\<noteq>{} \<and>
   associated_image W rel i x\<inter>associated_image W rel i y={})"
 by (auto simp: separates_def)

theorem collision_excludes_separation:
 assumes x: "x\<in>DC i" and y: "y\<in>DC i"
 and neq: "c_order_class DC fC trC admC rC i x\<noteq>c_order_class DC fC trC admC rC i y"
 and px: "p\<in>associated_image W rel i x" and py: "p\<in>associated_image W rel i y"
 shows "\<not>separates DC fC trC admC rC W rel"
 using assms unfolding separates_def by blast
theorem missing_record_excludes_separation:
 assumes x: "x\<in>DC i" and y: "y\<in>DC i"
 and neq: "c_order_class DC fC trC admC rC i x\<noteq>c_order_class DC fC trC admC rC i y"
 and missing: "associated_image W rel i x={}"
 shows "\<not>separates DC fC trC admC rC W rel"
 using assms unfolding separates_def by blast
end

locale record_affine =
 R: record_representation D f tr adm r emb + A: affine_frequency act diff
 for D :: "'u\<Rightarrow>'s set" and f :: "'u\<Rightarrow>'s\<Rightarrow>'v"
 and tr :: "'u\<Rightarrow>'u\<Rightarrow>'v\<Rightarrow>'v\<Rightarrow>bool"
 and adm :: "'u\<Rightarrow>'u\<Rightarrow>bool" and r
 and emb :: "(('u\<times>'v) set) set \<Rightarrow> 'p::linorder"
 and act :: "'p\<Rightarrow>'k::linordered_field\<Rightarrow>'p"
 and diff :: "'p\<Rightarrow>'p\<Rightarrow>'k"
begin
definition width_admissible where
 "width_admissible W g \<longleftrightarrow> (\<forall>i x.
  (R.cell_tokens W i x\<noteq>{} \<longrightarrow> has_ext(R.cell_image W i x)) \<and>
  (has_ext(R.cell_image W i x) \<longrightarrow> A.span_on_domain(R.cell_image W i x)\<le>g))"

theorem width_admissibility_contract:
 "width_admissible W g \<longleftrightarrow> (\<forall>i x.
  (R.cell_tokens W i x\<noteq>{} \<longrightarrow> has_ext(R.cell_image W i x)) \<and>
  (\<forall>e. extrema(R.cell_image W i x)e \<longrightarrow> A.affine_width e\<le>g))"
proof -
 have eq: "\<And>S. (has_ext S \<longrightarrow> A.span_on_domain S\<le>g) \<longleftrightarrow>
  (\<forall>e. extrema S e \<longrightarrow> A.affine_width e\<le>g)"
 proof
  fix S assume h: "has_ext S \<longrightarrow> A.span_on_domain S\<le>g"
  show "\<forall>e. extrema S e \<longrightarrow> A.affine_width e\<le>g"
  proof (intro allI impI)
   fix e assume e: "extrema S e"
   have ex: "has_ext S" using e unfolding has_ext_def by blast
   show "A.affine_width e\<le>g" using h ex A.span_agrees_with_every_witness[OF ex e] by simp
  qed
 next
  fix S assume h: "\<forall>e. extrema S e \<longrightarrow> A.affine_width e\<le>g"
  show "has_ext S \<longrightarrow> A.span_on_domain S\<le>g"
  proof
   assume ex: "has_ext S"
   then obtain e where e: "extrema S e" unfolding has_ext_def by blast
   have bound: "A.affine_width e\<le>g" using h e by blast
   show "A.span_on_domain S\<le>g" using bound A.span_agrees_with_every_witness[OF ex e] by simp
  qed
 qed
 show ?thesis unfolding width_admissible_def using eq by blast
qed

theorem admissible_nonempty_cell_has_bounded_width:
 assumes g: "0\<le>g" and adm: "width_admissible W g" and ne: "R.cell_tokens W i x\<noteq>{}"
 shows "\<exists>e. extrema(R.cell_image W i x)e \<and> 0\<le>A.affine_width e \<and> A.affine_width e\<le>g"
proof -
 have ext: "has_ext(R.cell_image W i x)" using adm ne unfolding width_admissible_def by blast
 obtain e where e: "extrema(R.cell_image W i x)e" using ext unfolding has_ext_def by blast
 have low: "0\<le>A.affine_width e" by (rule A.width_nonnegative[OF e])
 have bounds: "\<forall>i x. (R.cell_tokens W i x\<noteq>{} \<longrightarrow> has_ext(R.cell_image W i x)) \<and>
  (\<forall>e. extrema(R.cell_image W i x)e \<longrightarrow> A.affine_width e\<le>g)"
  using adm width_admissibility_contract[where W=W and g=g] by blast
 have high: "A.affine_width e\<le>g" using bounds e by blast
 show ?thesis using e low high by blast
qed
end

ML \<open>
val roots = @{thms record_representation.representation_injective
 record_representation.record_value_factorization record_representation.record_value_kernel
 record_representation.cell_image_membership record_representation.cell_image_nonempty
 has_ext_iff extrema_unique extrema_ordered affine_frequency.width_nonnegative
 affine_frequency.width_witness_independent affine_frequency.span_agrees_with_every_witness
 empty_has_no_extrema affine_frequency.singleton_width_zero
 record_affine.width_admissibility_contract record_affine.admissible_nonempty_cell_has_bounded_width
 record_representation.associated_image_nonempty record_representation.separation_exact_contract
 record_representation.collision_excludes_separation record_representation.missing_record_excludes_separation};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
