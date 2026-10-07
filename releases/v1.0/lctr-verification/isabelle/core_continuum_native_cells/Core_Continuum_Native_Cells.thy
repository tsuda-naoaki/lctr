theory Core_Continuum_Native_Cells
 imports "LCTR_Core_Observer_Record_Images.Core_Observer_Record_Images"
 "LCTR_Core_Record_Cells.Core_Record_Cells"
begin

definition mapped_image where
 "mapped_image m (S::real set)=image(map_candidate m)(S\<inter>map_interval m)"
lemma mapped_full_image:
 "S\<subseteq>map_interval m \<Longrightarrow> mapped_image m S=image(map_candidate m)S"
 by (auto simp: mapped_image_def)
lemma mapped_image_membership:
 "y\<in>mapped_image m S \<longleftrightarrow> (\<exists>z\<in>map_interval m. z\<in>S \<and> map_candidate m z=y)"
 by (auto simp: mapped_image_def)

locale native_record_cells =
 cmp: record_representation Arr f tr adm comparison_order emb +
 obs: observer_record_images C D B R Bind source_order rho window field sequence
 for Arr :: "'u\<Rightarrow>'d set" and f :: "'u\<Rightarrow>'d\<Rightarrow>'v"
 and tr :: "'u\<Rightarrow>'u\<Rightarrow>'v\<Rightarrow>'v\<Rightarrow>bool"
 and adm :: "'u\<Rightarrow>'u\<Rightarrow>bool" and comparison_order
 and emb :: "(('u\<times>'v)set)set\<Rightarrow>real"
 and C :: "'c set" and D :: "'d set" and B :: "'b set"
 and R :: "('c\<times>'d\<times>'b)set"
 and Bind :: "(('c\<times>'d\<times>'b)\<times>('c\<times>'d\<times>'b))set"
 and source_order :: "('c\<times>'c)set" and rho :: "'c set set\<Rightarrow>real"
 and window :: "'d\<Rightarrow>'d set" and field :: "'d\<Rightarrow>'p" and sequence :: "'d\<Rightarrow>'n" +
 assumes arrival_carrier: "\<And>u. Arr u\<subseteq>D"
 and window_carrier: "\<And>x. x\<in>D \<Longrightarrow> window x\<subseteq>D"
begin
definition comparison_image where "comparison_image x=cmp.cell_image window (fst x)(snd x)"
definition observer_image where "observer_image x=obs.real_image(window x)"
definition native_maps where
 "native_maps cm om other (i::nat)=(if i=1 then cm else if i=2 then om else other i)"
definition native_indices :: "nat\<Rightarrow>(('u\<times>'d)+'d)set" where
 "native_indices t=(if t=0 then image Inl (UNIV\<times>D) else image Inr D)"
definition native_cells where
 "native_cells cm om (t::nat) x=(if t=0 then
 (case x of Inl p \<Rightarrow> comparison_image p\<inter>map_interval cm | Inr r \<Rightarrow> {})
 else (case x of Inl p \<Rightarrow> {} | Inr r \<Rightarrow> observer_image r\<inter>map_interval om))"
definition native_width where
 "native_width cm om other=cell_width(native_maps cm om other)native_indices(native_cells cm om)"

lemma comparison_cell_exact:
 "cell_image(native_maps cm om other)(native_cells cm om)0(Inl x)=mapped_image cm(comparison_image x)"
 by (simp add: cell_image_def native_maps_def native_cells_def mapped_image_def)
lemma observer_cell_exact:
 "cell_image(native_maps cm om other)(native_cells cm om)1(Inr x)=mapped_image om(observer_image x)"
 by (simp add: cell_image_def native_maps_def native_cells_def mapped_image_def)
lemma comparison_native_witness:
 "y\<in>mapped_image cm(comparison_image (u,x)) \<longleftrightarrow>
 (\<exists>z\<in>map_interval cm. (\<exists>q\<in>Arr u. q\<in>window x \<and> cmp.record_value u q=z) \<and> map_candidate cm z=y)"
 by (simp only: mapped_image_membership comparison_image_def fst_conv snd_conv cmp.cell_image_membership)
lemma observer_native_witness:
 "y\<in>mapped_image om(observer_image r) \<longleftrightarrow>
 (\<exists>z\<in>map_interval om. (\<exists>w\<in>window r\<inter>D. \<exists>x\<in>obs.rec.raw_source.
 obs.rec.code(fst(snd x))=obs.rec.code w \<and>
 obs.time_rep(obs.time_projection(fst x))=z) \<and> map_candidate om z=y)"
 by (simp only: mapped_image_membership observer_image_def obs.real_image_membership)
lemma two_indices: "{..<2::nat}={0,1}" by auto
lemma two_cases: "t<(2::nat) \<longleftrightarrow> t=0 \<or> t=1" by arith
lemma both_families_width_bound:
 assumes en: "0\<le>eps"
 shows "native_width cm om other\<le>eps \<longleftrightarrow>
 (\<forall>u. \<forall>r\<in>D. diameter(map_deviation cm)(mapped_image cm(comparison_image(u,r)))\<le>eps) \<and>
 (\<forall>r\<in>D. diameter(map_deviation om)(mapped_image om(observer_image r))\<le>eps)"
 unfolding native_width_def cell_width_def two_indices
 by (simp add: nnSup_bound[OF en] native_indices_def native_maps_def
 cell_image_def native_cells_def mapped_image_def)
lemma both_families_width_excess:
 assumes en: "0\<le>eps"
 shows "eps<native_width cm om other \<longleftrightarrow>
 (\<exists>u. \<exists>r\<in>D. \<exists>a\<in>mapped_image cm(comparison_image(u,r)).
 \<exists>b\<in>mapped_image cm(comparison_image(u,r)). eps<map_deviation cm a b) \<or>
 (\<exists>r\<in>D. \<exists>a\<in>mapped_image om(observer_image r).
 \<exists>b\<in>mapped_image om(observer_image r). eps<map_deviation om a b)"
 using both_families_width_bound[OF en, of cm om other]
 by (simp add: diameter_bound[OF en] not_le[symmetric])
lemma native_width_source_supremum:
 "native_width cm om other=Sup({0}\<union>
 {v. \<exists>u. \<exists>r\<in>D. v=diameter(map_deviation cm)(mapped_image cm(comparison_image(u,r)))}\<union>
 {v. \<exists>r\<in>D. v=diameter(map_deviation om)(mapped_image om(observer_image r))})"
proof -
 have sets: "{v. \<exists>t<2. \<exists>x\<in>native_indices t.
 v=diameter(map_deviation(native_maps cm om other(Suc t)))
 (cell_image(native_maps cm om other)(native_cells cm om)t x)} =
 {v. \<exists>u. \<exists>r\<in>D. v=diameter(map_deviation cm)(mapped_image cm(comparison_image(u,r)))}\<union>
 {v. \<exists>r\<in>D. v=diameter(map_deviation om)(mapped_image om(observer_image r))}"
  by (auto simp: two_cases native_indices_def native_maps_def cell_image_def native_cells_def mapped_image_def)
 show ?thesis unfolding native_width_def width_equals_source_supremum sets by simp
qed
lemma full_cell_images_preserved:
 assumes c: "\<And>u r. r\<in>D \<Longrightarrow> comparison_image(u,r)\<subseteq>map_interval cm"
 and o: "\<And>r. r\<in>D \<Longrightarrow> observer_image r\<subseteq>map_interval om"
 shows "(\<forall>u. \<forall>r\<in>D. cell_image(native_maps cm om other)(native_cells cm om)0(Inl(u,r))=
 image(map_candidate cm)(comparison_image(u,r))) \<and>
 (\<forall>r\<in>D. cell_image(native_maps cm om other)(native_cells cm om)1(Inr r)=
 image(map_candidate om)(observer_image r))"
proof (intro conjI allI ballI)
 fix u r assume r: "r\<in>D"
 show "cell_image(native_maps cm om other)(native_cells cm om)0(Inl(u,r))=
 image(map_candidate cm)(comparison_image(u,r))"
 proof -
  have a: "cell_image(native_maps cm om other)(native_cells cm om)0(Inl(u,r))=
   mapped_image cm(comparison_image(u,r))" by (rule comparison_cell_exact)
  have b: "mapped_image cm(comparison_image(u,r))=image(map_candidate cm)(comparison_image(u,r))"
   by (rule mapped_full_image[OF c[OF r]])
  show ?thesis using a b by simp
 qed
next
 fix r assume r: "r\<in>D"
 show "cell_image(native_maps cm om other)(native_cells cm om)1(Inr r)=image(map_candidate om)(observer_image r)"
 proof -
  have a: "cell_image(native_maps cm om other)(native_cells cm om)1(Inr r)=mapped_image om(observer_image r)"
   by (rule observer_cell_exact)
  have b: "mapped_image om(observer_image r)=image(map_candidate om)(observer_image r)"
   by (rule mapped_full_image[OF o[OF r]])
  show ?thesis using a b by simp
 qed
qed
end

ML \<open>
val roots = @{thms mapped_full_image native_record_cells.comparison_cell_exact
 native_record_cells.observer_cell_exact native_record_cells.comparison_native_witness
 native_record_cells.observer_native_witness native_record_cells.both_families_width_bound
 native_record_cells.both_families_width_excess native_record_cells.native_width_source_supremum
 native_record_cells.full_cell_images_preserved};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
