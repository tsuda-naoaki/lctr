theory Generic_Differential_Covariance
  imports "LCTR_Generic_Value_Change.Generic_Value_Change"
    "LCTR_Core_Representation_Images.Core_Representation_Images"
begin

lemmas value_map_bijective = Generic_Value_Change.generic_value_map_bijective
lemmas value_preserves_time_coordinate = Native_Value_Change.preserves_time_coordinate
lemmas value_relation_image = Generic_Value_Change.generic_value_relation_image
lemmas time_map_bijective = Native_Time_Change.time_change_map_bijective
lemmas time_relation_image = Native_Time_Change.time_change_relation_image
lemmas time_preserves_zeroth_value = Native_Time_Change.time_change_preserves_zeroth

context representation_images
begin
lemma generic_differential_covariance:
  assumes vc: "\<forall>i\<in>I. value_change_valid (kv i) (Uv i) (Vv i) (Wv i) (fv i) (gv i) (JV i) (KV i)"
    and av: "\<forall>i\<in>I. Av i\<subseteq>Uv i\<times>jet_domain (kv i) (Vv i)"
    and bv: "\<forall>i\<in>I. Bv i\<subseteq>Uv i\<times>jet_domain (kv i) (Wv i)"
    and cv: "\<forall>i\<in>I. \<forall>p\<in>Uv i\<times>jet_domain (kv i) (Vv i).
      p\<in>Av i \<longleftrightarrow> value_jet_map (JV i) p\<in>Bv i"
    and tc: "\<forall>j\<in>T. time_change_valid (kt j) (Vt j) (Ut j) (Wt j) (ft j) (gt j) (JT j) (KT j)"
    and at: "\<forall>j\<in>T. At j\<subseteq>Ut j\<times>jet_domain (kt j) (Vt j)"
    and bt: "\<forall>j\<in>T. Bt j\<subseteq>Wt j\<times>jet_domain (kt j) (Vt j)"
    and ct: "\<forall>j\<in>T. \<forall>p\<in>Ut j\<times>jet_domain (kt j) (Vt j).
      p\<in>At j \<longleftrightarrow> time_jet_map (ft j) (JT j) p\<in>Bt j"
    and source_coord: "\<forall>j\<in>T. image (sc j) (Ut j)\<subseteq>image f A"
    and target_coord: "\<forall>j\<in>T. image (dc j) (Wt j)\<subseteq>image g A"
    and link: "\<forall>j\<in>T. \<forall>a\<in>Ut j. F (sc j a)=dc j (ft j a)"
  shows "\<exists>H. bij_betw H (image f A) (image g A) \<and>
    (\<forall>u\<in>image f A. \<forall>v\<in>image f A. (H u<H v)=(u<v)) \<and>
    (\<forall>x\<in>A. H (f x)=g x) \<and>
    (\<forall>i\<in>I. image (value_jet_map (JV i)) (Av i)=Bv i) \<and>
    (\<forall>j\<in>T. image (time_jet_map (ft j) (JT j)) (At j)=Bt j) \<and>
    (\<forall>j\<in>T. \<forall>a\<in>Ut j. H (sc j a)=dc j (ft j a)) \<and>
    (\<forall>G. (\<forall>x\<in>A. G (f x)=g x) \<longrightarrow> (\<forall>y\<in>image f A. G y=H y))"
proof -
  have vi: "image (value_jet_map (JV i)) (Av i)=Bv i" if "i\<in>I" for i
    by (rule generic_value_relation_image[where k="kv i" and U="Uv i" and V="Vv i"
      and W="Wv i" and f="fv i" and g="gv i" and K="KV i"])
      (use vc av bv cv that in blast)+
  have ti: "image (time_jet_map (ft j) (JT j)) (At j)=Bt j" if "j\<in>T" for j
    by (rule time_change_relation_image[where k="kt j" and V="Vt j" and U="Ut j"
      and W="Wt j" and g="gt j" and K="KT j"])
      (use tc at bt ct that in blast)+
  show ?thesis
  proof (rule exI[of _ F], intro conjI)
    show "bij_betw F (image f A) (image g A)" by (rule image_map_bijective)
    show "\<forall>u\<in>image f A. \<forall>v\<in>image f A. (F u<F v)=(u<v)"
      by (intro ballI, rule image_map_order)
    show "\<forall>x\<in>A. F (f x)=g x" by (intro ballI, rule image_map_commutes)
    show "\<forall>i\<in>I. image (value_jet_map (JV i)) (Av i)=Bv i" using vi by blast
    show "\<forall>j\<in>T. image (time_jet_map (ft j) (JT j)) (At j)=Bt j" using ti by blast
    show "\<forall>j\<in>T. \<forall>a\<in>Ut j. F (sc j a)=dc j (ft j a)" by (rule link)
    show "\<forall>G. (\<forall>x\<in>A. G (f x)=g x) \<longrightarrow> (\<forall>y\<in>image f A. G y=F y)"
      using image_map_unique by blast
  qed
qed
end
lemmas differential_covariance = representation_images.generic_differential_covariance
ML \<open>
val roots = @{thms value_map_bijective value_preserves_time_coordinate value_relation_image
  time_map_bijective time_relation_image time_preserves_zeroth_value differential_covariance};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
