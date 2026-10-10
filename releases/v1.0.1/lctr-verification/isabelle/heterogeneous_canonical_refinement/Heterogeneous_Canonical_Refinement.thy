theory Heterogeneous_Canonical_Refinement
 imports LCTR_Heterogeneous_Presentation_Arrows.Heterogeneous_Presentation_Arrows
begin

lemma partial_order_relation_laws:
 assumes p: "part_on A L"
 shows "refl_on A {(x,y). x\<in>A \<and> y\<in>A \<and> L x y}"
   "trans {(x,y). x\<in>A \<and> y\<in>A \<and> L x y}"
 using p unfolding part_on_def pre_on_def refl_on_def trans_def by auto

lemma heterogeneous_native_canonical_arrow:
 assumes ec: "equiv C EC" and eb: "equiv B EB" and typed: "R\<subseteq>C\<times>B"
   and po: "part_on (q`C) L"
   and adm: "native_admissible C B EC EB ord R q p
     {(x,y). x\<in>q`C \<and> y\<in>q`C \<and> L x y} trj"
 shows "\<exists>f g. presentation_arrow C B (\<lambda>c. EC``{c}) (\<lambda>b. EB``{b})
    (\<lambda>x y. (x,y)\<in>reach_on (C//EC) (source_quotient_edges C EC ord))
    (image_rel EC EB R) q p L trj f g \<and>
   (\<forall>h k. presentation_arrow C B (\<lambda>c. EC``{c}) (\<lambda>b. EB``{b})
    (\<lambda>x y. (x,y)\<in>reach_on (C//EC) (source_quotient_edges C EC ord))
    (image_rel EC EB R) q p L trj h k \<longrightarrow>
    (\<forall>x\<in>C//EC. h x=f x) \<and> (\<forall>y\<in>B//EB. k y=g y))"
proof -
 interpret N: dynamics_factor_pair C EC q B EB p R
   by unfold_locales (use ec eb typed adm in \<open>auto simp: native_admissible_def\<close>)
 let ?L = "{(x,y). x\<in>q`C \<and> y\<in>q`C \<and> L x y}"
 have rf: "refl_on (q`C) ?L" and tr: "trans ?L"
   by (rule partial_order_relation_laws[OF po])+
 have monob: "\<forall>x\<in>C. \<forall>y\<in>C. (x,y)\<in>ord \<longrightarrow> (q x,q y)\<in>?L"
   using adm unfolding native_admissible_def by iprover
 have mono: "\<And>x y. x\<in>C \<Longrightarrow> y\<in>C \<Longrightarrow> (x,y)\<in>ord \<Longrightarrow> (q x,q y)\<in>?L"
   by (rule monob[rule_format])
 have mo: "\<forall>x\<in>C//EC. \<forall>y\<in>C//EC.
    (x,y)\<in>reach_on (C//EC) (source_quotient_edges C EC ord)
    \<longrightarrow> L (N.C.F x) (N.C.F y)"
 proof (intro ballI impI)
   fix x y assume xy: "(x,y)\<in>reach_on (C//EC) (source_quotient_edges C EC ord)"
   have path: "(x,y)\<in>reach_on (C//EC) (N.C.edges ord)"
     using xy by (simp only: N.C.source_quotient_edges_agree)
   have "(N.C.F x,N.C.F y)\<in>?L" by (rule N.C.factor_monotone[OF rf tr mono path])
   then show "L (N.C.F x) (N.C.F y)" by simp
 qed
 have image: "trj=(\<lambda>(x,y). (N.C.F x,N.B.F y))`image_rel EC EB R"
   using adm N.trajectory_factor_image unfolding native_admissible_def by iprover
 have cc: "\<forall>c\<in>C. N.C.F (EC``{c})=q c"
   by (intro ballI) (rule N.C.commutes)
 have cb: "\<forall>b\<in>B. N.B.F (EB``{b})=p b"
   by (intro ballI) (rule N.B.commutes)
 have a: "presentation_arrow C B (\<lambda>c. EC``{c}) (\<lambda>b. EB``{b})
    (\<lambda>x y. (x,y)\<in>reach_on (C//EC) (source_quotient_edges C EC ord))
    (image_rel EC EB R) q p L trj N.C.F N.B.F"
   unfolding presentation_arrow_def canonical_projection_surjective
   using N.C.factor_image N.B.factor_image cc cb mo image by iprover
 have unique: "\<And>h k. presentation_arrow C B (\<lambda>c. EC``{c}) (\<lambda>b. EB``{b})
    (\<lambda>x y. (x,y)\<in>reach_on (C//EC) (source_quotient_edges C EC ord))
    (image_rel EC EB R) q p L trj h k \<Longrightarrow>
    (\<forall>x\<in>C//EC. h x=N.C.F x) \<and> (\<forall>y\<in>B//EB. k y=N.B.F y)"
 proof -
   fix h k assume h: "presentation_arrow C B (\<lambda>c. EC``{c}) (\<lambda>b. EB``{b})
    (\<lambda>x y. (x,y)\<in>reach_on (C//EC) (source_quotient_edges C EC ord))
    (image_rel EC EB R) q p L trj h k"
   have hc0: "\<forall>c\<in>C. h(EC``{c})=q c"
     and hb0: "\<forall>b\<in>B. k(EB``{b})=p b"
     using h unfolding presentation_arrow_def by iprover+
   have hc: "\<And>c. c\<in>C \<Longrightarrow> h(EC``{c})=q c" by (rule hc0[rule_format])
   have hb: "\<And>b. b\<in>B \<Longrightarrow> k(EB``{b})=p b" by (rule hb0[rule_format])
   show "(\<forall>x\<in>C//EC. h x=N.C.F x) \<and> (\<forall>y\<in>B//EB. k y=N.B.F y)"
     by (rule N.pair_unique[OF hc hb])
 qed
 show ?thesis using a unique by blast
qed

locale heterogeneous_pair =
 fixes C :: "'c set" and B :: "'b set"
   and q :: "'c\<Rightarrow>'t" and p :: "'b\<Rightarrow>'s"
   and L :: "'t\<Rightarrow>'t\<Rightarrow>bool" and R :: "('t\<times>'s) set"
   and r :: "'c\<Rightarrow>'u" and s :: "'b\<Rightarrow>'v"
   and M :: "'u\<Rightarrow>'u\<Rightarrow>bool" and U :: "('u\<times>'v) set"
 assumes typed_R: "R\<subseteq>(q`C)\<times>(p`B)"
   and typed_U: "U\<subseteq>(r`C)\<times>(s`B)"
begin
definition cq where "cq i = (if i then fiber_encode C q\<circ>q else fiber_encode C r\<circ>r)"
definition bq where "bq i = (if i then fiber_encode B p\<circ>p else fiber_encode B s\<circ>s)"
definition lo where "lo i = (if i then fiber_order C q L else fiber_order C r M)"
definition tj where "tj i = (if i then fiber_relation C q B p R else fiber_relation C r B s U)"

sublocale P: presentations C B "\<lambda>i. cq i`C" "\<lambda>i. bq i`B" cq bq lo tj
proof (unfold_locales)
 show "\<And>i. cq i`C=cq i`C" by (rule refl)
 show "\<And>i. bq i`B=bq i`B" by (rule refl)
 fix i show "tj i \<subseteq> (cq i`C)\<times>(bq i`B)"
   using fiber_relation_typed[OF typed_R] fiber_relation_typed[OF typed_U]
   by (cases i) (simp_all add: cq_def bq_def tj_def fiber_carrier_def image_image)
qed

lemma heterogeneous_pair_refinement_iff:
 "P.refines True False \<longleftrightarrow>
  (\<exists>f g. presentation_arrow C B r s M U q p L R f g)"
proof -
 have e: "P.refines True False \<longleftrightarrow>
   (\<exists>F G. presentation_arrow C B
    (fiber_encode C r\<circ>r) (fiber_encode B s\<circ>s)
    (fiber_order C r M) (fiber_relation C r B s U)
    (fiber_encode C q\<circ>q) (fiber_encode B p\<circ>p)
    (fiber_order C q L) (fiber_relation C q B p R) F G)"
   unfolding P.refines_def P.family_arrow_is_heterogeneous
   by (simp only: cq_def bq_def lo_def tj_def if_True if_False)
 show ?thesis using e heterogeneous_arrow_encoding_iff[OF typed_U typed_R, where L=M and M=L]
   by blast
qed

lemma heterogeneous_pair_class_refinement_iff:
 "qrel UNIV P.E P.refines (P.E``{True}) (P.E``{False}) \<longleftrightarrow>
  (\<exists>f g. presentation_arrow C B r s M U q p L R f g)"
 using P.class_refinement_relation heterogeneous_pair_refinement_iff by blast

lemma heterogeneous_pair_mutual_iff_structural_iso:
 "((\<exists>f g. presentation_arrow C B r s M U q p L R f g) \<and>
   (\<exists>h k. presentation_arrow C B q p L R r s M U h k)) \<longleftrightarrow>
  (\<exists>F G H K. P.structural_iso False True F G H K)"
proof -
 have reverse: "P.refines False True \<longleftrightarrow>
    (\<exists>h k. presentation_arrow C B q p L R r s M U h k)"
 proof -
   have e: "P.refines False True \<longleftrightarrow>
     (\<exists>F G. presentation_arrow C B
      (fiber_encode C q\<circ>q) (fiber_encode B p\<circ>p)
      (fiber_order C q L) (fiber_relation C q B p R)
      (fiber_encode C r\<circ>r) (fiber_encode B s\<circ>s)
      (fiber_order C r M) (fiber_relation C r B s U) F G)"
     unfolding P.refines_def P.family_arrow_is_heterogeneous
     by (simp only: cq_def bq_def lo_def tj_def if_True if_False)
   show ?thesis using e heterogeneous_arrow_encoding_iff[OF typed_R typed_U, where L=L and M=M]
     by blast
 qed
 show ?thesis using P.alignment_mutual_iff_iso[of False True]
   heterogeneous_pair_refinement_iff reverse by blast
qed
end

definition encoded_class_refinement where
 "encoded_class_refinement C B q p L R r s M U i j \<longleftrightarrow>
  (let cq=heterogeneous_pair.cq C q r;
       bq=heterogeneous_pair.bq B p s;
       lo=heterogeneous_pair.lo C q L r M;
       tj=heterogeneous_pair.tj C B q p R r s U;
       E=presentations.E C B (\<lambda>i. cq i`C) (\<lambda>i. bq i`B) cq bq lo tj;
       ref=presentations.refines C B (\<lambda>i. cq i`C) (\<lambda>i. bq i`B) cq bq lo tj
   in qrel UNIV E ref (E``{i}) (E``{j}))"

lemma heterogeneous_native_canonical_class_greatest:
 assumes ec: "equiv C EC" and eb: "equiv B EB" and typed: "R\<subseteq>C\<times>B"
   and po: "part_on (q`C) L"
   and adm: "native_admissible C B EC EB ord R q p
     {(x,y). x\<in>q`C \<and> y\<in>q`C \<and> L x y} trj"
 shows "encoded_class_refinement C B q p L trj
   (\<lambda>c. EC``{c}) (\<lambda>b. EB``{b})
   (\<lambda>x y. (x,y)\<in>reach_on (C//EC) (source_quotient_edges C EC ord))
   (image_rel EC EB R) True False"
proof -
 have t: "trj\<subseteq>(q`C)\<times>(p`B)"
   using adm typed unfolding native_admissible_def by auto
 have tc: "image_rel EC EB R \<subseteq>
     ((\<lambda>c. EC``{c})`C)\<times>((\<lambda>b. EB``{b})`B)"
   using typed unfolding image_rel_def by auto
 interpret H: heterogeneous_pair C B q p L trj
     "\<lambda>c. EC``{c}" "\<lambda>b. EB``{b}"
     "\<lambda>x y. (x,y)\<in>reach_on (C//EC) (source_quotient_edges C EC ord)"
     "image_rel EC EB R"
   by unfold_locales (rule t, rule tc)
 have a: "\<exists>f g. presentation_arrow C B (\<lambda>c. EC``{c}) (\<lambda>b. EB``{b})
    (\<lambda>x y. (x,y)\<in>reach_on (C//EC) (source_quotient_edges C EC ord))
    (image_rel EC EB R) q p L trj f g"
   using heterogeneous_native_canonical_arrow[OF ec eb typed po adm] by blast
 show ?thesis unfolding encoded_class_refinement_def Let_def
   by (rule H.heterogeneous_pair_class_refinement_iff[THEN iffD2, OF a])
qed

ML \<open>
val roots = @{thms partial_order_relation_laws heterogeneous_native_canonical_arrow
 heterogeneous_pair.heterogeneous_pair_refinement_iff
 heterogeneous_pair.heterogeneous_pair_class_refinement_iff
 heterogeneous_pair.heterogeneous_pair_mutual_iff_structural_iso
 heterogeneous_native_canonical_class_greatest};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
