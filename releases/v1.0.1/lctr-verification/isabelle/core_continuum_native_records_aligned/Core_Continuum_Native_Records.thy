theory Core_Continuum_Native_Records
 imports "LCTR_Core_Continuum_Datum.Core_Continuum_Datum"
 "LCTR_Core_Record_Codes_Aligned.Core_Record_Codes"
begin

datatype ('c,'b) record_object = TimeObject "'c set" | StateObject "'b set" | PairObject "'c set\<times>'b set"

context record_codes
begin
definition raw_source where "raw_source={x\<in>C\<times>D\<times>B. x\<in>R}"
definition raw_pair where "raw_pair x=(Image EC {fst x},Image EB {snd(snd x)})"
definition raw_object where
 "raw_object (i::nat) x=(if i=0 then TimeObject(fst(raw_pair x))
 else if i=1 then StateObject(snd(raw_pair x)) else PairObject(raw_pair x))"
definition object_domain where
 "object_domain (i::nat)=(if i=0 then image TimeObject (C//EC)
 else if i=1 then image StateObject (B//EB)
 else image PairObject (image_rel EC EB (source_rel C D B R)))"
definition native_records where
 "native_records mapping=\<lparr>record_domains=object_domain,
 code_relation=(\<lambda>i obj v. \<exists>x\<in>raw_source. raw_object i x=obj \<and> code(fst(snd x))=v),
 record_mapping=mapping\<rparr>"
lemma native_domains:
 "record_domains(native_records mapping)0=image TimeObject(C//EC) \<and>
 record_domains(native_records mapping)1=image StateObject(B//EB) \<and>
 record_domains(native_records mapping)2=image PairObject(image_rel EC EB(source_rel C D B R)) \<and>
 record_values=image code D"
 by (simp add: native_records_def object_domain_def record_values_def)

lemma raw_object_typed:
 assumes x: "x\<in>raw_source" and i: "i<3"
 shows "raw_object i x\<in>object_domain i"
proof -
 obtain c r b where eq: "x=(c,r,b)" and c: "c\<in>C" and r: "r\<in>D" and b: "b\<in>B"
  and src: "(c,r,b)\<in>R" using x unfolding raw_source_def by auto
 have tc: "Image EC {c}\<in>C//EC" by (rule quotientI[OF c])
 have sb: "Image EB {b}\<in>B//EB" by (rule quotientI[OF b])
 have pr: "((Image EC {c},Image EB {b}),code r)\<in>pair_records"
  by (rule pair_source_membership[OF c r b src])
 have tp: "(Image EC {c},Image EB {b})\<in>image_rel EC EB(source_rel C D B R)"
  using pair_records_typed[OF pr] by simp
 show ?thesis using tc sb tp eq unfolding raw_object_def object_domain_def raw_pair_def by auto
qed

lemma native_time_records:
 "code_relation(native_records mapping)0(TimeObject t)v \<longleftrightarrow> (t,v)\<in>time_records"
 by (auto simp: native_records_def raw_source_def raw_object_def raw_pair_def
 time_projection_exact pair_records_def; blast)
lemma native_state_records:
 "code_relation(native_records mapping)1(StateObject q)v \<longleftrightarrow> (q,v)\<in>state_records"
 by (auto simp: native_records_def raw_source_def raw_object_def raw_pair_def
 state_projection_exact pair_records_def; blast)
lemma native_pair_records:
 "code_relation(native_records mapping)2(PairObject p)v \<longleftrightarrow> (p,v)\<in>pair_records"
 by (auto simp: native_records_def raw_source_def raw_object_def raw_pair_def pair_records_def)
lemma native_code_typed:
 "code_relation(native_records mapping)i obj v \<Longrightarrow> v\<in>record_values"
 by (auto simp: native_records_def raw_source_def record_values_def)
lemma pair_domain_has_source:
 assumes p: "p\<in>image_rel EC EB (source_rel C D B R)"
 shows "\<exists>x\<in>raw_source. raw_pair x=p"
 using p unfolding image_rel_def source_rel_def raw_source_def raw_pair_def by auto
lemma pair_record_nonempty:
 assumes p: "p\<in>image_rel EC EB (source_rel C D B R)"
 shows "record_image(native_records mapping)2(PairObject p)\<noteq>{}"
proof -
 obtain x where x: "x\<in>raw_source" and eq: "raw_pair x=p"
  using pair_domain_has_source[OF p] by blast
 have rel: "code_relation(native_records mapping)2(PairObject p)(code(fst(snd x)))"
  unfolding native_records_def using x eq by (auto simp: raw_object_def)
 have "mapping(code(fst(snd x)))\<in>record_image(native_records mapping)2(PairObject p)"
  using rel unfolding record_image_def native_records_def by auto
 then show ?thesis by blast
qed
lemma native_image:
 "record_image(native_records mapping)i obj=
 {y. \<exists>x\<in>raw_source. raw_object i x=obj \<and> mapping(code(fst(snd x)))=y}"
 unfolding record_image_def native_records_def by auto
lemma native_collision:
 "collision(native_records mapping) \<longleftrightarrow>
 (\<exists>i<3. \<exists>x\<in>raw_source. \<exists>y\<in>raw_source.
 raw_object i x\<noteq>raw_object i y \<and>
 mapping(code(fst(snd x)))=mapping(code(fst(snd y))))"
proof -
 have typed: "\<And>i x. i<3 \<Longrightarrow> x\<in>raw_source \<Longrightarrow>
 raw_object i x\<in>record_domains(native_records mapping)i"
  by (simp add: native_records_def raw_object_typed)
 show ?thesis
 proof
  assume "collision(native_records mapping)"
  then obtain i a b where i: "i<3" and ne: "a\<noteq>b"
   and overlap: "record_image(native_records mapping)i a\<inter>record_image(native_records mapping)i b\<noteq>{}"
   unfolding collision_def by blast
  then obtain v where va: "v\<in>record_image(native_records mapping)i a"
   and vb: "v\<in>record_image(native_records mapping)i b" by blast
  obtain x where x: "x\<in>raw_source" and xa: "raw_object i x=a"
   and xv: "mapping(code(fst(snd x)))=v" using va unfolding native_image by blast
  obtain y where y: "y\<in>raw_source" and yb: "raw_object i y=b"
   and yv: "mapping(code(fst(snd y)))=v" using vb unfolding native_image by blast
  show "\<exists>i<3. \<exists>x\<in>raw_source. \<exists>y\<in>raw_source.
   raw_object i x\<noteq>raw_object i y \<and> mapping(code(fst(snd x)))=mapping(code(fst(snd y)))"
   apply (rule exI[where x=i], rule conjI[OF i])
   apply (rule bexI[where x=x], rule bexI[where x=y])
   apply (intro conjI)
   using ne xa yb apply simp
   using xv yv apply simp
   apply (rule y)
   apply (rule x)
   done
 next
  assume "\<exists>i<3. \<exists>x\<in>raw_source. \<exists>y\<in>raw_source.
   raw_object i x\<noteq>raw_object i y \<and> mapping(code(fst(snd x)))=mapping(code(fst(snd y)))"
  then obtain i x y where i: "i<3" and x: "x\<in>raw_source" and y: "y\<in>raw_source"
   and ne: "raw_object i x\<noteq>raw_object i y"
   and eq: "mapping(code(fst(snd x)))=mapping(code(fst(snd y)))" by blast
  have vx: "mapping(code(fst(snd x)))\<in>record_image(native_records mapping)i(raw_object i x)"
   using x unfolding native_image by blast
  have vy: "mapping(code(fst(snd x)))\<in>record_image(native_records mapping)i(raw_object i y)"
   unfolding native_image mem_Collect_eq
   apply (rule bexI[where x=y])
   using eq apply simp
   apply (rule y)
   done
  have ov: "record_image(native_records mapping)i(raw_object i x)\<inter>
   record_image(native_records mapping)i(raw_object i y)\<noteq>{}" using vx vy by blast
  show "collision(native_records mapping)"
   unfolding collision_def
   apply (rule exI[where x=i], rule conjI[OF i])
   apply (rule bexI[where x="raw_object i x"])
   apply (rule bexI[where x="raw_object i y"])
   apply (rule conjI[OF ne ov])
   apply (rule typed[OF i y])
   apply (rule typed[OF i x])
   done
 qed
qed
lemma native_separation_defect:
 assumes en: "0\<le>eps"
 shows "eps<separation_defect(native_records mapping) \<longleftrightarrow>
 ((\<exists>i<3. \<exists>x\<in>raw_source. \<exists>y\<in>raw_source.
 raw_object i x\<noteq>raw_object i y \<and>
 mapping(code(fst(snd x)))=mapping(code(fst(snd y)))) \<and> eps<1)"
 using separation_defect_excess[OF en, where r="native_records mapping"]
 by (simp add: native_collision)
lemma unmapped_codes_collision:
 "collision(native_records id) \<longleftrightarrow>
 (\<exists>i<3. \<exists>x\<in>raw_source. \<exists>y\<in>raw_source.
 raw_object i x\<noteq>raw_object i y \<and> code(fst(snd x))=code(fst(snd y)))"
 by (simp add: native_collision)
lemma raw_code_typed: "x\<in>raw_source \<Longrightarrow> code(fst(snd x))\<in>record_values"
 by (auto simp: raw_source_def record_values_def)
lemma injective_mapping_preserves_collision:
 assumes inj: "inj_on mapping record_values"
 shows "collision(native_records mapping) \<longleftrightarrow> collision(native_records id)"
proof -
 have eq: "\<And>x y. x\<in>raw_source \<Longrightarrow> y\<in>raw_source \<Longrightarrow>
  (mapping(code(fst(snd x)))=mapping(code(fst(snd y))) \<longleftrightarrow> code(fst(snd x))=code(fst(snd y)))"
  by (rule inj_on_eq_iff[OF inj raw_code_typed raw_code_typed]; assumption)
 show ?thesis by (simp add: native_collision eq)
qed
lemma extra_collision_requires_identification:
 assumes after: "collision(native_records mapping)" and before: "\<not>collision(native_records id)"
 shows "\<exists>a\<in>record_values. \<exists>b\<in>record_values. a\<noteq>b \<and> mapping a=mapping b"
proof -
 obtain i x y where i: "i<3" and x: "x\<in>raw_source" and y: "y\<in>raw_source"
 and ne: "raw_object i x\<noteq>raw_object i y"
 and eq: "mapping(code(fst(snd x)))=mapping(code(fst(snd y)))"
  using after unfolding native_collision by blast
 have different: "code(fst(snd x))\<noteq>code(fst(snd y))"
  using before i x y ne unfolding unmapped_codes_collision by blast
 show ?thesis using raw_code_typed[OF x] raw_code_typed[OF y] different eq by blast
qed
lemma empty_source_no_collision:
 assumes empty: "\<And>c r b. c\<in>C \<Longrightarrow> r\<in>D \<Longrightarrow> b\<in>B \<Longrightarrow> (c,r,b)\<notin>R"
 shows "\<not>collision(native_records mapping)"
 using empty unfolding native_collision raw_source_def by auto
end

ML \<open>
val roots = @{thms record_codes.native_domains record_codes.native_time_records
 record_codes.native_state_records record_codes.native_pair_records record_codes.pair_domain_has_source
 record_codes.pair_record_nonempty record_codes.native_image record_codes.native_collision
 record_codes.native_separation_defect record_codes.unmapped_codes_collision
 record_codes.injective_mapping_preserves_collision record_codes.extra_collision_requires_identification
 record_codes.empty_source_no_collision};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
