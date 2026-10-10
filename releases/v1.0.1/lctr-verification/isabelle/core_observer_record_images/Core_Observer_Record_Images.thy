theory Core_Observer_Record_Images
 imports "LCTR_Core_Continuum_Native_Records_Aligned.Core_Continuum_Native_Records"
 "LCTR_Core_Observer_Time.Core_Observer_Time"
begin

locale observer_record_images = observer_real C D B R Bind source_order rho
 for C :: "'c set" and D :: "'d set" and B :: "'b set"
 and R :: "('c\<times>'d\<times>'b) set"
 and Bind :: "(('c\<times>'d\<times>'b)\<times>('c\<times>'d\<times>'b)) set"
 and source_order :: "('c\<times>'c) set" and rho :: "'c set set\<Rightarrow>real" +
 fixes window :: "'d\<Rightarrow>'d set" and field :: "'d\<Rightarrow>'p" and sequence :: "'d\<Rightarrow>'n"
begin
sublocale rec: record_codes C D B R Bind window field sequence .
definition code_image where "code_image S=image rec.code (S\<inter>D)"
definition canonical_image where
 "canonical_image S={t. \<exists>v\<in>code_image S.
 code_relation(rec.native_records id)0(TimeObject t)v}"
definition order_image where "order_image S=image order_projection(canonical_image S)"
definition real_image where "real_image S=image time_rep(canonical_image S)"

lemma code_image_exact:
 "S\<subseteq>D \<Longrightarrow> code_image S=image rec.code S"
 by (auto simp: code_image_def)
lemma canonical_image_relation_inverse:
 "t\<in>canonical_image S \<longleftrightarrow> (\<exists>v\<in>image rec.code(S\<inter>D). (t,v)\<in>rec.time_records)"
 by (simp add: canonical_image_def code_image_def rec.native_time_records)
lemma canonical_image_source_witness:
 "t\<in>canonical_image S \<longleftrightarrow>
 (\<exists>w\<in>S\<inter>D. \<exists>x\<in>rec.raw_source.
 time_projection(fst x)=t \<and> rec.code(fst(snd x))=rec.code w)"
 unfolding canonical_image_def code_image_def rec.native_records_def
 rec.raw_object_def rec.raw_pair_def time_projection_def EC_def
 by auto
lemma source_record_in_image:
 assumes "c\<in>C" "r\<in>D" "b\<in>B" "(c,r,b)\<in>R" "r\<in>S"
 shows "time_projection c\<in>canonical_image S"
 unfolding canonical_image_source_witness
 apply (rule bexI[where x=r], rule bexI[where x="(c,r,b)"])
 using assms by (auto simp: rec.raw_source_def)
lemma equal_code_record_in_image:
 assumes "c\<in>C" "r\<in>D" "b\<in>B" "(c,r,b)\<in>R" "w\<in>S\<inter>D"
 and "rec.code r=rec.code w"
 shows "time_projection c\<in>canonical_image S"
 unfolding canonical_image_source_witness
 apply (rule bexI[where x=w], rule bexI[where x="(c,r,b)"])
 using assms by (auto simp: rec.raw_source_def)
lemma injective_code_window_characterization:
 assumes inj: "inj_on rec.code D"
 shows "t\<in>canonical_image S \<longleftrightarrow>
 (\<exists>x\<in>rec.raw_source. fst(snd x)\<in>S \<and> time_projection(fst x)=t)"
proof -
 have raw: "\<And>x. x\<in>rec.raw_source \<Longrightarrow> fst(snd x)\<in>D"
  by (auto simp: rec.raw_source_def)
 have eq: "\<And>x w. x\<in>rec.raw_source \<Longrightarrow> w\<in>D \<Longrightarrow>
  rec.code(fst(snd x))=rec.code w \<Longrightarrow> fst(snd x)=w"
  by (rule inj_onD[OF inj _ raw]; assumption)
 show ?thesis unfolding canonical_image_source_witness using raw eq by blast
qed
lemma image_monotonicity:
 assumes sub: "S\<subseteq>T"
 shows "code_image S\<subseteq>code_image T \<and> canonical_image S\<subseteq>canonical_image T \<and>
 order_image S\<subseteq>order_image T \<and> real_image S\<subseteq>real_image T"
proof -
 have c: "code_image S\<subseteq>code_image T" using sub unfolding code_image_def by blast
 have t: "canonical_image S\<subseteq>canonical_image T" using c unfolding canonical_image_def by blast
 show ?thesis using c t unfolding order_image_def real_image_def by blast
qed
lemma equal_code_images_same_time_images:
 assumes "code_image S=code_image T"
 shows "canonical_image S=canonical_image T \<and> order_image S=order_image T \<and>
 real_image S=real_image T"
 using assms by (simp add: canonical_image_def order_image_def real_image_def)
lemma real_image_factorization:
 "real_image S=image rho(order_image S)"
 by (simp add: real_image_def order_image_def time_rep_def image_comp)
lemma real_image_membership:
 "z\<in>real_image S \<longleftrightarrow> (\<exists>w\<in>S\<inter>D. \<exists>x\<in>rec.raw_source.
 rec.code(fst(snd x))=rec.code w \<and> time_rep(time_projection(fst x))=z)"
proof
 assume "z\<in>real_image S"
 then obtain t where t: "t\<in>canonical_image S" and tz: "time_rep t=z"
  unfolding real_image_def by blast
 obtain w x where w: "w\<in>S\<inter>D" and x: "x\<in>rec.raw_source"
  and xt: "time_projection(fst x)=t" and eq: "rec.code(fst(snd x))=rec.code w"
  using t unfolding canonical_image_source_witness by blast
 show "\<exists>w\<in>S\<inter>D. \<exists>x\<in>rec.raw_source.
  rec.code(fst(snd x))=rec.code w \<and> time_rep(time_projection(fst x))=z"
  apply (rule bexI[where x=w], rule bexI[where x=x])
  using eq xt tz x w by simp_all
next
 assume "\<exists>w\<in>S\<inter>D. \<exists>x\<in>rec.raw_source.
  rec.code(fst(snd x))=rec.code w \<and> time_rep(time_projection(fst x))=z"
 then obtain w x where w: "w\<in>S\<inter>D" and x: "x\<in>rec.raw_source"
  and eq: "rec.code(fst(snd x))=rec.code w" and xz: "time_rep(time_projection(fst x))=z" by blast
 have t: "time_projection(fst x)\<in>canonical_image S"
  unfolding canonical_image_source_witness
  apply (rule bexI[where x=w], rule bexI[where x=x])
  using eq x w by simp_all
 show "z\<in>real_image S" unfolding real_image_def
  by (rule image_eqI[where x="time_projection(fst x)"]) (rule xz[symmetric],rule t)
qed
lemma nonempty_images:
 "real_image S\<noteq>{} \<longleftrightarrow> canonical_image S\<noteq>{}"
 by (simp add: real_image_def)
lemma empty_window_images:
 "code_image {}={} \<and> canonical_image {}={} \<and> order_image {}={} \<and> real_image {}={}"
 by (simp add: code_image_def canonical_image_def order_image_def real_image_def)
lemma four_images_unique:
 "\<exists>!images. fst images=code_image S \<and>
 fst(snd images)={t. \<exists>v\<in>fst images. code_relation(rec.native_records id)0(TimeObject t)v} \<and>
 fst(snd(snd images))=image order_projection(fst(snd images)) \<and>
 snd(snd(snd images))=image rho(fst(snd(snd images)))"
 apply (rule ex1I[where a="(code_image S,canonical_image S,order_image S,real_image S)"])
 apply (simp add: canonical_image_def order_image_def real_image_factorization)
proof -
 fix images
 assume h: "fst images=code_image S \<and>
 fst(snd images)={t. \<exists>v\<in>fst images. code_relation(rec.native_records id)0(TimeObject t)v} \<and>
 fst(snd(snd images))=image order_projection(fst(snd images)) \<and>
 snd(snd(snd images))=image rho(fst(snd(snd images)))"
 obtain a b c d where im: "images=(a,b,c,d)" by (cases images; force)
 have a: "a=code_image S" using h im by simp
 have b: "b=canonical_image S" using h im a by (simp add: canonical_image_def)
 have c: "c=order_image S" using h im b by (simp add: order_image_def)
 have d: "d=real_image S" using h im c by (simp add: real_image_factorization)
 show "images=(code_image S,canonical_image S,order_image S,real_image S)"
  using im a b c d by simp
qed
lemma native_record_cell_factorization:
 "real_image(window r)=image rho(order_image(window r))"
 by (rule real_image_factorization)
lemma canonical_image_typed:
 "canonical_image S\<subseteq>Time"
 using canonical_image_source_witness projection_typed unfolding rec.raw_source_def by auto
lemma order_image_typed:
 "order_image S\<subseteq>OrderTime"
 using canonical_image_typed projection_contract unfolding order_image_def by blast
end

ML \<open>
val roots = @{thms observer_record_images.code_image_exact observer_record_images.canonical_image_relation_inverse
 observer_record_images.canonical_image_source_witness observer_record_images.source_record_in_image
 observer_record_images.equal_code_record_in_image observer_record_images.injective_code_window_characterization
 observer_record_images.image_monotonicity observer_record_images.equal_code_images_same_time_images
 observer_record_images.real_image_factorization observer_record_images.real_image_membership
 observer_record_images.nonempty_images observer_record_images.empty_window_images
 observer_record_images.four_images_unique observer_record_images.native_record_cell_factorization};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
