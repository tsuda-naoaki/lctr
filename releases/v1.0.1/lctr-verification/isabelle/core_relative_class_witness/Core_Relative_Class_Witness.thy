theory Core_Relative_Class_Witness
 imports Main
begin

lemma product_nonempty:
 "(\<exists>w. \<forall>i\<in>I. w i\<in>P i) \<longleftrightarrow> (\<forall>i\<in>I. P i\<noteq>{})"
proof
 assume "\<exists>w. \<forall>i\<in>I. w i\<in>P i"
 then show "\<forall>i\<in>I. P i\<noteq>{}" by blast
next
 assume ne: "\<forall>i\<in>I. P i\<noteq>{}"
 let ?w = "\<lambda>i. SOME e. e\<in>P i"
 have "\<forall>i\<in>I. ?w i\<in>P i"
 proof
  fix i assume "i\<in>I"
  then have "\<exists>e. e\<in>P i" using ne by blast
  then show "?w i\<in>P i" by (rule someI_ex)
 qed
 then show "\<exists>w. \<forall>i\<in>I. w i\<in>P i" by (rule exI[of _ ?w])
qed

lemma witness_family:
 "(\<forall>i\<in>I. P i\<noteq>{}) \<longleftrightarrow> (\<exists>w. \<forall>i\<in>I. w i\<in>P i)"
 using product_nonempty[of I P] by blast

lemma supplied_image:
 assumes fi: "finite I" and typed: "\<And>i. i\<in>I \<Longrightarrow> P i\<subseteq>S"
 and hw: "\<And>i. i\<in>I \<Longrightarrow> w i\<in>P i"
 shows "w ` I\<subseteq>S \<and> finite (w ` I) \<and> card (w ` I)\<le>card I \<and>
   (\<forall>i\<in>I. (w ` I) \<inter> P i\<noteq>{})"
proof -
 have sub: "w ` I\<subseteq>S" using typed hw by blast
 have fin: "finite (w ` I)" by (rule finite_imageI[OF fi])
 have bound: "card (w ` I)\<le>card I" by (rule card_image_le[OF fi])
 have hit: "\<forall>i\<in>I. (w ` I) \<inter> P i\<noteq>{}"
 proof
  fix i assume i: "i\<in>I"
  have "w i\<in>w ` I" by (rule imageI[OF i])
  then show "(w ` I) \<inter> P i\<noteq>{}" using hw[OF i] by blast
 qed
 show ?thesis using sub fin bound hit by blast
qed

ML \<open>
val roots = @{thms product_nonempty witness_family supplied_image};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
