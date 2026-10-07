theory Core_Finite_Class_Witness
 imports Main
begin

lemma finite_witness_set:
 fixes I :: "'i set" and S :: "'e set" and P :: "'e \<Rightarrow> 'i \<Rightarrow> bool"
 assumes fi: "finite I" and typed: "\<And>e i. i\<in>I \<Longrightarrow> P e i \<Longrightarrow> e\<in>S"
 shows "\<exists>W\<subseteq>S. finite W \<and> card W\<le>card I \<and>
   (\<forall>i\<in>I. (\<exists>e. P e i) \<longleftrightarrow> (\<exists>e\<in>W. P e i))"
proof -
 let ?A = "{i\<in>I. \<exists>e. P e i}"
 let ?p = "\<lambda>i. SOME e. P e i"
 let ?W = "?p ` ?A"
 have fa: "finite ?A" using fi by simp
 have chosen: "\<And>i. i\<in>?A \<Longrightarrow> P (?p i) i"
   by (rule someI_ex) simp
 have sub: "?W\<subseteq>S" using typed chosen by blast
 have fw: "finite ?W" by (rule finite_imageI[OF fa])
 have ca: "card ?A\<le>card I" by (rule card_mono[OF fi]) auto
 have cw: "card ?W\<le>card I" using card_image_le[OF fa, of ?p] ca by arith
 have hit: "\<forall>i\<in>I. (\<exists>e. P e i) \<longleftrightarrow> (\<exists>e\<in>?W. P e i)"
 proof (intro ballI iffI)
  fix i assume i: "i\<in>I" and ex: "\<exists>e. P e i"
  have ia: "i\<in>?A" using i ex by simp
  show "\<exists>e\<in>?W. P e i" using imageI[OF ia, of ?p] chosen[OF ia] by blast
 next
  fix i assume "i\<in>I" and "\<exists>e\<in>?W. P e i"
  then show "\<exists>e. P e i" by blast
 qed
 show ?thesis using sub fw cw hit by blast
qed

lemma two_members:
 assumes fin: "finite S"
 shows "2\<le>card S \<longleftrightarrow> (\<exists>i\<in>S. \<exists>j\<in>S. i\<noteq>j)"
proof
 assume c: "2\<le>card S"
 show "\<exists>i\<in>S. \<exists>j\<in>S. i\<noteq>j"
 proof (rule ccontr)
  assume no: "\<not>(\<exists>i\<in>S. \<exists>j\<in>S. i\<noteq>j)"
  have sub: "\<And>x. x\<in>S \<Longrightarrow> S\<subseteq>{x}" using no by blast
  have ne: "S\<noteq>{}" using c by auto
  then obtain x where x: "x\<in>S" by blast
  have fx: "finite {x}" by simp
  have "card S\<le>1" using card_mono[OF fx sub[OF x]] by simp
  then show False using c by arith
 qed
next
 assume ex: "\<exists>i\<in>S. \<exists>j\<in>S. i\<noteq>j"
 then obtain i j where ij: "i\<in>S" "j\<in>S" "i\<noteq>j" by blast
 have "card {i,j}\<le>card S" by (rule card_mono[OF fin]) (use ij in auto)
 then show "2\<le>card S" using ij by simp
qed

ML \<open>
val roots = @{thms finite_witness_set two_members};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
