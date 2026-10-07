theory Core_Record_Codes
  imports "LCTR_Core_Trajectory_Descent.Core_Trajectory_Descent"
begin

locale record_codes =
  fixes C :: "'c set" and D :: "'d set" and B :: "'b set"
    and R :: "('c \<times> 'd \<times> 'b) set"
    and Bind :: "(('c \<times> 'd \<times> 'b) \<times> ('c \<times> 'd \<times> 'b)) set"
    and window :: "'d \<Rightarrow> 'w" and field :: "'d \<Rightarrow> 'p"
    and sequence :: "'d \<Rightarrow> 'n"
begin

definition code where "code r = (window r, field r, sequence r)"
definition record_values where "record_values = image code D"
abbreviation EC where "EC \<equiv> least_equiv C (generator_c C D B R Bind)"
abbreviation EB where "EB \<equiv> least_equiv B (generator_b C D B R Bind)"

definition pair_records where
  "pair_records = {p. \<exists>c\<in>C. \<exists>r\<in>D. \<exists>b\<in>B.
    (c,r,b)\<in>R \<and> ((Image EC {c},Image EB {b}),code r)=p}"
definition time_records where
  "time_records = image (\<lambda>p. (fst (fst p),snd p)) pair_records"
definition state_records where
  "state_records = image (\<lambda>p. (snd (fst p),snd p)) pair_records"

lemma record_code_components:
  "code r = (window r,field r,sequence r)"
  by (simp add: code_def)

lemma pair_source_membership:
  assumes "c\<in>C" "r\<in>D" "b\<in>B" "(c,r,b)\<in>R"
  shows "((Image EC {c},Image EB {b}),code r)\<in>pair_records"
  using assms unfolding pair_records_def by blast

lemma pair_records_typed:
  assumes "p\<in>pair_records"
  shows "fst p \<in> image_rel EC EB (source_rel C D B R) \<and> snd p \<in> record_values"
proof -
  obtain c r b where a: "c\<in>C" "r\<in>D" "b\<in>B" "(c,r,b)\<in>R"
    and p: "p=((Image EC {c},Image EB {b}),code r)"
    using assms unfolding pair_records_def by blast
  have src: "(c,b)\<in>source_rel C D B R"
    using a unfolding source_rel_def by blast
  have trj: "(Image EC {c},Image EB {b})\<in>image_rel EC EB (source_rel C D B R)"
    unfolding image_rel_def by (rule image_eqI[where x="(c,b)"]) (simp, rule src)
  have val: "code r\<in>record_values"
    using a(2) unfolding record_values_def by blast
  show ?thesis using trj val p by simp
qed

lemma time_projection_exact:
  "(t,v)\<in>time_records \<longleftrightarrow> (\<exists>s. ((t,s),v)\<in>pair_records)"
  unfolding time_records_def by force

lemma state_projection_exact:
  "(s,v)\<in>state_records \<longleftrightarrow> (\<exists>t. ((t,s),v)\<in>pair_records)"
  unfolding state_records_def by force

lemma projected_record_values_typed:
  "(\<forall>p\<in>time_records. snd p\<in>record_values) \<and>
   (\<forall>p\<in>state_records. snd p\<in>record_values)"
  using pair_records_typed unfolding time_records_def state_records_def by auto

lemma record_values_not_forced_single:
  assumes "c\<in>C" "b\<in>B" "r\<in>D" "s\<in>D"
    and "(c,r,b)\<in>R" "(c,s,b)\<in>R" "code r \<noteq> code s"
  shows "\<exists>p v w. (p,v)\<in>pair_records \<and> (p,w)\<in>pair_records \<and> v\<noteq>w"
proof -
  have a: "((Image EC {c},Image EB {b}),code r)\<in>pair_records"
    by (rule pair_source_membership[OF assms(1,3,2,5)])
  have b: "((Image EC {c},Image EB {b}),code s)\<in>pair_records"
    by (rule pair_source_membership[OF assms(1,4,2,6)])
  show ?thesis using a b assms(7) by blast
qed

lemma empty_source_records:
  assumes "\<And>c r b. c\<in>C \<Longrightarrow> r\<in>D \<Longrightarrow> b\<in>B \<Longrightarrow> (c,r,b)\<notin>R"
  shows "pair_records = {}"
  using assms unfolding pair_records_def by blast

end

ML \<open>
val roots = @{thms record_codes.record_code_components record_codes.pair_source_membership record_codes.pair_records_typed record_codes.time_projection_exact record_codes.state_projection_exact record_codes.projected_record_values_typed record_codes.record_values_not_forced_single record_codes.empty_source_records};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
