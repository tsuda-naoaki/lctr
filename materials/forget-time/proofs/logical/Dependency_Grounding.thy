theory Dependency_Grounding
  imports Complex_Main
begin

inductive grounded :: "'a set \<Rightarrow> ('a set \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> bool"
  for B R where
  initial: "v \<in> B \<Longrightarrow> grounded B R v"
| inference: "finite P \<Longrightarrow> (P,v) \<in> R \<Longrightarrow>
    (\<And>p. p \<in> P \<Longrightarrow> grounded B R p) \<Longrightarrow> grounded B R v"

fun reached :: "'a set \<Rightarrow> ('a set \<times> 'a) set \<Rightarrow> nat \<Rightarrow> 'a set" where
  "reached B R 0 = B"
| "reached B R (Suc n) = reached B R n \<union>
    {v. \<exists>P. finite P \<and> (P,v) \<in> R \<and> P \<subseteq> reached B R n}"

lemma reached_mono:
  "m \<le> n \<Longrightarrow> reached B R m \<subseteq> reached B R n"
  by (induction n) (auto simp: le_Suc_eq)

lemma finite_common_stage:
  assumes "finite P" "\<And>p. p \<in> P \<Longrightarrow> \<exists>n. p \<in> reached B R n"
  shows "\<exists>n. P \<subseteq> reached B R n"
  using assms
proof (induction P rule: finite_induct)
  case empty
  then show ?case by auto
next
  case (insert x P)
  obtain m where m: "P \<subseteq> reached B R m" using insert by auto
  obtain n where n: "x \<in> reached B R n" using insert by auto
  have "insert x P \<subseteq> reached B R (max m n)"
    using m n reached_mono[of m "max m n" B R]
      reached_mono[of n "max m n" B R] by auto
  then show ?case by blast
qed

theorem grounded_iff_reached:
  "grounded B R v \<longleftrightarrow> (\<exists>n. v \<in> reached B R n)"
proof
  assume "grounded B R v"
  then show "\<exists>n. v \<in> reached B R n"
  proof (induction rule: grounded.induct)
    case (initial v)
    then show ?case by (metis reached.simps(1))
  next
    case (inference P v)
    obtain n where "P \<subseteq> reached B R n"
      using finite_common_stage[OF inference.hyps(1) inference.IH] by blast
    then have "v \<in> reached B R (Suc n)" using inference by auto
    then show ?case by blast
  qed
next
  assume "\<exists>n. v \<in> reached B R n"
  then obtain n where "v \<in> reached B R n" by blast
  then show "grounded B R v"
  proof (induction n arbitrary: v)
    case 0
    then show ?case by (simp add: grounded.initial)
  next
    case (Suc n)
    show ?case
    proof (cases "v \<in> reached B R n")
      case True
      then show ?thesis by (rule Suc.IH)
    next
      case False
      obtain P where P: "finite P" "(P,v) \<in> R" "P \<subseteq> reached B R n"
        using Suc.prems False by auto
      show ?thesis by (rule grounded.inference[OF P(1,2)]) (use P(3) Suc.IH in auto)
    qed
  qed
qed

theorem ungrounded_cycle:
  assumes "B \<inter> U = {}"
    "\<And>P v. (P,v) \<in> R \<Longrightarrow> v \<in> U \<Longrightarrow> P \<inter> U \<noteq> {}"
    "grounded B R v"
  shows "v \<notin> U"
  using assms(3)
proof (induction rule: grounded.induct)
  case (initial v)
  then show ?case using assms(1) by blast
next
  case (inference P v)
  then show ?case using assms(2) by blast
qed

lemma independent_alternative:
  assumes "finite P" "(P,v) \<in> R" "P \<subseteq> B"
  shows "grounded B R v"
  by (rule grounded.inference[OF assms(1,2)]; rule grounded.initial)
    (use assms(3) in blast)

lemma grounded_in_universe:
  assumes "B \<subseteq> V" "\<And>P v. (P,v) \<in> R \<Longrightarrow> v \<in> V"
    "grounded B R v"
  shows "v \<in> V"
  using assms(3) by (induction rule: grounded.induct) (use assms in auto)

theorem finite_reachability_fixed_point:
  assumes "finite V" "B \<subseteq> V"
    "\<And>P v. (P,v) \<in> R \<Longrightarrow> v \<in> V"
  shows "\<exists>n. reached B R n = {v. grounded B R v} \<and>
    (\<forall>m\<ge>n. reached B R m = reached B R n)"
proof -
  let ?G = "{v. grounded B R v}"
  have "?G \<subseteq> V"
  proof
    fix v assume "v \<in> ?G"
    then have "grounded B R v" by simp
    show "v \<in> V" by (rule grounded_in_universe[OF assms(2,3) \<open>grounded B R v\<close>])
  qed
  then have fin: "finite ?G" using assms(1) finite_subset by blast
  have "\<And>p. p \<in> ?G \<Longrightarrow> \<exists>n. p \<in> reached B R n"
    by (simp add: grounded_iff_reached)
  then obtain n where inc: "?G \<subseteq> reached B R n"
    using finite_common_stage[OF fin] by blast
  have sub: "\<And>m. reached B R m \<subseteq> ?G"
    by (auto simp: grounded_iff_reached)
  have eq: "reached B R n = ?G" using inc sub by blast
  have "\<And>m. n \<le> m \<Longrightarrow> reached B R m = reached B R n"
  proof -
    fix m assume nm: "n \<le> m"
    have "reached B R n \<subseteq> reached B R m" by (rule reached_mono[OF nm])
    then show "reached B R m = reached B R n" using sub[of m] eq by blast
  qed
  then show ?thesis using eq by blast
qed

datatype 'a premise_tree = Premise 'a | Inference 'a "'a premise_tree list"

fun leaves :: "'a premise_tree \<Rightarrow> 'a set" where
  "leaves (Premise p) = {p}"
| "leaves (Inference v ts) = \<Union>(leaves ` set ts)"

fun substitute :: "('a \<Rightarrow> 'a premise_tree) \<Rightarrow> 'a premise_tree \<Rightarrow> 'a premise_tree" where
  "substitute f (Premise p) = f p"
| "substitute f (Inference v ts) = Inference v (map (substitute f) ts)"

theorem substitution_leaves:
  "leaves (substitute f t) = \<Union>(leaves ` f ` leaves t)"
  by (induction t) auto

corollary selected_substitution_leaves:
  "leaves (substitute (\<lambda>p. if p \<in> S then f p else Premise p) t) =
    (leaves t - S) \<union> \<Union>(leaves ` f ` (leaves t \<inter> S))"
  by (simp add: substitution_leaves) auto

end
