theory Core_Refinement_Paths
  imports LCTR_Core_Refinement_Forest.Core_Refinement_Forest
begin

type_synonym ('i,'l) raw_path = "'i \<times> 'l list"
definition append_child where "append_child p l = (fst p,snd p @ [l])"
fun paths :: "'i set \<Rightarrow> (('i,'l) raw_path \<Rightarrow> 'l set) \<Rightarrow> nat \<Rightarrow> ('i,'l) raw_path set" where
  "paths I J 0 = (\<lambda>i. (i,[])) ` I"
| "paths I J (Suc n) = {p. \<exists>q\<in>paths I J n. \<exists>l\<in>J q. p=append_child q l}"
definition nodes where "nodes I J = (\<Union>n. paths I J n)"
definition truncated where "truncated I J m = {p. \<exists>n\<le>m. p\<in>paths I J n}"
definition tagged_truncated where "tagged_truncated I J m = {(n,p). n\<le>m \<and> p\<in>paths I J n}"

lemma path_zero: "(p\<in>paths I J 0) = (\<exists>i\<in>I. p=(i,[]))" by auto
lemma path_successor:
  "(p\<in>paths I J (Suc n)) = (\<exists>q\<in>paths I J n. \<exists>l\<in>J q. p=append_child q l)" by simp
lemma path_length: "p\<in>paths I J n \<Longrightarrow> length (snd p)=n"
proof (induction n arbitrary: p)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then obtain q l where q: "q\<in>paths I J n" and p: "p=append_child q l" by auto
  have "length (snd q)=n" by (rule Suc.IH[OF q])
  then show ?case by (simp add: p append_child_def)
qed
lemma unique_level: "p\<in>paths I J n \<Longrightarrow> p\<in>paths I J m \<Longrightarrow> n=m"
  using path_length by metis
lemma nodes_iff: "(p\<in>nodes I J) = (\<exists>n. p\<in>paths I J n)" by (simp add: nodes_def)
lemma truncated_exact:
  "(p\<in>truncated I J m) = (p\<in>nodes I J \<and> length (snd p)\<le>m)"
  unfolding truncated_def nodes_iff using path_length by blast
lemma tagged_truncation_injective: "inj_on snd (tagged_truncated I J m)"
proof (rule inj_onI)
  fix x y
  assume x: "x\<in>tagged_truncated I J m" and y: "y\<in>tagged_truncated I J m"
    and eq: "snd x=snd y"
  have xp: "snd x\<in>paths I J (fst x)" using x by (auto simp: tagged_truncated_def)
  have yp: "snd x\<in>paths I J (fst y)" using y eq by (auto simp: tagged_truncated_def)
  have first: "fst x=fst y" by (rule unique_level[OF xp yp])
  show "x=y" using first eq by (cases x; cases y; simp)
qed
lemma tagged_truncation_range: "snd ` tagged_truncated I J m = truncated I J m"
proof (rule set_eqI)
  fix p
  show "(p\<in>snd ` tagged_truncated I J m) = (p\<in>truncated I J m)"
  proof
    assume "p\<in>snd ` tagged_truncated I J m"
    then show "p\<in>truncated I J m" by (auto simp: tagged_truncated_def truncated_def)
  next
    assume "p\<in>truncated I J m"
    then obtain n where n: "n\<le>m" "p\<in>paths I J n" by (auto simp: truncated_def)
    have pair: "(n,p)\<in>tagged_truncated I J m" using n by (simp add: tagged_truncated_def)
    have "snd (n,p)\<in>snd ` tagged_truncated I J m" by (rule imageI[OF pair])
    then show "p\<in>snd ` tagged_truncated I J m" by simp
  qed
qed
lemma child_closure: "p\<in>nodes I J \<Longrightarrow> l\<in>J p \<Longrightarrow> append_child p l\<in>nodes I J"
proof -
  assume p: "p\<in>nodes I J" and l: "l\<in>J p"
  obtain n where n: "p\<in>paths I J n" using p by (auto simp: nodes_iff)
  have step: "append_child p l\<in>paths I J (Suc n)" using n l by auto
  show ?thesis unfolding nodes_iff by (rule exI[of _ "Suc n"], fact step)
qed

locale path_regions =
  fixes I :: "'i set" and J :: "('i,'l) raw_path \<Rightarrow> 'l set"
    and R :: "('i,'l) raw_path \<Rightarrow> 'e set"
  assumes within: "\<And>p l. p\<in>nodes I J \<Longrightarrow> l\<in>J p \<Longrightarrow> R (append_child p l)\<subseteq>R p"
begin
definition children_at where "children_at p = (if p\<in>nodes I J then J p else {})"
sublocale F: refinement_forest children_at append_child R
proof
  fix p l
  assume h: "l\<in>children_at p"
  have valid: "p\<in>nodes I J" and child: "l\<in>J p"
    using h by (auto simp: children_at_def split: if_splits)
  show "R (append_child p l)\<subseteq>R p" by (rule within[OF valid child])
qed
lemma child_edge_exact:
  "p\<in>nodes I J \<Longrightarrow> (F.child_edge p q) = (\<exists>l\<in>J p. q=append_child p l)"
  by (simp add: F.child_edge_def children_at_def)
lemma child_depth:
  "F.child_edge p q \<Longrightarrow> length (snd q)=length (snd p)+1"
  by (auto simp: F.child_edge_def children_at_def append_child_def split: if_splits)
lemma acyclic: "\<not>tranclp F.child_edge p p"
proof -
  have increases: "\<And>a b. tranclp F.child_edge a b \<Longrightarrow> length (snd a)<length (snd b)"
  proof -
    fix a b
    assume path: "tranclp F.child_edge a b"
    then show "length (snd a)<length (snd b)"
    proof (induction rule: tranclp_induct)
      case (base y)
      have "length (snd y)=length (snd a)+1" by (rule child_depth[OF base])
      then show ?case by arith
    next
      case (step y z)
      have "length (snd z)=length (snd y)+1" by (rule child_depth[OF step.hyps(2)])
      then show ?case using step.IH by arith
    qed
  qed
  show ?thesis using increases[of p p] by blast
qed
lemma node_decomposition:
  "R p=F.covered p \<union> F.unrefined p \<and> F.covered p \<inter> F.unrefined p={}"
  by (rule F.node_decomposition)
lemma ancestor_inclusion: "rtranclp F.child_edge p q \<Longrightarrow> R q\<subseteq>R p"
  by (rule F.ancestor_inclusion)
lemma empty_leaf: "J p={} \<Longrightarrow> F.covered p={} \<and> F.unrefined p=R p"
  by (simp add: F.covered_def F.unrefined_def children_at_def)
end

lemma arbitrary_depth_control: "((),replicate n ())\<in>paths UNIV (\<lambda>_. UNIV) n"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have eq: "((),replicate (Suc n) ()) = append_child ((),replicate n ()) ()"
    by (simp add: append_child_def replicate_append_same)
  show ?case using Suc.IH eq by auto
qed

ML \<open>
val roots = @{thms path_zero path_successor path_length unique_level nodes_iff
  truncated_exact tagged_truncation_injective tagged_truncation_range child_closure
  path_regions.child_edge_exact path_regions.child_depth path_regions.acyclic
  path_regions.node_decomposition path_regions.ancestor_inclusion path_regions.empty_leaf
  arbitrary_depth_control};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
