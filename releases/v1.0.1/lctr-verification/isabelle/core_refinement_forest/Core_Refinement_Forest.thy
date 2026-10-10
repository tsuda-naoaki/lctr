theory Core_Refinement_Forest
  imports LCTR_Core_Comparison_Failure.Core_Comparison_Failure
begin

locale refinement_forest =
  fixes children :: "'n\<Rightarrow>'c set" and descend :: "'n\<Rightarrow>'c\<Rightarrow>'n"
    and region :: "'n\<Rightarrow>'e set"
  assumes child_subset: "\<And>n i. i\<in>children n \<Longrightarrow> region (descend n i)\<subseteq>region n"
begin
definition covered where "covered n = (\<Union>i\<in>children n. region (descend n i))"
definition unrefined where "unrefined n = region n - covered n"
definition child_edge where "child_edge n m = (\<exists>i\<in>children n. m=descend n i)"

lemma covered_subset: "covered n\<subseteq>region n"
  using child_subset unfolding covered_def by blast
lemma node_decomposition:
  "region n=covered n\<union>unrefined n \<and> covered n\<inter>unrefined n={}"
  using covered_subset[of n] unfolding unrefined_def by auto
lemma child_family_with_remainder:
  assumes pairwise: "\<forall>i\<in>children n. \<forall>j\<in>children n. i\<noteq>j \<longrightarrow>
    region (descend n i)\<inter>region (descend n j)={}"
  shows "(\<forall>i\<in>children n. \<forall>j\<in>children n. i\<noteq>j \<longrightarrow>
    region (descend n i)\<inter>region (descend n j)={}) \<and>
    (\<forall>i\<in>children n. region (descend n i)\<inter>unrefined n={})"
  using pairwise unfolding unrefined_def covered_def by blast
lemma ancestor_inclusion:
  assumes path: "rtranclp child_edge n m"
  shows "region m\<subseteq>region n"
  using path
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  have child: "region z\<subseteq>region y"
    using step.hyps(2) child_subset unfolding child_edge_def by blast
  show ?case by (rule subset_trans[OF child step.IH])
qed
end

lemma snapshot_monotonicity:
  fixes embed :: "'j\<Rightarrow>'k" and r :: "'j\<Rightarrow>'e set" and s :: "'k\<Rightarrow>'e set"
  assumes maps: "\<And>i. i\<in>I \<Longrightarrow> embed i\<in>J"
    and same: "\<And>i. i\<in>I \<Longrightarrow> r i=s (embed i)"
  shows "(\<Union>i\<in>I. r i)\<subseteq>(\<Union>j\<in>J. s j) \<and>
    P-(\<Union>j\<in>J. s j)\<subseteq>P-(\<Union>i\<in>I. r i)"
proof -
  have sub: "(\<Union>i\<in>I. r i)\<subseteq>(\<Union>j\<in>J. s j)"
    using maps same by blast
  show ?thesis using sub by blast
qed

lemma snapshot_generic_nat_bool_control:
  "(\<And>n::nat. n\<in>I \<Longrightarrow> f n\<in>J) \<Longrightarrow>
   (\<And>n::nat. n\<in>I \<Longrightarrow> r n=s (f n::bool)) \<Longrightarrow>
   (\<Union>n\<in>I. r n)\<subseteq>(\<Union>b\<in>J. s b) \<and> P-(\<Union>b\<in>J. s b)\<subseteq>P-(\<Union>n\<in>I. r n)"
  by (rule snapshot_monotonicity[where embed=f]) assumption+

lemma snapshot_generic_bool_nat_control:
  "(\<And>b::bool. b\<in>I \<Longrightarrow> f b\<in>J) \<Longrightarrow>
   (\<And>b::bool. b\<in>I \<Longrightarrow> r b=s (f b::nat)) \<Longrightarrow>
   (\<Union>b\<in>I. r b)\<subseteq>(\<Union>n\<in>J. s n) \<and> P-(\<Union>n\<in>J. s n)\<subseteq>P-(\<Union>b\<in>I. r b)"
  by (rule snapshot_monotonicity[where embed=f]) assumption+

datatype ('i,'j,'k) node = Root 'i | First 'i 'j | Second 'i 'j 'k
fun depth :: "('i,'j,'k) node\<Rightarrow>nat" where
  "depth (Root i)=0" | "depth (First i j)=1" | "depth (Second i j k)=2"

fun child_indices :: "'i set\<Rightarrow>('i\<Rightarrow>'j set)\<Rightarrow>('i\<Rightarrow>'j\<Rightarrow>'k set)
    \<Rightarrow>('i,'j,'k) node\<Rightarrow>('j+'k) set" where
  "child_indices I J K (Root i) = (if i\<in>I then image Inl (J i) else {})"
| "child_indices I J K (First i j) = (if i\<in>I \<and> j\<in>J i then image Inr (K i j) else {})"
| "child_indices I J K (Second i j k) = {}"

fun child_node :: "('i,'j,'k) node\<Rightarrow>('j+'k)\<Rightarrow>('i,'j,'k) node" where
  "child_node (Root i) (Inl j)=First i j"
| "child_node (Root i) (Inr k)=Root i"
| "child_node (First i j) (Inr k)=Second i j k"
| "child_node (First i j) (Inl l)=First i j"
| "child_node (Second i j k) c=Second i j k"

fun node_region :: "('i\<Rightarrow>'e set)\<Rightarrow>('i\<Rightarrow>'j\<Rightarrow>'e set)
    \<Rightarrow>('i\<Rightarrow>'j\<Rightarrow>'k\<Rightarrow>'e set)\<Rightarrow>('i,'j,'k) node\<Rightarrow>'e set" where
  "node_region r0 r1 r2 (Root i)=r0 i"
| "node_region r0 r1 r2 (First i j)=r1 i j"
| "node_region r0 r1 r2 (Second i j k)=r2 i j k"

locale two_level_regions =
  fixes I :: "'i set" and J :: "'i\<Rightarrow>'j set" and K :: "'i\<Rightarrow>'j\<Rightarrow>'k set"
    and r0 :: "'i\<Rightarrow>'e set" and r1 :: "'i\<Rightarrow>'j\<Rightarrow>'e set"
    and r2 :: "'i\<Rightarrow>'j\<Rightarrow>'k\<Rightarrow>'e set"
  assumes first_sub: "\<And>i j. i\<in>I \<Longrightarrow> j\<in>J i \<Longrightarrow> r1 i j\<subseteq>r0 i"
    and second_sub: "\<And>i j k. i\<in>I \<Longrightarrow> j\<in>J i \<Longrightarrow> k\<in>K i j \<Longrightarrow> r2 i j k\<subseteq>r1 i j"
begin
sublocale F: refinement_forest "child_indices I J K" child_node "node_region r0 r1 r2"
proof
  fix n l
  assume l: "l\<in>child_indices I J K n"
  show "node_region r0 r1 r2 (child_node n l)\<subseteq>node_region r0 r1 r2 n"
    using l by (cases n; cases l;
      auto dest: first_sub[THEN subsetD] second_sub[THEN subsetD] split: if_splits)
qed

lemma two_level_child_depth:
  "F.child_edge n m \<Longrightarrow> depth m=depth n+1"
  unfolding F.child_edge_def
  by (cases n; auto split: if_splits)

lemma two_level_acyclic: "\<not>tranclp F.child_edge n n"
proof -
  have increases: "\<And>n m. tranclp F.child_edge n m \<Longrightarrow> depth n<depth m"
  proof -
    fix n m
    assume path: "tranclp F.child_edge n m"
    then show "depth n<depth m"
    proof (induction rule: tranclp_induct)
      case (base y)
      then show ?case using two_level_child_depth by fastforce
    next
      case (step y z)
      have "depth z=depth y+1" by (rule two_level_child_depth[OF step.hyps(2)])
      then show ?case using step.IH by arith
    qed
  qed
  show ?thesis using increases[of n n] less_irrefl by blast
qed

lemma two_level_leaf:
  "F.covered (Second i j k)={} \<and> F.unrefined (Second i j k)=r2 i j k"
  by (simp add: F.covered_def F.unrefined_def)
end

definition comparison_root where
  "comparison_root f e c i = {x. run (f x) (e x) (c x) 40 (cmp_token i)=Failed}"

lemma native_comparison_forest_laws:
  fixes regions covered unrefined forest_edges
  assumes first_sub: "\<And>i j. i\<in>cmp_indices \<Longrightarrow> j\<in>J i \<Longrightarrow>
      r1 i j\<subseteq>comparison_root f e c i"
    and second_sub: "\<And>i j k. i\<in>cmp_indices \<Longrightarrow> j\<in>J i \<Longrightarrow> k\<in>K i j \<Longrightarrow>
      r2 i j k\<subseteq>r1 i j"
  defines "regions \<equiv> node_region (comparison_root f e c) r1 r2"
    and "covered \<equiv> refinement_forest.covered (child_indices cmp_indices J K) child_node regions"
    and "unrefined \<equiv> refinement_forest.unrefined (child_indices cmp_indices J K) child_node regions"
    and "forest_edges \<equiv> refinement_forest.child_edge (child_indices cmp_indices J K) child_node"
  shows "(\<forall>n. regions n=covered n\<union>unrefined n \<and> covered n\<inter>unrefined n={}) \<and>
    (\<forall>n m. rtranclp forest_edges n m \<longrightarrow> regions m\<subseteq>regions n)"
proof -
  interpret N: two_level_regions cmp_indices J K "comparison_root f e c" r1 r2
    by unfold_locales (fact first_sub, fact second_sub)
  have decomp: "\<forall>n. regions n=covered n\<union>unrefined n \<and> covered n\<inter>unrefined n={}"
    unfolding regions_def covered_def unrefined_def by (intro allI, rule N.F.node_decomposition)
  have ancestors: "\<forall>n m. rtranclp forest_edges n m \<longrightarrow> regions m\<subseteq>regions n"
    unfolding regions_def forest_edges_def by (intro allI impI, rule N.F.ancestor_inclusion, assumption)
  show ?thesis by (intro conjI; fact)
qed

ML \<open>
val snapshot_variables = Term.add_vars (Thm.prop_of @{thm snapshot_monotonicity}) [];
val _ = (case AList.lookup (op =) snapshot_variables ("embed", 0) of
    SOME (Type ("fun", [TVar a, TVar b])) =>
      if a <> b then () else error "Snapshot map domain and codomain were identified"
  | _ => error "Snapshot comparison lacks an arbitrary polymorphic map");
val roots = @{thms refinement_forest.covered_subset refinement_forest.node_decomposition
  refinement_forest.child_family_with_remainder refinement_forest.ancestor_inclusion
  snapshot_monotonicity two_level_regions.two_level_child_depth
  two_level_regions.two_level_acyclic two_level_regions.two_level_leaf
  native_comparison_forest_laws};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
