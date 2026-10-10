theory Core_Native_Law_Failure
  imports "LCTR_Core_Native_Law_Components.Core_Native_Law_Components"
begin
lemma law_node_UNIV: "(UNIV::law_node set)={Law1,Law2,Law3,Law4,Law5}"
  using law_node.exhaust by auto
lemma law_node_finite: "finite(UNIV::law_node set)"
  by (simp add: law_node_UNIV)
lemma law_node_card: "card(UNIV::law_node set)=5"
  by (simp add: law_node_UNIV)

locale selected_law_family =
  fixes S :: "'e set" and datum :: "'e\<Rightarrow>('t,'a,'x,'y) law_family"
begin
definition total_condition where "total_condition e i \<longleftrightarrow> e\<in>S \<and> condition(datum e)i"
definition failure where "failure e \<longleftrightarrow> e\<in>S \<and> \<not>(\<forall>i. total_condition e i)"
definition ancestor_all where "ancestor_all e i \<longleftrightarrow> (\<forall>j. ancestor j i \<longrightarrow> total_condition e j)"
definition minimal_class where "minimal_class e i \<longleftrightarrow> e\<in>S \<and> ancestor_all e i \<and> \<not>total_condition e i"

lemma selected_condition_exact:
  "e\<in>S \<Longrightarrow> (total_condition e i \<longleftrightarrow> condition(datum e)i)"
  by (simp add: total_condition_def)
lemma outside_selection_not_failure:
  "e\<notin>S \<Longrightarrow> (\<forall>i. \<not>total_condition e i) \<and> \<not>failure e \<and> (\<forall>i. \<not>minimal_class e i)"
  by (simp add: total_condition_def failure_def minimal_class_def)
lemma failure_on_selected_datum:
  "e\<in>S \<Longrightarrow> (failure e \<longleftrightarrow> \<not>all_conditions(datum e))"
  by (simp add: failure_def total_condition_def all_conditions_exact)
lemma ancestors_explicit:
  "ancestor_all e i \<longleftrightarrow>
    (if i=Law3 then total_condition e Law1
     else if i=Law5 then total_condition e Law1 \<and> total_condition e Law3 else True)"
  by (cases i) (simp_all add: ancestor_all_def forall_nodes ancestor_def edge_def)
lemma failure_covered_by_minimal_classes:
  "failure e \<longleftrightarrow> (\<exists>i. minimal_class e i)"
  using failure_cover[of "e\<in>S" "total_condition e"]
  unfolding failure_def minimal_class_def ancestor_all_def fails_def minimal_def ancestors_hold_def .
lemma minimal_classes_antichain:
  "minimal_class e i \<Longrightarrow> minimal_class e j \<Longrightarrow>
    \<not>tranclp edge i j \<and> \<not>tranclp edge j i"
  unfolding minimal_class_def ancestor_all_def
  using minimal_antichain[of "e\<in>S" "total_condition e" i j]
  unfolding minimal_def ancestors_hold_def by blast
lemma failure_domain_union: "{e. failure e}=(\<Union>i. {e. minimal_class e i})"
  using failure_covered_by_minimal_classes by auto
lemma finite_witness_set:
  "\<exists>W\<subseteq>S. finite W \<and> card W\<le>5 \<and>
    (\<forall>i. (\<exists>e. minimal_class e i) \<longleftrightarrow> (\<exists>e\<in>W. minimal_class e i))"
proof -
  let ?active = "{i. \<exists>e. minimal_class e i}"
  let ?pick = "\<lambda>i. SOME e. minimal_class e i"
  let ?W = "image ?pick ?active"
  have finite_active: "finite ?active"
    by (rule finite_subset[OF subset_UNIV law_node_finite])
  have bound: "card ?active\<le>5"
    using card_mono[OF law_node_finite, of ?active] law_node_card by simp
  have chosen: "\<And>i. i\<in>?active \<Longrightarrow> minimal_class(?pick i)i"
    by (rule someI_ex) simp
  have sub: "?W\<subseteq>S" using chosen unfolding minimal_class_def by blast
  have fin: "finite ?W" by (rule finite_imageI[OF finite_active])
  have card: "card ?W\<le>5" using card_image_le[OF finite_active, of ?pick] bound by linarith
  have meets: "\<forall>i. (\<exists>e. minimal_class e i) \<longleftrightarrow> (\<exists>e\<in>?W. minimal_class e i)"
  proof (intro allI iffI)
    fix i assume hi: "\<exists>e. minimal_class e i"
    have i: "i\<in>?active" using hi by simp
    show "\<exists>e\<in>?W. minimal_class e i" using imageI[OF i, of ?pick] chosen[OF i] by blast
  next
    fix i assume "\<exists>e\<in>?W. minimal_class e i"
    then show "\<exists>e. minimal_class e i" by blast
  qed
  show ?thesis using sub fin card meets by blast
qed
end
context native_law_context
begin
lemma native_failure_exact:
  "e\<in>S \<Longrightarrow>
    (selected_law_family.failure S (\<lambda>_. native_family A a allowed faithful) e \<longleftrightarrow>
      \<not>all_conditions(native_family A a allowed faithful))"
proof -
  assume e: "e\<in>S"
  interpret f: selected_law_family S "\<lambda>_. native_family A a allowed faithful" .
  show ?thesis by (rule f.failure_on_selected_datum[OF e])
qed
end
ML \<open>
val roots = @{thms selected_law_family.selected_condition_exact
 selected_law_family.outside_selection_not_failure selected_law_family.failure_on_selected_datum
 selected_law_family.ancestors_explicit selected_law_family.failure_covered_by_minimal_classes
 selected_law_family.minimal_classes_antichain selected_law_family.failure_domain_union
 selected_law_family.finite_witness_set native_law_context.native_failure_exact};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
