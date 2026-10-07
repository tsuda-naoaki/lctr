theory Core_Engineering_Input_Burden
  imports "../core_audit_state_transport/Core_Audit_State_Transport"
begin

datatype tag = View | RecordConfig | Invasiveness | Communication | CountStep | Stability
  | CellWidth | Discernibility | Coupling | Trajectory | Observable | LawTest | DifferentialTest
definition all_tags where
  "all_tags = [View,RecordConfig,Invasiveness,Communication,CountStep,Stability,
    CellWidth,Discernibility,Coupling,Trajectory,Observable,LawTest,DifferentialTest]"
lemma tag_count: "length all_tags=13" by (simp add: all_tags_def)
lemma tag_distinct: "distinct all_tags" by (simp add: all_tags_def)
lemma tag_complete: "t\<in>set all_tags" by (cases t) (simp_all add: all_tags_def)

definition value_type where
  "value_type v0 v1 v2 v3 other t = (case t of
    View\<Rightarrow>v0 | RecordConfig\<Rightarrow>v1 | Invasiveness\<Rightarrow>v2 |
    Communication\<Rightarrow>v3 | _\<Rightarrow>other t)"
definition basic_range where "basic_range f domain=f ` domain"
lemma view_origin:
  "v\<in>value_type (basic_range f domain) v1 v2 v3 other View \<Longrightarrow> \<exists>x\<in>domain. f x=v"
  by (auto simp: value_type_def basic_range_def)
lemma config_origin:
  "v\<in>value_type v0 (basic_range f domain) v2 v3 other RecordConfig \<Longrightarrow> \<exists>x\<in>domain. f x=v"
  by (auto simp: value_type_def basic_range_def)
lemma invasion_origin:
  "v\<in>value_type v0 v1 (basic_range f domain) v3 other Invasiveness \<Longrightarrow> \<exists>x\<in>domain. f x=v"
  by (auto simp: value_type_def basic_range_def)
lemma communication_origin:
  "v\<in>value_type v0 v1 v2 (basic_range f domain) other Communication \<Longrightarrow> \<exists>x\<in>domain. f x=v"
  by (auto simp: value_type_def basic_range_def)
record ('r,'v,'c) audit_input =
  references :: "'r set"
  tag_of :: "'r\<Rightarrow>tag"
  value_types :: "tag\<Rightarrow>'v set"
  measure :: "'r\<Rightarrow>'v"
  certificate :: 'c
definition input_typed where
  "input_typed d = (\<forall>r\<in>references d. measure d r\<in>value_types d (tag_of d r))"
lemma all_references_typed:
  "input_typed d \<Longrightarrow> r\<in>references d \<Longrightarrow>
    \<exists>v\<in>value_types d (tag_of d r). measure d r=v"
  unfolding input_typed_def by blast
lemma range_not_ambient:
  "y\<notin>basic_range f domain \<Longrightarrow> \<not>(\<exists>v\<in>basic_range f domain. v=y)"
  by simp

definition bulk_tags where
  "bulk_tags={View,RecordConfig,Invasiveness,CountStep,Stability,CellWidth,Discernibility}"
definition following_tags where "following_tags=bulk_tags\<union>{Communication,Coupling}"
lemma bulk_tags_exact:
  "t\<in>bulk_tags = (t=View \<or> t=RecordConfig \<or> t=Invasiveness \<or> t=CountStep \<or>
    t=Stability \<or> t=CellWidth \<or> t=Discernibility)"
  by (simp add: bulk_tags_def)
lemma following_tags_exact:
  "t\<in>following_tags = (t\<in>bulk_tags \<or> t=Communication \<or> t=Coupling)"
  by (auto simp: following_tags_def)
lemma four_other_tags_excluded:
  "Trajectory\<notin>following_tags \<and> Observable\<notin>following_tags \<and>
    LawTest\<notin>following_tags \<and> DifferentialTest\<notin>following_tags"
  by (simp add: bulk_tags_def following_tags_def)

record ('r,'e,'t) configuration =
  verified :: "nat\<Rightarrow>'e set"
  refs :: "'e\<Rightarrow>'r set"
  tag :: "'r\<Rightarrow>tag"
  state :: "nat\<Rightarrow>'e\<Rightarrow>audit_status"
  target :: "'e\<Rightarrow>'t"
definition has_ref where
  "has_ref d allowed e = (\<exists>r\<in>refs d e. tag d r\<in>allowed)"
definition evidence where
  "evidence d allowed k = {e\<in>verified d k. has_ref d allowed e}"
definition indexed where
  "indexed d allowed = {(k,e). k<2 \<and> e\<in>evidence d allowed k}"
definition failed where
  "failed d allowed k = {e\<in>evidence d allowed k. state d k e=Fail}"
definition failing_union where
  "failing_union d allowed = {e. \<exists>k<2. e\<in>failed d allowed k}"
definition tokens where "tokens d allowed = target d ` failing_union d allowed"
definition burden where "burden K d allowed = K (tokens d allowed)"

lemma evidence_exact:
  "e\<in>evidence d allowed k = (e\<in>verified d k \<and> (\<exists>r\<in>refs d e. tag d r\<in>allowed))"
  by (simp add: evidence_def has_ref_def)
lemma indexed_exact:
  "k<2 \<Longrightarrow> (k,e)\<in>indexed d allowed = (e\<in>evidence d allowed k)"
  by (simp add: indexed_def)
lemma indexed_separates: "((0::nat),e)\<noteq>(1,e)" by simp
lemma failed_exact:
  "e\<in>failed d allowed k = (e\<in>verified d k \<and> has_ref d allowed e \<and> state d k e=Fail)"
  by (simp add: failed_def evidence_def)
lemma union_exact:
  "e\<in>failing_union d allowed = (\<exists>k<2. e\<in>failed d allowed k)"
  by (simp add: failing_union_def)
lemma tokens_exact:
  "t\<in>tokens d allowed = (\<exists>k<2. \<exists>e. e\<in>verified d k \<and>
    has_ref d allowed e \<and> state d k e=Fail \<and> target d e=t)"
  unfolding tokens_def failing_union_def failed_def evidence_def by blast
lemma nonfail_excluded:
  "state d k e\<noteq>Fail \<Longrightarrow> e\<notin>failed d allowed k"
  by (simp add: failed_def)
lemma outside_tags_excluded:
  "(\<forall>r\<in>refs d e. tag d r\<notin>allowed) \<Longrightarrow> e\<notin>evidence d allowed k"
  by (simp add: evidence_def has_ref_def)
lemma burden_exact: "burden K d allowed = K (tokens d allowed)"
  by (simp add: burden_def)
definition delta where "delta a b=(a-b)\<union>(b-a)"
lemma configuration_delta:
  "s\<in>delta (burden K d0 bulk_tags) (burden K d1 following_tags) =
    ((s\<in>K (tokens d0 bulk_tags) \<and> s\<notin>K (tokens d1 following_tags)) \<or>
     (s\<in>K (tokens d1 following_tags) \<and> s\<notin>K (tokens d0 bulk_tags)))"
  by (simp add: delta_def burden_def)

ML \<open>
val roots = @{thms tag_count tag_distinct tag_complete view_origin config_origin invasion_origin
  communication_origin all_references_typed range_not_ambient bulk_tags_exact following_tags_exact
  four_other_tags_excluded evidence_exact indexed_exact indexed_separates failed_exact union_exact
  tokens_exact nonfail_excluded outside_tags_excluded burden_exact configuration_delta};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
