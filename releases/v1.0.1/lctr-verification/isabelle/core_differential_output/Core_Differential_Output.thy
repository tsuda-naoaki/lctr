theory Core_Differential_Output
  imports LCTR_Core_Differential_Selected.Core_Differential_Selected
begin

record 'e output_data =
  dag :: "node\<Rightarrow>node\<Rightarrow>bool"
  parents :: "node\<Rightarrow>'e set"
  remainders :: "node\<Rightarrow>'e set"
  signatures :: "'e\<Rightarrow>node\<Rightarrow>bool"

context matching_differential
begin

definition parent where "parent S i={ev\<in>S. nativeMinimal ev i}"
definition "output" where
  "output S children=\<lparr>dag=edge, parents=parent S,
    remainders=(\<lambda>i. parent S i-\<Union>(children i)), signatures=nativeMinimal\<rparr>"
definition represents :: "'e set\<Rightarrow>(node\<Rightarrow>'e set set)\<Rightarrow>'e output_data\<Rightarrow>bool" where
  "represents S children out=(dag out=edge \<and> parents out=parent S \<and>
    remainders out=(\<lambda>i. parent S i-\<Union>(children i)) \<and> signatures out=nativeMinimal)"

lemma output_unique: "\<exists>!out. represents S children out"
proof (rule ex1I[of _ "output S children"])
  show "represents S children (output S children)" by (simp add: represents_def output_def)
next
  fix out assume "represents S children out"
  then show "out=output S children"
    by (cases out) (simp add: represents_def output_def)
qed

lemma parent_signature_correspondence:
  "ev\<in>parents (output S children) i = (ev\<in>S \<and> signatures (output S children) ev i)"
  by (simp add: output_def parent_def)

lemma output_parent_cover:
  "(\<Union>i. parents (output S children) i)={ev\<in>S. nativeFailure ev}"
  using native_failure_cover by (auto simp: output_def parent_def)

lemma remainder_subset_parent:
  "remainders (output S children) i\<subseteq>parents (output S children) i"
  by (auto simp: output_def)

lemma children_and_remainder:
  assumes sub: "\<And>i C. C\<in>children i \<Longrightarrow> C\<subseteq>parent S i"
  shows "parents (output S children) i=\<Union>(children i)\<union>remainders (output S children) i \<and>
    \<Union>(children i)\<inter>remainders (output S children) i={}"
  using sub by (auto simp: output_def)

lemma output_signature_nonzero:
  "(signatures (output S children) ev\<noteq>(\<lambda>_. False))=nativeFailure ev"
  by (simp add: output_def fun_eq_iff native_failure_cover)

lemma parent_indices_antichain:
  assumes hi: "ev\<in>parents (output S children) i"
    and hj: "ev\<in>parents (output S children) j"
  shows "\<not>tranclp (dag (output S children)) i j \<and> \<not>tranclp (dag (output S children)) j i"
  using native_minimal_antichain hi hj by (auto simp: output_def parent_def)

end

ML \<open>
val roots = @{thms matching_differential.output_unique matching_differential.parent_signature_correspondence
  matching_differential.output_parent_cover matching_differential.remainder_subset_parent
  matching_differential.children_and_remainder matching_differential.output_signature_nonzero
  matching_differential.parent_indices_antichain};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
