theory Global_Gluing_Isabelle
imports Main
begin

datatype expr = Comp nat | OperativeE | NotOperativeE | L7E | NotGE | ReprE nat | OutE nat nat

definition operative :: "bool => bool => bool" where
  "operative L7 G = (L7 \<and> G)"

definition comp_exprs :: "nat set => expr set" where
  "comp_exprs C = Comp ` C"

definition out_layer :: "(nat => nat set) => nat => expr set" where
  "out_layer Slots k = OutE k ` Slots k"

definition out_notG :: "(nat => nat set) => expr set" where
  "out_notG Slots = (\<Union>k\<in>{0..<4}. out_layer Slots k)"

definition req0 :: "nat set => expr set" where
  "req0 C = comp_exprs C \<union> {OperativeE}"

definition req_layer :: "nat set => (nat => nat set) => nat => expr set" where
  "req_layer C Slots k =
   (if k = 0 then req0 C
    else req0 C \<union> {ReprE k} \<union> (\<Union>j\<in>{0..<k}. out_layer Slots j))"

definition dep_repr :: "nat set => (nat => nat set) => (expr set * expr) set" where
  "dep_repr C Slots =
   {(req_layer C Slots k, y) |k y. k < 4 \<and> y \<in> out_layer Slots k}"

definition ctx_notG :: "nat set => expr set" where
  "ctx_notG C = comp_exprs C \<union> {L7E, NotGE, NotOperativeE}"

definition dep_closed :: "(expr set * expr) set => expr set => bool" where
  "dep_closed Dep S =
   (\<forall>A y. (A,y) \<in> Dep \<longrightarrow> A \<subseteq> S \<longrightarrow> y \<in> S)"

definition gen_closure :: "(expr set * expr) set => expr set => expr set" where
  "gen_closure Dep In = (\<Inter>{S. In \<subseteq> S \<and> dep_closed Dep S})"

definition gen_def :: "(expr set * expr) set => expr => expr set => bool" where
  "gen_def Dep y In = (y \<in> gen_closure Dep In)"

lemma operative_iff: "operative L7 G \<longleftrightarrow> (L7 \<and> G)"
  unfolding operative_def by simp

lemma gluing_failure_not_operative:
  assumes L7 and "\<not> G"
  shows "\<not> operative L7 G"
  using assms unfolding operative_def by simp

lemma input_in_gen_closure: "In \<subseteq> gen_closure Dep In"
  unfolding gen_closure_def by auto

lemma gen_closure_least:
  assumes "In \<subseteq> S" and "dep_closed Dep S"
  shows "gen_closure Dep In \<subseteq> S"
  using assms unfolding gen_closure_def by auto

lemma operative_in_req_layer: "OperativeE \<in> req_layer C Slots k"
  unfolding req_layer_def req0_def by auto

definition safe_set :: "(nat => nat set) => expr set" where
  "safe_set Slots = UNIV - (out_notG Slots \<union> {OperativeE})"

lemma ctx_notG_subset_safe: "ctx_notG C \<subseteq> safe_set Slots"
  unfolding ctx_notG_def comp_exprs_def safe_set_def out_notG_def out_layer_def by auto

lemma safe_set_dep_closed:
  "dep_closed (dep_repr C Slots) (safe_set Slots)"
proof (unfold dep_closed_def, intro allI impI)
  fix A y
  assume r: "(A,y) \<in> dep_repr C Slots"
  then obtain k where "k < 4" and yo: "y \<in> out_layer Slots k"
      and ae: "A = req_layer C Slots k"
    unfolding dep_repr_def by auto
  assume asub: "A \<subseteq> safe_set Slots"
  have opA: "OperativeE \<in> A" using operative_in_req_layer ae by simp
  have opS: "OperativeE \<in> safe_set Slots" using asub opA by auto
  have "OperativeE \<notin> safe_set Slots" unfolding safe_set_def by simp
  with opS show "y \<in> safe_set Slots" by contradiction
qed

lemma designated_output_not_safe:
  assumes "y \<in> out_notG Slots"
  shows "y \<notin> safe_set Slots"
  using assms unfolding safe_set_def by auto

theorem designated_outputs_absent_from_failed_gluing_closure:
  assumes yo: "y \<in> out_notG Slots"
  shows "\<not> gen_def (dep_repr C Slots) y (ctx_notG C)"
proof
  assume g: "gen_def (dep_repr C Slots) y (ctx_notG C)"
  have sub: "gen_closure (dep_repr C Slots) (ctx_notG C) \<subseteq> safe_set Slots"
    using gen_closure_least[OF ctx_notG_subset_safe safe_set_dep_closed] .
  have yin: "y \<in> gen_closure (dep_repr C Slots) (ctx_notG C)"
    using g unfolding gen_def_def .
  have "y \<in> safe_set Slots" using sub yin by auto
  moreover have "y \<notin> safe_set Slots" using designated_output_not_safe[OF yo] .
  ultimately show False by contradiction
qed

theorem global_gluing_failure_blocks_representation_entry:
  assumes L7 and "\<not> G"
  shows "\<not> operative L7 G"
    and "\<forall>y\<in>out_notG Slots.
         \<not> gen_def (dep_repr C Slots) y (ctx_notG C)"
  using assms gluing_failure_not_operative designated_outputs_absent_from_failed_gluing_closure
  by auto

lemma supplied_output_is_generated:
  assumes "y \<in> out_notG Slots"
  shows "gen_def (dep_repr C Slots) y (insert y (ctx_notG C))"
proof -
  have in_cl:
    "insert y (ctx_notG C) \<subseteq>
     gen_closure (dep_repr C Slots) (insert y (ctx_notG C))"
    using input_in_gen_closure[
      where Dep="dep_repr C Slots" and In="insert y (ctx_notG C)"] .
  have "y \<in> gen_closure (dep_repr C Slots) (insert y (ctx_notG C))"
    using in_cl by auto
  then show ?thesis unfolding gen_def_def .
qed

lemma empty_component_context:
  "ctx_notG {} = {L7E, NotGE, NotOperativeE}"
  unfolding ctx_notG_def comp_exprs_def by simp

lemma empty_output_family:
  assumes "\<And>k. k < 4 \<Longrightarrow> Slots k = {}"
  shows "out_notG Slots = {}"
  using assms unfolding out_notG_def out_layer_def by auto

end
