theory Abstract_Gluing_Isabelle
imports Main
begin

definition abs_out_notG :: "(nat => 'e set) => 'e set" where
  "abs_out_notG Out = (\<Union>k\<in>{0..<4}. Out k)"

definition abs_req0 :: "'e set => 'e => 'e set" where
  "abs_req0 C Op = C \<union> {Op}"

definition abs_req_layer ::
  "'e set => 'e => (nat => 'e) => (nat => 'e set) => nat => 'e set" where
  "abs_req_layer C Op Repr Out k =
   (if k = 0 then abs_req0 C Op
    else abs_req0 C Op \<union> {Repr k}
         \<union> (\<Union>j\<in>{0..<k}. Out j))"

definition abs_dep_repr ::
  "'e set => 'e => (nat => 'e) => (nat => 'e set) => ('e set * 'e) set" where
  "abs_dep_repr C Op Repr Out =
   {(abs_req_layer C Op Repr Out k, y) |k y.
      k < 4 \<and> y \<in> Out k}"

definition abs_ctx_notG ::
  "'e set => 'e => 'e => 'e => 'e set" where
  "abs_ctx_notG C L7Expr NotGExpr NotOpExpr =
   C \<union> {L7Expr, NotGExpr, NotOpExpr}"

definition paper_ctx_output_separation ::
  "'e set => 'e => 'e => 'e => 'e => (nat => 'e set) => bool" where
  "paper_ctx_output_separation C Op L7Expr NotGExpr NotOpExpr Out =
   (abs_ctx_notG C L7Expr NotGExpr NotOpExpr
    \<subseteq> UNIV - (abs_out_notG Out \<union> {Op}))"

definition abs_dep_closed ::
  "('e set * 'e) set => 'e set => bool" where
  "abs_dep_closed Dep S =
   (\<forall>A y. (A,y) \<in> Dep \<longrightarrow> A \<subseteq> S \<longrightarrow> y \<in> S)"

definition abs_gen_closure ::
  "('e set * 'e) set => 'e set => 'e set" where
  "abs_gen_closure Dep In =
   (\<Inter>{S. In \<subseteq> S \<and> abs_dep_closed Dep S})"

definition abs_gen_def ::
  "('e set * 'e) set => 'e => 'e set => bool" where
  "abs_gen_def Dep y In = (y \<in> abs_gen_closure Dep In)"

definition paper_operative :: "bool => bool => bool" where
  "paper_operative L7 G = (L7 \<and> G)"

lemma abs_input_in_gen_closure:
  "In \<subseteq> abs_gen_closure Dep In"
  unfolding abs_gen_closure_def by auto

lemma abs_gen_closure_least:
  assumes "In \<subseteq> S" and "abs_dep_closed Dep S"
  shows "abs_gen_closure Dep In \<subseteq> S"
  using assms unfolding abs_gen_closure_def by auto

lemma abs_op_in_req_layer:
  "Op \<in> abs_req_layer C Op Repr Out k"
  unfolding abs_req_layer_def abs_req0_def by auto

definition abs_safe_set :: "'e => (nat => 'e set) => 'e set" where
  "abs_safe_set Op Out = UNIV - (abs_out_notG Out \<union> {Op})"

lemma separation_is_exact_ctx_subset:
  assumes sep:
    "paper_ctx_output_separation C Op L7Expr NotGExpr NotOpExpr Out"
  shows "abs_ctx_notG C L7Expr NotGExpr NotOpExpr
         \<subseteq> abs_safe_set Op Out"
  using sep unfolding paper_ctx_output_separation_def abs_safe_set_def .

lemma abs_safe_set_dep_closed:
  "abs_dep_closed (abs_dep_repr C Op Repr Out) (abs_safe_set Op Out)"
proof (unfold abs_dep_closed_def, intro allI impI)
  fix A y
  assume rule: "(A,y) \<in> abs_dep_repr C Op Repr Out"
  then obtain k where k4: "k < 4"
      and yout: "y \<in> Out k"
      and Aeq: "A = abs_req_layer C Op Repr Out k"
    unfolding abs_dep_repr_def by auto
  assume Asafe: "A \<subseteq> abs_safe_set Op Out"
  have opA: "Op \<in> A"
    using abs_op_in_req_layer[of Op C Repr Out k] Aeq by simp
  have opSafe: "Op \<in> abs_safe_set Op Out"
    using Asafe opA by auto
  have "Op \<notin> abs_safe_set Op Out"
    unfolding abs_safe_set_def by simp
  with opSafe show "y \<in> abs_safe_set Op Out" by contradiction
qed

lemma abs_designated_output_not_safe:
  assumes "y \<in> abs_out_notG Out"
  shows "y \<notin> abs_safe_set Op Out"
  using assms unfolding abs_safe_set_def by auto

theorem abstract_designated_outputs_absent:
  assumes sep:
    "paper_ctx_output_separation C Op L7Expr NotGExpr NotOpExpr Out"
      and yout: "y \<in> abs_out_notG Out"
  shows "\<not> abs_gen_def
           (abs_dep_repr C Op Repr Out) y
           (abs_ctx_notG C L7Expr NotGExpr NotOpExpr)"
proof
  assume gen:
    "abs_gen_def
      (abs_dep_repr C Op Repr Out) y
      (abs_ctx_notG C L7Expr NotGExpr NotOpExpr)"
  have ctxsafe:
    "abs_ctx_notG C L7Expr NotGExpr NotOpExpr
     \<subseteq> abs_safe_set Op Out"
    using separation_is_exact_ctx_subset[OF sep] .
  have closed:
    "abs_dep_closed
      (abs_dep_repr C Op Repr Out)
      (abs_safe_set Op Out)"
    using abs_safe_set_dep_closed .
  have clsub:
    "abs_gen_closure
      (abs_dep_repr C Op Repr Out)
      (abs_ctx_notG C L7Expr NotGExpr NotOpExpr)
     \<subseteq> abs_safe_set Op Out"
    using abs_gen_closure_least[OF ctxsafe closed] .
  have yin:
    "y \<in> abs_gen_closure
      (abs_dep_repr C Op Repr Out)
      (abs_ctx_notG C L7Expr NotGExpr NotOpExpr)"
    using gen unfolding abs_gen_def_def .
  have "y \<in> abs_safe_set Op Out"
    using clsub yin by auto
  moreover have "y \<notin> abs_safe_set Op Out"
    using abs_designated_output_not_safe[OF yout] .
  ultimately show False by contradiction
qed

theorem abstract_global_gluing_failure_blocks_representation_entry:
  assumes L7
      and "\<not> G"
      and sep:
        "paper_ctx_output_separation C Op L7Expr NotGExpr NotOpExpr Out"
  shows "\<not> paper_operative L7 G"
    and "\<forall>y\<in>abs_out_notG Out.
         \<not> abs_gen_def
           (abs_dep_repr C Op Repr Out) y
           (abs_ctx_notG C L7Expr NotGExpr NotOpExpr)"
proof -
  show "\<not> paper_operative L7 G"
    using assms(1,2) unfolding paper_operative_def by simp
  show "\<forall>y\<in>abs_out_notG Out.
         \<not> abs_gen_def
           (abs_dep_repr C Op Repr Out) y
           (abs_ctx_notG C L7Expr NotGExpr NotOpExpr)"
    using abstract_designated_outputs_absent[OF sep] by auto
qed

lemma abstract_supplied_output_is_generated:
  assumes "y \<in> abs_out_notG Out"
  shows "abs_gen_def
          (abs_dep_repr C Op Repr Out) y
          (insert y (abs_ctx_notG C L7Expr NotGExpr NotOpExpr))"
proof -
  have in_cl:
    "insert y (abs_ctx_notG C L7Expr NotGExpr NotOpExpr)
     \<subseteq>
     abs_gen_closure
       (abs_dep_repr C Op Repr Out)
       (insert y (abs_ctx_notG C L7Expr NotGExpr NotOpExpr))"
    using abs_input_in_gen_closure[
      where Dep="abs_dep_repr C Op Repr Out"
        and In="insert y (abs_ctx_notG C L7Expr NotGExpr NotOpExpr)"] .
  have
    "y \<in> abs_gen_closure
      (abs_dep_repr C Op Repr Out)
      (insert y (abs_ctx_notG C L7Expr NotGExpr NotOpExpr))"
    using in_cl by auto
  then show ?thesis unfolding abs_gen_def_def .
qed

lemma abstract_empty_output_family:
  assumes "\<And>k. k < 4 \<Longrightarrow> Out k = {}"
  shows "abs_out_notG Out = {}"
  using assms unfolding abs_out_notG_def by auto

end
