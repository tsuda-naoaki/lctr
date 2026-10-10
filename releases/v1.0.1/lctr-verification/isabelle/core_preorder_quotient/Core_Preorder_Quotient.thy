theory Core_Preorder_Quotient
  imports Main
begin

definition pre_on where
  "pre_on A r = ((\<forall>a\<in>A. r a a) \<and>
    (\<forall>a\<in>A. \<forall>b\<in>A. \<forall>c\<in>A. r a b \<longrightarrow> r b c \<longrightarrow> r a c))"
definition part_on where
  "part_on A r = (pre_on A r \<and> (\<forall>a\<in>A. \<forall>b\<in>A. r a b \<longrightarrow> r b a \<longrightarrow> a=b))"
definition pullback where "pullback f r a b = r (f a) (f b)"

theorem preorder_pullback:
  assumes "f ` A \<subseteq> T" "pre_on T r"
  shows "pre_on A (pullback f r)"
  using assms unfolding pre_on_def pullback_def by blast

definition ord_desc where
  "ord_desc A E r = (\<forall>a\<in>A. \<forall>a'\<in>A. \<forall>b\<in>A. \<forall>b'\<in>A.
    (a,a')\<in>E \<longrightarrow> (b,b')\<in>E \<longrightarrow> (r a b = r a' b'))"
definition ord_sep where
  "ord_sep A E r = (\<forall>a\<in>A. \<forall>b\<in>A. r a b \<longrightarrow> r b a \<longrightarrow> (a,b)\<in>E)"
definition qrel where
  "qrel A E r X Y = (\<exists>a\<in>A. \<exists>b\<in>A. X=E``{a} \<and> Y=E``{b} \<and> r a b)"

lemma quotient_on_representatives:
  assumes eqv: "equiv A E" and desc: "ord_desc A E r" and a: "a\<in>A" and b: "b\<in>A"
  shows "qrel A E r (E``{a}) (E``{b}) = r a b"
proof
  assume "qrel A E r (E``{a}) (E``{b})"
  then obtain a' b' where aa: "a'\<in>A" and bb: "b'\<in>A"
    and qa: "E``{a}=E``{a'}" and qb: "E``{b}=E``{b'}" and rr: "r a' b'"
    unfolding qrel_def by blast
  have ea: "(a,a')\<in>E" using eq_equiv_class_iff[OF eqv a aa] qa by simp
  have eb: "(b,b')\<in>E" using eq_equiv_class_iff[OF eqv b bb] qb by simp
  show "r a b" using desc a aa b bb ea eb rr unfolding ord_desc_def by blast
next
  assume "r a b"
  then show "qrel A E r (E``{a}) (E``{b})" using a b unfolding qrel_def by blast
qed

theorem quotient_preorder:
  assumes eqv: "equiv A E" and desc: "ord_desc A E r" and pre: "pre_on A r"
  shows "pre_on (A//E) (qrel A E r)"
proof -
  have qr: "\<And>a b. a\<in>A \<Longrightarrow> b\<in>A \<Longrightarrow> qrel A E r (E``{a}) (E``{b}) = r a b"
    by (rule quotient_on_representatives[OF eqv desc])
  show ?thesis using pre unfolding pre_on_def quotient_def using qr by blast
qed

theorem quotient_partial_order:
  assumes eqv: "equiv A E" and desc: "ord_desc A E r" and sep: "ord_sep A E r"
    and pre: "pre_on A r"
  shows "part_on (A//E) (qrel A E r)"
proof -
  have qp: "pre_on (A//E) (qrel A E r)" by (rule quotient_preorder[OF eqv desc pre])
  have anti: "\<And>X Y. X\<in>A//E \<Longrightarrow> Y\<in>A//E \<Longrightarrow> qrel A E r X Y \<Longrightarrow> qrel A E r Y X \<Longrightarrow> X=Y"
  proof -
    fix X Y
    assume X: "X\<in>A//E" and Y: "Y\<in>A//E" and xy: "qrel A E r X Y" and yx: "qrel A E r Y X"
    obtain a where a: "a\<in>A" and xa: "X=E``{a}" using X unfolding quotient_def by blast
    obtain b where b: "b\<in>A" and yb: "Y=E``{b}" using Y unfolding quotient_def by blast
    have ab: "r a b" using xy quotient_on_representatives[OF eqv desc a b] xa yb by simp
    have ba: "r b a" using yx quotient_on_representatives[OF eqv desc b a] xa yb by simp
    have "(a,b)\<in>E" using sep a b ab ba unfolding ord_sep_def by blast
    then show "X=Y" using equiv_class_eq[OF eqv] xa yb by blast
  qed
  show ?thesis using qp anti unfolding part_on_def by blast
qed

theorem quotient_relation_unique:
  assumes eqv: "equiv A E" and desc: "ord_desc A E r"
    and q: "\<And>a b. a\<in>A \<Longrightarrow> b\<in>A \<Longrightarrow> q (E``{a}) (E``{b}) = r a b"
    and X: "X\<in>A//E" and Y: "Y\<in>A//E"
  shows "q X Y = qrel A E r X Y"
  using X Y q quotient_on_representatives[OF eqv desc] unfolding quotient_def by blast

theorem descent_is_necessary:
  assumes eqv: "equiv A E"
    and q: "\<And>a b. a\<in>A \<Longrightarrow> b\<in>A \<Longrightarrow> q (E``{a}) (E``{b}) = r a b"
  shows "ord_desc A E r"
  using q equiv_class_eq[OF eqv] unfolding ord_desc_def by metis

theorem empty_quotient: "({}::'a set)//E = {}" by simp

theorem missing_descent_counterexample:
  "pre_on (UNIV::bool set) (=) \<and> ord_sep UNIV (UNIV::(bool\<times>bool)set) (=) \<and>
    \<not>ord_desc (UNIV::bool set) UNIV (=)"
  unfolding pre_on_def ord_sep_def ord_desc_def by auto

theorem missing_separation_counterexample:
  "pre_on (UNIV::bool set) (\<lambda>_ _. True) \<and>
    ord_desc (UNIV::bool set) Id (\<lambda>_ _. True) \<and>
    \<not>ord_sep (UNIV::bool set) Id (\<lambda>_ _. True)"
  unfolding pre_on_def ord_desc_def ord_sep_def by auto

ML \<open>
val roots = @{thms preorder_pullback quotient_on_representatives quotient_preorder
  quotient_partial_order quotient_relation_unique descent_is_necessary empty_quotient
  missing_descent_counterexample missing_separation_counterexample};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
