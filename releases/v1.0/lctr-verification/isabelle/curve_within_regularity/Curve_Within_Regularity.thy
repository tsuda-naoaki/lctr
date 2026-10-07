theory Curve_Within_Regularity
  imports "HOL-Analysis.Analysis"
begin

fun curve_Ck_on :: "nat \<Rightarrow> (real \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> real set \<Rightarrow> bool" where
  "curve_Ck_on 0 f S = continuous_on S f"
| "curve_Ck_on (Suc k) f S = (\<forall>x\<in>S. \<exists>U. eventually (\<lambda>y. y\<in>U) (inf (nhds x) (principal (insert x S))) \<and>
      (\<exists>d. (\<forall>y\<in>U. (f has_vector_derivative d y) (at y within U)) \<and> curve_Ck_on k d U))"

lemma zero_order_exact: "curve_Ck_on 0 f S \<longleftrightarrow> continuous_on S f"
  by simp

lemma empty_domain_exact: "curve_Ck_on k f {}"
  by (cases k) simp_all

lemma linear_transport_forward:
  fixes F :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes F: "bounded_linear F" and h: "curve_Ck_on k f S"
  shows "curve_Ck_on k (F \<circ> f) S"
  using h
proof (induction k arbitrary: f S)
  case 0
  show ?case using continuous_on_compose[OF _ linear_continuous_on[OF F]] 0 by simp
next
  case (Suc k)
  show ?case unfolding curve_Ck_on.simps(2)
  proof (intro ballI)
    fix x assume x: "x\<in>S"
    obtain U d where U: "eventually (\<lambda>y. y\<in>U) (inf (nhds x) (principal (insert x S)))"
      and d: "\<forall>y\<in>U. (f has_vector_derivative d y) (at y within U)"
      and ck: "curve_Ck_on k d U"
      using Suc.prems x by auto
    have deriv: "((F \<circ> f) has_vector_derivative (F \<circ> d) y) (at y within U)" if "y\<in>U" for y
      using bounded_linear.has_vector_derivative[OF F d[rule_format, OF that]]
      by (simp add: o_def)
    have next_ck: "curve_Ck_on k (F \<circ> d) U" by (rule Suc.IH[OF ck])
    show "\<exists>U. eventually (\<lambda>y. y\<in>U) (inf (nhds x) (principal (insert x S))) \<and>
      (\<exists>d. (\<forall>y\<in>U. ((F \<circ> f) has_vector_derivative d y) (at y within U)) \<and> curve_Ck_on k d U)"
      by (intro exI[of _ U] conjI U exI[of _ "F \<circ> d"] ballI deriv next_ck) assumption?
  qed
qed

lemma linear_transport_exact:
  fixes F :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector" and G :: "'b \<Rightarrow> 'a"
  assumes F: "bounded_linear F" and G: "bounded_linear G"
    and GF: "\<And>x. G (F x)=x"
  shows "curve_Ck_on k (F \<circ> f) S \<longleftrightarrow> curve_Ck_on k f S"
proof
  assume h: "curve_Ck_on k (F \<circ> f) S"
  have "curve_Ck_on k (G \<circ> (F \<circ> f)) S" by (rule linear_transport_forward[OF G h])
  then show "curve_Ck_on k f S" by (simp add: o_def GF)
next
  assume "curve_Ck_on k f S"
  then show "curve_Ck_on k (F \<circ> f) S" by (rule linear_transport_forward[OF F])
qed

ML \<open>
val roots = @{thms zero_order_exact empty_domain_exact linear_transport_forward linear_transport_exact};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
