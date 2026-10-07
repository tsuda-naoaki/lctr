theory Native_Coordinate_Vectors
  imports "LCTR_Finite_Coordinate_Sup_Norm.Finite_Coordinate_Sup_Norm"
    "HOL-Analysis.Bounded_Continuous_Function"
begin

type_synonym coord_vector = "nat \<Rightarrow>\<^sub>C real"

definition coordinate_vector :: "nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> coord_vector" where
  "coordinate_vector n v = Bcontfun (\<lambda>i. if i<n then v i else 0)"
definition vector_carrier where
  "vector_carrier n = {v::coord_vector. apply_bcontfun v \<in> coordinate_carrier n}"

lemma finite_coordinates_bounded:
  "(\<lambda>i::nat. if i<n then (v i::real) else 0) \<in> bcontfun"
proof (rule bcontfun_normI[where b="coordinate_sup_norm n v"])
  show "continuous_on UNIV (\<lambda>i. if i<n then v i else 0)" by simp
  show "norm (if i<n then v i else 0) \<le> coordinate_sup_norm n v" for i
    using coordinate_bound[of i n v] sup_norm_nonnegative[of n v] by auto
qed

lemma coordinate_vector_apply[simp]:
  "apply_bcontfun (coordinate_vector n v) i = (if i<n then v i else 0)"
  by (simp add: coordinate_vector_def Bcontfun_inverse[OF finite_coordinates_bounded])

lemma coordinate_vector_typed: "coordinate_vector n v \<in> vector_carrier n"
  by (auto simp: vector_carrier_def coordinate_carrier_def)

lemma coordinate_decode_encode:
  "v\<in>coordinate_carrier n \<Longrightarrow> apply_bcontfun (coordinate_vector n v)=v"
  by (auto simp: coordinate_carrier_def fun_eq_iff)

lemma coordinate_encode_decode:
  "v\<in>vector_carrier n \<Longrightarrow> coordinate_vector n (apply_bcontfun v)=v"
  by (rule bcontfun_eqI) (auto simp: vector_carrier_def coordinate_carrier_def)

lemma coordinate_vector_bijection:
  "bij_betw (coordinate_vector n) (coordinate_carrier n) (vector_carrier n)"
proof (rule bij_betwI)
  show "coordinate_vector n \<in> coordinate_carrier n \<rightarrow> vector_carrier n"
    using coordinate_vector_typed by blast
  show "apply_bcontfun \<in> vector_carrier n \<rightarrow> coordinate_carrier n"
    by (simp add: vector_carrier_def)
  show "\<And>x. x\<in>coordinate_carrier n \<Longrightarrow> apply_bcontfun (coordinate_vector n x)=x"
    by (rule coordinate_decode_encode)
  show "\<And>x. x\<in>vector_carrier n \<Longrightarrow> coordinate_vector n (apply_bcontfun x)=x"
    by (rule coordinate_encode_decode)
qed

lemma coordinate_vector_norm:
  "norm (coordinate_vector n v)=coordinate_sup_norm n v"
proof (rule antisym)
  show "norm (coordinate_vector n v)\<le>coordinate_sup_norm n v"
    by (rule norm_bound) (auto simp: coordinate_bound sup_norm_nonnegative)
  show "coordinate_sup_norm n v\<le>norm (coordinate_vector n v)"
    unfolding sup_norm_le_iff[OF norm_ge_zero]
  proof (intro allI impI)
    fix i assume i: "i<n"
    show "abs(v i)\<le>norm (coordinate_vector n v)"
      using norm_bounded[of "coordinate_vector n v" i] by (simp add: i)
  qed
qed

lemma zero_dimension_native: "vector_carrier 0 = {0}"
proof (rule set_eqI)
  fix v
  have "v\<in>vector_carrier 0 \<Longrightarrow> v=0"
    by (rule bcontfun_eqI) (auto simp: vector_carrier_def coordinate_carrier_def)
  then show "v\<in>vector_carrier 0 \<longleftrightarrow> v\<in>{0}"
    by (auto simp: vector_carrier_def coordinate_carrier_def)
qed

definition vector_concat :: "nat \<Rightarrow> nat \<Rightarrow> coord_vector \<times> coord_vector \<Rightarrow> coord_vector" where
  "vector_concat m n p = coordinate_vector (m+n)
    (concatenate_coordinates m n (apply_bcontfun (fst p),apply_bcontfun (snd p)))"
definition vector_split :: "nat \<Rightarrow> nat \<Rightarrow> coord_vector \<Rightarrow> coord_vector \<times> coord_vector" where
  "vector_split m n v = (coordinate_vector m (apply_bcontfun v),
    coordinate_vector n (\<lambda>i. apply_bcontfun v (m+i)))"

lemma vector_concat_apply[simp]:
  "apply_bcontfun (vector_concat m n p) i =
    (if i<m then apply_bcontfun (fst p) i else if i<m+n then apply_bcontfun (snd p) (i-m) else 0)"
  by (auto simp: vector_concat_def concatenate_coordinates_def)

lemma vector_split_concat:
  assumes p: "p\<in>vector_carrier m \<times> vector_carrier n"
  shows "vector_split m n (vector_concat m n p)=p"
proof (rule prod_eqI)
  show "fst (vector_split m n (vector_concat m n p))=fst p"
    by (rule bcontfun_eqI) (use p in \<open>auto simp: vector_split_def vector_carrier_def coordinate_carrier_def\<close>)
  show "snd (vector_split m n (vector_concat m n p))=snd p"
    by (rule bcontfun_eqI) (use p in \<open>auto simp: vector_split_def vector_carrier_def coordinate_carrier_def\<close>)
qed

lemma vector_concat_split:
  assumes v: "v\<in>vector_carrier (m+n)"
  shows "vector_concat m n (vector_split m n v)=v"
  by (rule bcontfun_eqI) (use v in \<open>auto simp: vector_split_def vector_carrier_def coordinate_carrier_def\<close>)

lemma vector_concat_typed: "vector_concat m n p\<in>vector_carrier (m+n)"
  unfolding vector_concat_def by (rule coordinate_vector_typed)

lemma vector_split_typed: "vector_split m n v\<in>vector_carrier m \<times> vector_carrier n"
  by (simp add: vector_split_def coordinate_vector_typed)

ML \<open>
val roots = @{thms finite_coordinates_bounded coordinate_vector_apply coordinate_vector_typed
 coordinate_decode_encode coordinate_encode_decode coordinate_vector_bijection coordinate_vector_norm
 zero_dimension_native vector_concat_apply vector_split_concat vector_concat_split vector_concat_typed vector_split_typed};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
