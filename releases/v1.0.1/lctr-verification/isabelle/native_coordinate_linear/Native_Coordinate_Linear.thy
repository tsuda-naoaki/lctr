theory Native_Coordinate_Linear
  imports "LCTR_Native_Coordinate_Vectors.Native_Coordinate_Vectors"
    "LCTR_Curve_Within_Regularity.Curve_Within_Regularity"
begin

lemma vector_concat_additive: "vector_concat m n (p+q)=vector_concat m n p+vector_concat m n q"
  by (rule bcontfun_eqI) auto
lemma vector_concat_homogeneous: "vector_concat m n (c *\<^sub>R p)=c *\<^sub>R vector_concat m n p"
  by (rule bcontfun_eqI) auto
lemma vector_concat_bounded: "norm (vector_concat m n p)\<le>norm p"
proof (rule norm_bound)
  fix i
  have a: "norm (fst p)\<le>norm p" by (cases p) (simp add: norm_fst_le)
  have b: "norm (snd p)\<le>norm p" by (cases p) (simp add: norm_snd_le)
  have aa: "norm (apply_bcontfun (fst p) i)\<le>norm p" by (rule order_trans[OF norm_bounded a])
  have bb: "norm (apply_bcontfun (snd p) (i-m))\<le>norm p" by (rule order_trans[OF norm_bounded b])
  show "norm (apply_bcontfun (vector_concat m n p) i)\<le>norm p" using aa bb by auto
qed
lemma vector_concat_linear: "bounded_linear (vector_concat m n)"
  by (rule bounded_linear_intro[where K=1]) (simp_all add: vector_concat_additive vector_concat_homogeneous vector_concat_bounded)

lemma vector_split_additive: "vector_split m n (v+w)=vector_split m n v+vector_split m n w"
  by (rule prod_eqI) (auto simp: vector_split_def intro!: bcontfun_eqI)
lemma vector_split_homogeneous: "vector_split m n (c *\<^sub>R v)=c *\<^sub>R vector_split m n v"
  by (rule prod_eqI) (auto simp: vector_split_def intro!: bcontfun_eqI)
lemma coordinate_projection_bounded:
  "norm (coordinate_vector n (\<lambda>i. apply_bcontfun v (r i)))\<le>norm v"
proof (rule norm_bound)
  fix i
  show "norm (apply_bcontfun (coordinate_vector n (\<lambda>i. apply_bcontfun v (r i))) i)\<le>norm v"
    using norm_bounded[of v "r i"] by auto
qed
lemma vector_split_bounded: "norm (vector_split m n v)\<le>norm v * 2"
proof -
  have a: "norm (coordinate_vector m (apply_bcontfun v))\<le>norm v"
    using coordinate_projection_bounded[of m v id] by simp
  have b: "norm (coordinate_vector n (\<lambda>i. apply_bcontfun v (m+i)))\<le>norm v"
    by (rule coordinate_projection_bounded)
  have "norm (vector_split m n v)\<le>norm (coordinate_vector m (apply_bcontfun v))+
    norm (coordinate_vector n (\<lambda>i. apply_bcontfun v (m+i)))"
    unfolding vector_split_def by (rule norm_Pair_le)
  with a b show ?thesis by linarith
qed
lemma vector_split_linear: "bounded_linear (vector_split m n)"
  by (rule bounded_linear_intro[where K=2]) (simp_all add: vector_split_additive vector_split_homogeneous vector_split_bounded)

lemma native_flatten_smoothness:
  assumes f: "\<And>t. f t\<in>vector_carrier m \<times> vector_carrier n"
  shows "curve_Ck_on k (vector_concat m n \<circ> f) U \<longleftrightarrow> curve_Ck_on k f U"
proof
  assume h: "curve_Ck_on k (vector_concat m n \<circ> f) U"
  have "curve_Ck_on k (vector_split m n \<circ> (vector_concat m n \<circ> f)) U"
    by (rule linear_transport_forward[OF vector_split_linear h])
  then show "curve_Ck_on k f U" by (simp add: o_def vector_split_concat[OF f])
next
  assume "curve_Ck_on k f U"
  then show "curve_Ck_on k (vector_concat m n \<circ> f) U"
    by (rule linear_transport_forward[OF vector_concat_linear])
qed

ML \<open>
val roots = @{thms vector_concat_additive vector_concat_homogeneous vector_concat_bounded vector_concat_linear
 vector_split_additive vector_split_homogeneous coordinate_projection_bounded vector_split_bounded vector_split_linear native_flatten_smoothness};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
