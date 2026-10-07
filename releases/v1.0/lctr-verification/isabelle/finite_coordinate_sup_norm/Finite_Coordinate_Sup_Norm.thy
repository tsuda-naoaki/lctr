theory Finite_Coordinate_Sup_Norm
  imports "LCTR_Finite_Coordinate_Flattening.Finite_Coordinate_Flattening"
begin

definition coordinate_abs_values where
  "coordinate_abs_values n (v::nat\<Rightarrow>real) = insert 0 ((\<lambda>i. abs(v i)) ` {..<n})"
definition coordinate_sup_norm where
  "coordinate_sup_norm n v = Max (coordinate_abs_values n v)"

lemma finite_abs_values: "finite (coordinate_abs_values n v)"
  by (simp add: coordinate_abs_values_def)
lemma abs_values_nonempty: "coordinate_abs_values n v \<noteq> {}"
  by (simp add: coordinate_abs_values_def)
lemma abs_values_concat:
  "coordinate_abs_values (m+n) (concatenate_coordinates m n p)=
    coordinate_abs_values m (fst p) \<union> coordinate_abs_values n (snd p)"
proof (rule set_eqI)
  fix x
  show "x\<in>coordinate_abs_values (m+n) (concatenate_coordinates m n p) \<longleftrightarrow>
    x\<in>coordinate_abs_values m (fst p) \<union> coordinate_abs_values n (snd p)"
  proof (cases "x=0")
    case True then show ?thesis by (simp add: coordinate_abs_values_def)
  next
    case False
    show ?thesis
    proof
      assume h: "x\<in>coordinate_abs_values (m+n) (concatenate_coordinates m n p)"
      obtain i where i: "i<m+n" "x=abs(concatenate_coordinates m n p i)"
        using h False by (auto simp: coordinate_abs_values_def)
      show "x\<in>coordinate_abs_values m (fst p) \<union> coordinate_abs_values n (snd p)"
      proof (cases "i<m")
        case True then show ?thesis using i by (auto simp: coordinate_abs_values_def concatenate_coordinates_def)
      next
        case False
        have low: "i-m<n" and rec: "m+(i-m)=i" using i(1) False by arith+
        have val_eq: "x=abs(snd p (i-m))" using i False by (simp add: concatenate_coordinates_def)
        show ?thesis using low val_eq by (auto simp: coordinate_abs_values_def)
      qed
    next
      assume h: "x\<in>coordinate_abs_values m (fst p) \<union> coordinate_abs_values n (snd p)"
      then consider (left) i where "i<m" "x=abs(fst p i)"
        | (right) i where "i<n" "x=abs(snd p i)"
        using False by (auto simp: coordinate_abs_values_def)
      then show "x\<in>coordinate_abs_values (m+n) (concatenate_coordinates m n p)"
      proof cases
        case (left i)
        have "i<m+n" using left(1) by arith
        then show ?thesis using left by (auto simp: coordinate_abs_values_def concatenate_coordinates_def)
      next
        case (right i)
        have "m+i<m+n" using right(1) by simp
        moreover have "x=abs(concatenate_coordinates m n p (m+i))"
          using right by (simp add: concatenate_coordinates_def)
        ultimately show ?thesis by (auto simp: coordinate_abs_values_def)
      qed
    qed
  qed
qed

lemma sup_norm_concat:
  "coordinate_sup_norm (m+n) (concatenate_coordinates m n p)=
    max (coordinate_sup_norm m (fst p)) (coordinate_sup_norm n (snd p))"
  unfolding coordinate_sup_norm_def
  by (simp add: abs_values_concat Max_Un finite_abs_values abs_values_nonempty)

lemma zero_dimension_sup_norm: "coordinate_sup_norm 0 v=0"
  by (simp add: coordinate_sup_norm_def coordinate_abs_values_def)

lemma sup_norm_nonnegative: "0\<le>coordinate_sup_norm n v"
  unfolding coordinate_sup_norm_def
  by (rule Max_ge[OF finite_abs_values]) (simp add: coordinate_abs_values_def)

lemma coordinate_bound:
  "i<n \<Longrightarrow> abs(v i)\<le>coordinate_sup_norm n v"
  unfolding coordinate_sup_norm_def
  by (rule Max_ge[OF finite_abs_values]) (auto simp: coordinate_abs_values_def)

lemma sup_norm_le_iff:
  assumes c: "0\<le>c"
  shows "coordinate_sup_norm n v\<le>c \<longleftrightarrow> (\<forall>i<n. abs(v i)\<le>c)"
  unfolding coordinate_sup_norm_def
  by (auto simp: Max_le_iff finite_abs_values abs_values_nonempty coordinate_abs_values_def c)

lemma split_sup_norm:
  assumes v: "v\<in>coordinate_carrier (m+n)"
  shows "max (coordinate_sup_norm m (fst(split_coordinates m n v)))
    (coordinate_sup_norm n (snd(split_coordinates m n v))) = coordinate_sup_norm (m+n) v"
  using sup_norm_concat[of m n "split_coordinates m n v"] concatenate_split[OF v] by simp

ML \<open>
val roots = @{thms finite_abs_values abs_values_nonempty abs_values_concat sup_norm_concat
 zero_dimension_sup_norm sup_norm_nonnegative coordinate_bound sup_norm_le_iff split_sup_norm};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
