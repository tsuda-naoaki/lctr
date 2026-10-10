theory Finite_Coordinate_Flattening
  imports "HOL-Analysis.Analysis"
begin

definition coordinate_carrier :: "nat \<Rightarrow> (nat \<Rightarrow> real) set" where
  "coordinate_carrier n = {v. \<forall>i\<ge>n. v i=0}"
definition concatenate_coordinates :: "nat \<Rightarrow> nat \<Rightarrow> ((nat\<Rightarrow>real) \<times> (nat\<Rightarrow>real)) \<Rightarrow> nat \<Rightarrow> real" where
  "concatenate_coordinates m n p i =
    (if i<m then fst p i else if i<m+n then snd p (i-m) else 0)"
definition split_coordinates :: "nat \<Rightarrow> nat \<Rightarrow> (nat\<Rightarrow>real) \<Rightarrow> ((nat\<Rightarrow>real) \<times> (nat\<Rightarrow>real))" where
  "split_coordinates m n v =
    ((\<lambda>i. if i<m then v i else 0), (\<lambda>i. if i<n then v (m+i) else 0))"
definition coordinate_square_norm where
  "coordinate_square_norm n (v::nat\<Rightarrow>real) = (\<Sum>i<n. (v i)^2)"

lemma zero_dimension_exact:
  "coordinate_carrier 0 = {\<lambda>_. 0}"
  by (auto simp: coordinate_carrier_def fun_eq_iff)

lemma coordinate_extensionality:
  assumes v: "v\<in>coordinate_carrier n" and w: "w\<in>coordinate_carrier n"
    and same: "\<And>i. i<n \<Longrightarrow> v i=w i"
  shows "v=w"
proof (rule ext)
  fix i show "v i=w i"
    using v w same[of i] unfolding coordinate_carrier_def by (cases "i<n") auto
qed

lemma concatenate_typed:
  "concatenate_coordinates m n p\<in>coordinate_carrier (m+n)"
  by (auto simp: coordinate_carrier_def concatenate_coordinates_def)

lemma split_typed:
  "split_coordinates m n v\<in>coordinate_carrier m \<times> coordinate_carrier n"
  by (auto simp: coordinate_carrier_def split_coordinates_def)

lemma concatenate_left_component:
  "i<m \<Longrightarrow> concatenate_coordinates m n p i = fst p i"
  by (simp add: concatenate_coordinates_def)
lemma concatenate_right_component:
  "i<n \<Longrightarrow> concatenate_coordinates m n p (m+i) = snd p i"
  by (simp add: concatenate_coordinates_def)

lemma split_concatenate:
  assumes p: "p\<in>coordinate_carrier m \<times> coordinate_carrier n"
  shows "split_coordinates m n (concatenate_coordinates m n p)=p"
proof (rule prod_eqI)
  show "fst (split_coordinates m n (concatenate_coordinates m n p))=fst p"
    using p by (auto simp: split_coordinates_def coordinate_carrier_def
      concatenate_coordinates_def fun_eq_iff)
  show "snd (split_coordinates m n (concatenate_coordinates m n p))=snd p"
    using p by (auto simp: split_coordinates_def coordinate_carrier_def
      concatenate_coordinates_def fun_eq_iff)
qed

lemma concatenate_split:
  assumes v: "v\<in>coordinate_carrier (m+n)"
  shows "concatenate_coordinates m n (split_coordinates m n v)=v"
proof (rule ext)
  fix i
  show "concatenate_coordinates m n (split_coordinates m n v) i=v i"
  proof (cases "i<m")
    case True then show ?thesis by (simp add: concatenate_coordinates_def split_coordinates_def)
  next
    case False
    have im: "m\<le>i" using False by simp
    show ?thesis using v im by (auto simp: concatenate_coordinates_def split_coordinates_def coordinate_carrier_def)
  qed
qed

lemma concatenate_bijection:
  "bij_betw (concatenate_coordinates m n)
    (coordinate_carrier m \<times> coordinate_carrier n) (coordinate_carrier (m+n))"
proof (rule bij_betwI)
  show "concatenate_coordinates m n \<in>
    coordinate_carrier m \<times> coordinate_carrier n \<rightarrow> coordinate_carrier (m+n)"
    by (rule Pi_I) (rule concatenate_typed)
  show "split_coordinates m n \<in>
    coordinate_carrier (m+n) \<rightarrow> coordinate_carrier m \<times> coordinate_carrier n"
    by (rule Pi_I) (rule split_typed)
  show "\<And>p. p\<in>coordinate_carrier m \<times> coordinate_carrier n \<Longrightarrow>
    split_coordinates m n (concatenate_coordinates m n p)=p"
    by (rule split_concatenate)
  show "\<And>v. v\<in>coordinate_carrier (m+n) \<Longrightarrow>
    concatenate_coordinates m n (split_coordinates m n v)=v"
    by (rule concatenate_split)
qed

lemma concatenate_additive:
  "concatenate_coordinates m n ((\<lambda>i. fst p i+fst q i),(\<lambda>i. snd p i+snd q i))=
    (\<lambda>i. concatenate_coordinates m n p i + concatenate_coordinates m n q i)"
  by (rule ext) (simp add: concatenate_coordinates_def)
lemma concatenate_homogeneous:
  "concatenate_coordinates m n ((\<lambda>i. c * fst p i),(\<lambda>i. c * snd p i))=
    (\<lambda>i. c * concatenate_coordinates m n p i)"
  by (rule ext) (simp add: concatenate_coordinates_def)
lemma split_additive:
  "split_coordinates m n (\<lambda>i. v i+w i)=
    ((\<lambda>i. fst (split_coordinates m n v) i+fst (split_coordinates m n w) i),
     (\<lambda>i. snd (split_coordinates m n v) i+snd (split_coordinates m n w) i))"
  by (auto simp: split_coordinates_def fun_eq_iff)
lemma split_homogeneous:
  "split_coordinates m n (\<lambda>i. c * v i)=
    ((\<lambda>i. c * fst (split_coordinates m n v) i),
     (\<lambda>i. c * snd (split_coordinates m n v) i))"
  by (auto simp: split_coordinates_def fun_eq_iff)

lemma finite_sum_split:
  "(\<Sum>i<m+n. f i) = (\<Sum>i<m. f i) + (\<Sum>i<n. (f::nat\<Rightarrow>real) (m+i))"
  by (induct n) (simp_all add: algebra_simps)

lemma square_norm_preserved:
  "coordinate_square_norm (m+n) (concatenate_coordinates m n p)=
    coordinate_square_norm m (fst p) + coordinate_square_norm n (snd p)"
  unfolding coordinate_square_norm_def
  by (simp add: finite_sum_split concatenate_coordinates_def)

lemma square_norm_zero_iff:
  assumes v: "v\<in>coordinate_carrier n"
  shows "coordinate_square_norm n v=0 \<longleftrightarrow> v=(\<lambda>_. 0)"
proof
  assume h: "coordinate_square_norm n v=0"
  have low: "\<And>i. i<n \<Longrightarrow> v i=0"
    using h unfolding coordinate_square_norm_def by (simp add: sum_nonneg_eq_0_iff)
  show "v=(\<lambda>_. 0)" by (rule coordinate_extensionality[OF v])
    (auto simp: coordinate_carrier_def intro: low)
next
  assume "v=(\<lambda>_. 0)"
  then show "coordinate_square_norm n v=0" by (simp add: coordinate_square_norm_def)
qed

ML \<open>
val roots = @{thms zero_dimension_exact coordinate_extensionality concatenate_typed split_typed
 concatenate_left_component concatenate_right_component split_concatenate concatenate_split
 concatenate_bijection concatenate_additive concatenate_homogeneous split_additive split_homogeneous
 square_norm_preserved square_norm_zero_iff};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
