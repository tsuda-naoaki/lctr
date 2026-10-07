theory Native_Flatten_Final
  imports "LCTR_Native_Coordinate_Linear.Native_Coordinate_Linear"
    "LCTR_Linear_Retraction_Derivatives.Linear_Retraction_Derivatives"
    "LCTR_Carrier_Jet_Transport.Carrier_Jet_Transport"
begin

interpretation coordinate_retraction: bounded_linear_retraction "vector_concat m n" "vector_split m n" for m n
  by (rule bounded_linear_retraction.intro) (rule vector_concat_linear, rule vector_split_linear)

interpretation coordinate_bijection: carrier_bijection "vector_concat m n" "vector_split m n"
  "vector_carrier m \<times> vector_carrier n" "vector_carrier (m+n)" for m n
  by unfold_locales (auto intro: vector_concat_typed vector_split_typed vector_split_concat vector_concat_split)

definition native_curve_jet where
  "native_curve_jet k a f = restrict (\<lambda>j. (zderiv ^^ j) f a) {..k}"

lemma flatten_inverse:
  "v\<in>vector_carrier m \<times> vector_carrier n \<Longrightarrow> vector_split m n (vector_concat m n v)=v"
  by (rule vector_split_concat)
lemma unflatten_inverse:
  "v\<in>vector_carrier (m+n) \<Longrightarrow> vector_concat m n (vector_split m n v)=v"
  by (rule vector_concat_split)
lemma smoothness_preserved:
  "(\<And>t. f t\<in>vector_carrier m \<times> vector_carrier n) \<Longrightarrow>
   curve_Ck_on k (vector_concat m n \<circ> f) U \<longleftrightarrow> curve_Ck_on k f U"
  by (rule native_flatten_smoothness)
lemma derivatives_preserved:
  "(\<And>t. f t\<in>vector_carrier m \<times> vector_carrier n) \<Longrightarrow>
   (zderiv ^^ j) (vector_concat m n \<circ> f) a = vector_concat m n ((zderiv ^^ j) f a)"
  by (rule coordinate_retraction.iterated_zderiv_retraction_comp) (rule vector_split_concat, assumption)

lemma native_derivative_carrier:
  assumes f: "\<And>t. f t\<in>vector_carrier m \<times> vector_carrier n"
  shows "(zderiv ^^ j) f a\<in>vector_carrier m \<times> vector_carrier n"
proof -
  have e: "vector_split m n (vector_concat m n ((zderiv ^^ j) f a))=(zderiv ^^ j) f a"
    by (rule coordinate_retraction.iterated_retraction_identity) (rule vector_split_concat[OF f])
  show ?thesis using vector_split_typed[of m n "vector_concat m n ((zderiv ^^ j) f a)"] e by simp
qed

lemma native_curve_jet_typed:
  assumes f: "\<And>t. f t\<in>vector_carrier m \<times> vector_carrier n" and base: "f a\<in>V"
  shows "native_curve_jet k a f\<in>carrier_jet_domain k (vector_carrier m \<times> vector_carrier n) V"
  using base native_derivative_carrier[OF f]
  by (auto simp: native_curve_jet_def carrier_jet_domain_def restrict_def PiE_def Pi_iff extensional_def)

lemma jet_flatten_derivative_order:
  assumes "v\<in>carrier_jet_domain k (vector_carrier m \<times> vector_carrier n) V" and "j\<le>k"
  shows "carrier_jet_push k (vector_concat m n) v j=vector_concat m n (v j)"
  by (rule carrier_jet_component[OF assms(2)])

lemma flatten_actual_jet:
  assumes f: "\<And>t. f t\<in>vector_carrier m \<times> vector_carrier n" and base: "f a\<in>V"
  shows "carrier_jet_push k (vector_concat m n) (native_curve_jet k a f)=
    native_curve_jet k a (vector_concat m n \<circ> f)"
    and "native_curve_jet k a f\<in>carrier_jet_domain k (vector_carrier m \<times> vector_carrier n) V"
    and "native_curve_jet k a (vector_concat m n \<circ> f)\<in>carrier_jet_domain k (vector_carrier (m+n)) (vector_concat m n ` V)"
proof -
  show eq: "carrier_jet_push k (vector_concat m n) (native_curve_jet k a f)=
    native_curve_jet k a (vector_concat m n \<circ> f)"
    by (auto simp: carrier_jet_push_def native_curve_jet_def restrict_def fun_eq_iff derivatives_preserved[OF f])
  show typed: "native_curve_jet k a f\<in>carrier_jet_domain k (vector_carrier m \<times> vector_carrier n) V"
    by (rule native_curve_jet_typed[where f=f and m=m and n=n and a=a and V=V and k=k, OF f base])
  show "native_curve_jet k a (vector_concat m n \<circ> f)\<in>carrier_jet_domain k (vector_carrier (m+n)) (vector_concat m n ` V)"
    using coordinate_bijection.jet_forward_typed[OF typed] by (simp only: eq)
qed

lemma numeric_time_preserved: "fst (carrier_ambient_push k (vector_concat m n) p)=fst p"
  by (rule carrier_numeric_time_preserved)

lemma flattened_relation_membership:
  assumes "R\<subseteq>U \<times> carrier_jet_domain k (vector_carrier m \<times> vector_carrier n) V"
    and "p\<in>U \<times> carrier_jet_domain k (vector_carrier m \<times> vector_carrier n) V"
  shows "carrier_ambient_push k (vector_concat m n) p\<in>carrier_ambient_push k (vector_concat m n) ` R \<longleftrightarrow> p\<in>R"
  by (rule coordinate_bijection.carrier_relation_membership[OF assms])

lemma flattened_relation_recovered:
  assumes "R\<subseteq>U \<times> carrier_jet_domain k (vector_carrier m \<times> vector_carrier n) V"
  shows "carrier_ambient_push k (vector_split m n) ` (carrier_ambient_push k (vector_concat m n) ` R)=R"
  by (rule coordinate_bijection.carrier_relation_recovered[OF assms])

ML \<open>
val roots = @{thms flatten_inverse unflatten_inverse smoothness_preserved derivatives_preserved
 jet_flatten_derivative_order flatten_actual_jet numeric_time_preserved flattened_relation_membership flattened_relation_recovered};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
