theory Core_Native_Charts
 imports LCTR_Core_Exact_Structure.Core_Exact_Structure
begin

lemma inc_equivalence_on:
 assumes "strict_on A r" "inc_trans_on A r"
 shows "equiv A {(a,b). inc_on A r a b}"
 using assms unfolding equiv_def refl_on_def sym_def trans_def strict_on_def inc_trans_on_def inc_on_def by blast

theorem reverse_input_commutes:
 assumes "x\<in>A\<inter>B"
 shows "qproj B r x\<in>image(qproj B r)(B\<inter>A) \<and>
  image(qproj B r)(A\<inter>B)=image(qproj B r)(B\<inter>A)"
 using assms by auto

context order_pair
begin
theorem reversed_chart_is_inverse:
 assumes p: "p\<in>image(qproj A r)(A\<inter>B)"
 shows "overlap_change B A r (overlap_change A B r p)=p"
proof -
 obtain x where x: "x\<in>A\<inter>B" and px: "p=qproj A r x" using p by blast
 show ?thesis unfolding px by (simp only: overlap_change_commutes[OF x] reverse_change_commutes[OF x])
qed
end

theorem quotient_embedding_composition:
 assumes typed: "\<And>x. x\<in>A \<Longrightarrow> p x\<in>Q"
 and inj: "inj_on e Q"
 and ker: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> (p x=p y \<longleftrightarrow> same x y)"
 and ord: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> (ltQ(p x)(p y) \<longleftrightarrow> strict x y)"
 and emb: "\<And>a b. a\<in>Q \<Longrightarrow> b\<in>Q \<Longrightarrow> (ltY(e a)(e b) \<longleftrightarrow> ltQ a b)"
 shows "(\<forall>x\<in>A. \<forall>y\<in>A. e(p x)=e(p y) \<longleftrightarrow> same x y) \<and>
  (\<forall>x\<in>A. \<forall>y\<in>A. ltY(e(p x))(e(p y)) \<longleftrightarrow> strict x y)"
proof -
 have eq: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> (e(p x)=e(p y) \<longleftrightarrow> p x=p y)"
 proof -
  fix x y assume x: "x\<in>A" and y: "y\<in>A"
  have px: "p x\<in>Q" and py: "p y\<in>Q" using typed x y by auto
  show "e(p x)=e(p y) \<longleftrightarrow> p x=p y"
   using inj_on_eq_iff[OF inj px py] .
 qed
 have val: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> (e(p x)=e(p y) \<longleftrightarrow> same x y)"
  using eq ker by metis
 have rel: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> (ltY(e(p x))(e(p y)) \<longleftrightarrow> strict x y)"
 proof -
  fix x y assume x: "x\<in>A" and y: "y\<in>A"
  show "ltY(e(p x))(e(p y)) \<longleftrightarrow> strict x y"
   using emb[OF typed[OF x] typed[OF y]] ord[OF x y] by simp
 qed
 show ?thesis using val rel by blast
qed

context exact_structure
begin
theorem local_inc_equivalence:
 assumes h: "inc_trans_on (local_carrier u) canonical_lt"
 shows "equiv (local_carrier u) {(a,b). inc_on (local_carrier u) canonical_lt a b}"
 by (rule inc_equivalence_on[OF local_strict h])

theorem local_strict_invariance:
 assumes h: "inc_trans_on (local_carrier u) canonical_lt"
 and aa: "inc_on(local_carrier u)canonical_lt a a'"
 and bb: "inc_on(local_carrier u)canonical_lt b b'"
 shows "canonical_lt a b \<longleftrightarrow> canonical_lt a' b'"
 by (rule lt_invariant_under_inc[OF local_strict h aa bb])

theorem local_global_inc_restriction:
 assumes "a\<in>local_carrier u" "b\<in>local_carrier u"
 shows "inc_on(local_carrier u)canonical_lt a b \<longleftrightarrow> inc_on canonical_carrier canonical_lt a b"
 using assms local_subset unfolding inc_on_def by blast

theorem global_inc_equivalence:
 assumes h: "inc_trans_on canonical_carrier canonical_lt"
 shows "equiv canonical_carrier {(a,b). inc_on canonical_carrier canonical_lt a b}"
 by (rule inc_equivalence_on[OF strict_part_contract h])

theorem global_strict_invariance:
 assumes h: "inc_trans_on canonical_carrier canonical_lt"
 and aa: "inc_on canonical_carrier canonical_lt a a'"
 and bb: "inc_on canonical_carrier canonical_lt b b'"
 shows "canonical_lt a b \<longleftrightarrow> canonical_lt a' b'"
 by (rule lt_invariant_under_inc[OF strict_part_contract h aa bb])

lemma local_pair:
 assumes hi: "inc_trans_on(local_carrier i)canonical_lt"
 and hj: "inc_trans_on(local_carrier j)canonical_lt"
 shows "order_pair (local_carrier i) (local_carrier j) canonical_lt"
 by unfold_locales (rule local_strict, fact hi, rule local_strict, fact hj)

theorem actual_chart_change_order:
 assumes hi: "inc_trans_on(local_carrier i)canonical_lt"
 and hj: "inc_trans_on(local_carrier j)canonical_lt"
 and a: "a\<in>image(qproj(local_carrier i)canonical_lt)(local_carrier i\<inter>local_carrier j)"
 and b: "b\<in>image(qproj(local_carrier i)canonical_lt)(local_carrier i\<inter>local_carrier j)"
 shows "qlt(local_carrier j)canonical_lt
  (overlap_change(local_carrier i)(local_carrier j)canonical_lt a)
  (overlap_change(local_carrier i)(local_carrier j)canonical_lt b)
  \<longleftrightarrow> qlt(local_carrier i)canonical_lt a b"
proof -
 interpret P: order_pair "local_carrier i" "local_carrier j" canonical_lt by (rule local_pair[OF hi hj])
 show ?thesis by (rule P.overlap_order[OF a b])
qed

theorem actual_chart_change_inverse:
 assumes hi: "inc_trans_on(local_carrier i)canonical_lt"
 and hj: "inc_trans_on(local_carrier j)canonical_lt"
 and p: "p\<in>image(qproj(local_carrier i)canonical_lt)(local_carrier i\<inter>local_carrier j)"
 shows "overlap_change(local_carrier j)(local_carrier i)canonical_lt
  (overlap_change(local_carrier i)(local_carrier j)canonical_lt p)=p"
proof -
 interpret P: order_pair "local_carrier i" "local_carrier j" canonical_lt by (rule local_pair[OF hi hj])
 show ?thesis by (rule P.reversed_chart_is_inverse[OF p])
qed

theorem actual_chart_change_identity:
 assumes hi: "inc_trans_on(local_carrier i)canonical_lt"
 and p: "p\<in>image(qproj(local_carrier i)canonical_lt)(local_carrier i\<inter>local_carrier i)"
 shows "overlap_change(local_carrier i)(local_carrier i)canonical_lt p=p"
proof -
 have d: "order_domain(local_carrier i)canonical_lt" by standard (rule local_strict, fact hi)
 have mem: "p\<in>QuSet(local_carrier i)canonical_lt" using p by (simp add: QuSet_def)
 show ?thesis by (rule self_change_identity[OF d mem])
qed

theorem actual_triple_cocycle:
 assumes hi: "inc_trans_on(local_carrier i)canonical_lt"
 and hj: "inc_trans_on(local_carrier j)canonical_lt"
 and hk: "inc_trans_on(local_carrier k)canonical_lt"
 and x: "x\<in>local_carrier i\<inter>local_carrier j\<inter>local_carrier k"
 shows "overlap_change(local_carrier j)(local_carrier k)canonical_lt
  (overlap_change(local_carrier i)(local_carrier j)canonical_lt(qproj(local_carrier i)canonical_lt x))
  =overlap_change(local_carrier i)(local_carrier k)canonical_lt(qproj(local_carrier i)canonical_lt x)"
proof -
 interpret T: order_triple "local_carrier i" "local_carrier j" "local_carrier k" canonical_lt
  by unfold_locales (rule local_strict, fact hi, rule local_strict, fact hj, rule local_strict, fact hk)
 show ?thesis by (rule T.triple_overlap_cocycle[OF x])
qed

theorem actual_representation_contract:
 assumes hg: "inc_trans_on canonical_carrier canonical_lt"
 and inj: "inj_on emb (QuSet canonical_carrier canonical_lt)"
 and order: "\<And>a b. a\<in>QuSet canonical_carrier canonical_lt \<Longrightarrow>
  b\<in>QuSet canonical_carrier canonical_lt \<Longrightarrow> (lt(emb a)(emb b) \<longleftrightarrow> qlt canonical_carrier canonical_lt a b)"
 shows "(\<forall>x\<in>canonical_carrier. \<forall>y\<in>canonical_carrier.
  represented emb x=represented emb y \<longleftrightarrow> \<not>canonical_lt x y \<and> \<not>canonical_lt y x) \<and>
  (\<forall>x\<in>canonical_carrier. \<forall>y\<in>canonical_carrier.
  lt(represented emb x)(represented emb y) \<longleftrightarrow> canonical_lt x y)"
 using represented_kernel[OF hg inj]
  represented_order_pullback[where emb=emb and lt=lt, OF hg order] by blast

theorem actual_chart_composition:
 assumes h: "inc_trans_on(local_carrier u)canonical_lt"
 shows "local_chart u=qproj(local_carrier u)canonical_lt \<circ> canonical_projection \<and>
  image(local_chart u)(regions D f u)=QuSet(local_carrier u)canonical_lt \<and>
  (\<forall>a\<in>regions D f u. \<forall>b\<in>regions D f u. local_chart u a=local_chart u b \<longleftrightarrow>
   \<not>canonical_lt(canonical_projection a)(canonical_projection b) \<and>
   \<not>canonical_lt(canonical_projection b)(canonical_projection a)) \<and>
  (\<forall>a\<in>regions D f u. \<forall>b\<in>regions D f u.
   qlt(local_carrier u)canonical_lt(local_chart u a)(local_chart u b) \<longleftrightarrow>
   canonical_lt(canonical_projection a)(canonical_projection b))"
 using actual_local_chart_contract[OF h] local_chart_def by blast
end

ML \<open>
val roots = @{thms exact_structure.local_inc_equivalence exact_structure.local_strict_invariance
 exact_structure.local_global_inc_restriction exact_structure.global_inc_equivalence
 exact_structure.global_strict_invariance reverse_input_commutes order_pair.reversed_chart_is_inverse
 exact_structure.actual_chart_change_order exact_structure.actual_chart_change_inverse
 exact_structure.actual_chart_change_identity exact_structure.actual_triple_cocycle
 quotient_embedding_composition exact_structure.actual_representation_contract exact_structure.actual_chart_composition};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
