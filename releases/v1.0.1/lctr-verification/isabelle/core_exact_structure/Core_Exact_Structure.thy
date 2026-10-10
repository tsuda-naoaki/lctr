theory Core_Exact_Structure
 imports LCTR_Core_Order_Atlas.Core_Order_Atlas
 LCTR_Core_Comparison_Integration.Core_Comparison_Integration
begin

abbreviation native_carrier where "native_carrier D f \<equiv> (\<Union>u. regions D f u)"
abbreviation native_equiv where
 "native_equiv D f tr adm \<equiv> {(a,b). typed_actions.orbit
  (regions D f) {e. admitted adm e} initial terminal (cmp_act D f tr) a b}"

locale exact_structure = native_comparison D f tr adm
 for D :: "'u\<Rightarrow>'s set" and f :: "'u\<Rightarrow>'s\<Rightarrow>'v"
 and tr :: "'u\<Rightarrow>'u\<Rightarrow>'v\<Rightarrow>'v\<Rightarrow>bool"
 and adm :: "'u\<Rightarrow>'u\<Rightarrow>bool" +
 fixes r :: "'s\<Rightarrow>'s\<Rightarrow>bool"
 assumes source_pre: "pre_on UNIV r"
 and source_anti: "\<And>x y. r x y \<Longrightarrow> r y x \<Longrightarrow> x=y"
 and descent: "ord_desc (native_carrier D f) (native_equiv D f tr adm)
  (pullback (native_comparison.recover_tag D f) r)"
begin

interpretation W: typed_actions "regions D f" "{e. admitted adm e}" initial terminal inverted "cmp_act D f tr"
proof
  fix e assume "e\<in>{e. admitted adm e}"
  then show "inverted e\<in>{e. admitted adm e}" by (cases e) auto
next
  fix e assume "e\<in>{e. admitted adm e}"
  show "initial (inverted e)=terminal e" by (cases e) auto
next
  fix e assume "e\<in>{e. admitted adm e}"
  show "terminal (inverted e)=initial e" by (cases e) auto
next
  fix e assume "e\<in>{e. admitted adm e}"
  show "inverted (inverted e)=e" by (cases e) auto
next
  fix e p q assume "e\<in>{e. admitted adm e}" and pq: "cmp_act D f tr e p q"
  show "p\<in>regions D f (initial e) \<and> q\<in>regions D f (terminal e)" by (rule atom_type[OF pq])
next
  fix e p q r assume "e\<in>{e. admitted adm e}" and "cmp_act D f tr e p q" and "cmp_act D f tr e p r"
  then show "q=r" using atom_functional by auto
next
  fix e p q assume "e\<in>{e. admitted adm e}"
  show "cmp_act D f tr (inverted e) q p = cmp_act D f tr e p q" by (rule atom_inverse)
qed

definition canonical_carrier where
 "canonical_carrier=(native_carrier D f)//(native_equiv D f tr adm)"
definition canonical_projection where
 "canonical_projection x=Image (native_equiv D f tr adm) {x}"
definition canonical_le where
 "canonical_le=qrel (native_carrier D f) (native_equiv D f tr adm) (pullback recover_tag r)"
definition canonical_lt where "canonical_lt x y=(canonical_le x y \<and> x\<noteq>y)"
definition local_carrier where
 "local_carrier u=image canonical_projection (regions D f u)"
definition local_chart where "local_chart u=qproj (local_carrier u) canonical_lt \<circ> canonical_projection"
definition local_global where
 "local_global u=order_inclusion (local_carrier u) canonical_carrier canonical_lt"
definition represented where "represented emb=emb \<circ> qproj canonical_carrier canonical_lt"

lemma native_equivalence: "equiv (native_carrier D f) (native_equiv D f tr adm)"
 using comparison_equivalence unfolding W.carrier_def .
lemma projection_maps:
 "x\<in>native_carrier D f \<Longrightarrow> canonical_projection x\<in>canonical_carrier"
 by (auto simp: canonical_projection_def canonical_carrier_def quotient_def)

theorem canonical_partial_order: "part_on canonical_carrier canonical_le"
 using canonical_comparison_partial_order[OF source_pre source_anti] descent
 unfolding canonical_carrier_def canonical_le_def W.carrier_def by blast
theorem canonical_order_representatives:
 assumes x: "x\<in>native_carrier D f" and y: "y\<in>native_carrier D f"
 shows "canonical_le (canonical_projection x)(canonical_projection y) \<longleftrightarrow> r(recover_tag x)(recover_tag y)"
 using quotient_on_representatives[OF native_equivalence descent x y]
 by (simp add: canonical_le_def canonical_projection_def pullback_def)
theorem strict_part_contract: "strict_on canonical_carrier canonical_lt"
 using canonical_partial_order
 unfolding part_on_def pre_on_def strict_on_def canonical_lt_def by blast

theorem receive_onto:
 "image canonical_projection (regions D f u)=local_carrier u"
 by (simp add: local_carrier_def)
lemma local_subset: "local_carrier u\<subseteq>canonical_carrier"
 using projection_maps unfolding local_carrier_def by blast
lemma local_strict: "strict_on (local_carrier u) canonical_lt"
 using strict_part_contract local_subset unfolding strict_on_def by blast

theorem actual_local_chart_contract:
 assumes h: "inc_trans_on (local_carrier u) canonical_lt"
 shows "image(local_chart u)(regions D f u)=QuSet(local_carrier u)canonical_lt \<and>
  (\<forall>a\<in>regions D f u. \<forall>b\<in>regions D f u. local_chart u a=local_chart u b \<longleftrightarrow>
   \<not>canonical_lt(canonical_projection a)(canonical_projection b) \<and>
   \<not>canonical_lt(canonical_projection b)(canonical_projection a)) \<and>
  (\<forall>a\<in>regions D f u. \<forall>b\<in>regions D f u.
   qlt(local_carrier u)canonical_lt(local_chart u a)(local_chart u b) \<longleftrightarrow>
   canonical_lt(canonical_projection a)(canonical_projection b))"
proof -
 interpret L: order_domain "local_carrier u" canonical_lt by standard (rule local_strict, fact h)
 show ?thesis using L.composite_chart_contract[OF receive_onto] unfolding local_chart_def by simp
qed

theorem actual_local_quotient_linear:
 assumes h: "inc_trans_on (local_carrier u) canonical_lt"
 shows "Order_Embedding_Isabelle.strict_linear_on
  (QuSet(local_carrier u)canonical_lt)(qlt(local_carrier u)canonical_lt)"
proof -
 interpret L: order_domain "local_carrier u" canonical_lt by standard (rule local_strict, fact h)
 show ?thesis by (rule L.quotient_strict_linear)
qed

theorem global_implies_local_inc:
 assumes h: "inc_trans_on canonical_carrier canonical_lt"
 shows "inc_trans_on (local_carrier u) canonical_lt"
 using h local_subset unfolding inc_trans_on_def inc_on_def by blast

lemma local_global_pair:
 assumes hl: "inc_trans_on (local_carrier u) canonical_lt"
 and hg: "inc_trans_on canonical_carrier canonical_lt"
 shows "order_pair (local_carrier u) canonical_carrier canonical_lt"
 by unfold_locales (rule local_strict, fact hl, rule strict_part_contract, fact hg)

theorem local_global_commutes:
 assumes hl: "inc_trans_on (local_carrier u) canonical_lt"
 and hg: "inc_trans_on canonical_carrier canonical_lt" and x: "x\<in>local_carrier u"
 shows "local_global u (qproj(local_carrier u)canonical_lt x)=qproj canonical_carrier canonical_lt x"
proof -
 interpret LG: order_pair "local_carrier u" canonical_carrier canonical_lt
  by (rule local_global_pair[OF hl hg])
 show ?thesis unfolding local_global_def by (rule LG.inclusion_commutes[OF local_subset x])
qed

theorem local_global_injective:
 assumes hl: "inc_trans_on (local_carrier u) canonical_lt"
 and hg: "inc_trans_on canonical_carrier canonical_lt"
 shows "inj_on (local_global u) (QuSet(local_carrier u)canonical_lt)"
proof -
 interpret LG: order_pair "local_carrier u" canonical_carrier canonical_lt
  by (rule local_global_pair[OF hl hg])
 show ?thesis unfolding local_global_def by (rule LG.inclusion_injective[OF local_subset])
qed

theorem local_global_order:
 assumes hl: "inc_trans_on (local_carrier u) canonical_lt"
 and hg: "inc_trans_on canonical_carrier canonical_lt"
 and a: "a\<in>QuSet(local_carrier u)canonical_lt" and b: "b\<in>QuSet(local_carrier u)canonical_lt"
 shows "qlt canonical_carrier canonical_lt(local_global u a)(local_global u b)
  \<longleftrightarrow> qlt(local_carrier u)canonical_lt a b"
proof -
 interpret LG: order_pair "local_carrier u" canonical_carrier canonical_lt
  by (rule local_global_pair[OF hl hg])
 show ?thesis unfolding local_global_def by (rule LG.inclusion_order[OF local_subset a b])
qed

theorem actual_global_quotient_linear:
 assumes hg: "inc_trans_on canonical_carrier canonical_lt"
 shows "Order_Embedding_Isabelle.strict_linear_on
  (QuSet canonical_carrier canonical_lt)(qlt canonical_carrier canonical_lt)"
proof -
 interpret G: order_domain canonical_carrier canonical_lt by standard (rule strict_part_contract, fact hg)
 show ?thesis by (rule G.quotient_strict_linear)
qed

theorem local_global_chart_commutes:
 assumes hl: "inc_trans_on (local_carrier u) canonical_lt"
 and hg: "inc_trans_on canonical_carrier canonical_lt" and a: "a\<in>regions D f u"
 shows "local_global u (local_chart u a)=qproj canonical_carrier canonical_lt(canonical_projection a)"
proof -
 have mem: "canonical_projection a\<in>local_carrier u" using a unfolding local_carrier_def by blast
 show ?thesis using local_global_commutes[OF hl hg mem] unfolding local_chart_def by simp
qed

theorem chosen_representation_compatibility:
 assumes hl: "inc_trans_on (local_carrier u) canonical_lt"
 and hg: "inc_trans_on canonical_carrier canonical_lt" and a: "a\<in>regions D f u"
 shows "represented emb (canonical_projection a)=emb(local_global u (local_chart u a))"
 using local_global_chart_commutes[OF hl hg a] unfolding represented_def by simp

theorem represented_order_pullback:
 assumes hg: "inc_trans_on canonical_carrier canonical_lt"
 and order: "\<And>a b. a\<in>QuSet canonical_carrier canonical_lt \<Longrightarrow>
  b\<in>QuSet canonical_carrier canonical_lt \<Longrightarrow> (lt(emb a)(emb b) \<longleftrightarrow> qlt canonical_carrier canonical_lt a b)"
 and x: "x\<in>canonical_carrier" and y: "y\<in>canonical_carrier"
 shows "lt(represented emb x)(represented emb y) \<longleftrightarrow> canonical_lt x y"
proof -
 have px: "qproj canonical_carrier canonical_lt x\<in>QuSet canonical_carrier canonical_lt" using x by (auto simp: QuSet_def)
 have py: "qproj canonical_carrier canonical_lt y\<in>QuSet canonical_carrier canonical_lt" using y by (auto simp: QuSet_def)
 show ?thesis using order[OF px py] qproj_order_iff[OF strict_part_contract hg x y]
  unfolding represented_def by simp
qed

theorem represented_kernel:
 assumes hg: "inc_trans_on canonical_carrier canonical_lt"
 and inj: "inj_on emb (QuSet canonical_carrier canonical_lt)"
 and x: "x\<in>canonical_carrier" and y: "y\<in>canonical_carrier"
 shows "represented emb x=represented emb y \<longleftrightarrow> \<not>canonical_lt x y \<and> \<not>canonical_lt y x"
proof -
 have px: "qproj canonical_carrier canonical_lt x\<in>QuSet canonical_carrier canonical_lt" using x by (auto simp: QuSet_def)
 have py: "qproj canonical_carrier canonical_lt y\<in>QuSet canonical_carrier canonical_lt" using y by (auto simp: QuSet_def)
 have eq: "emb(qproj canonical_carrier canonical_lt x)=emb(qproj canonical_carrier canonical_lt y)
  \<longleftrightarrow> qproj canonical_carrier canonical_lt x=qproj canonical_carrier canonical_lt y"
  using inj px py unfolding inj_on_def by auto
 show ?thesis using eq qproj_class_iff[OF strict_part_contract hg x y] x y
  unfolding represented_def inc_on_def by simp
qed
end

ML \<open>
val roots = @{thms exact_structure.canonical_partial_order exact_structure.canonical_order_representatives
 exact_structure.strict_part_contract exact_structure.receive_onto
 exact_structure.actual_local_chart_contract exact_structure.actual_local_quotient_linear
 exact_structure.global_implies_local_inc exact_structure.local_global_commutes
 exact_structure.local_global_injective exact_structure.local_global_order
 exact_structure.actual_global_quotient_linear exact_structure.local_global_chart_commutes
 exact_structure.chosen_representation_compatibility exact_structure.represented_order_pullback
 exact_structure.represented_kernel};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
