theory Law_Index_Encoding
  imports "LCTR_Full_Carrier_Family_Transport.Full_Carrier_Family_Transport"
begin

locale law_index_encoding = ix: carrier_bijection A B f g
  for A :: "'a set" and B :: "'b set" and f :: "'a\<Rightarrow>'b" and g :: "'b\<Rightarrow>'a" +
  fixes d :: "('t,'a,'x,'y) law_family"
  assumes source_indices: "law_indices d=A" and wf: "well_typed_family d"
begin

lemma index_ball_iff: "(\<forall>b\<in>B. P(g b)) \<longleftrightarrow> (\<forall>a\<in>A. P a)"
proof
  assume h: "\<forall>b\<in>B. P(g b)"
  show "\<forall>a\<in>A. P a"
  proof
    fix a assume a: "a\<in>A"
    have fb: "f a\<in>B" using ix.forward_typed a by blast
    show "P a" using h[rule_format, OF fb] ix.left_inverse[OF a] by simp
  qed
next
  assume h: "\<forall>a\<in>A. P a"
  show "\<forall>b\<in>B. P(g b)" using h ix.inverse_typed by blast
qed

definition pulled where "pulled phi b=phi(g b)"
definition index_agrees where
  "index_agrees phi psi \<longleftrightarrow> (\<forall>b\<in>B. \<forall>z\<in>tuple_carrier d (g b).
    forward_map(psi b)z=forward_map(pulled phi b)z \<and>
    inverse_map(psi b)z=inverse_map(pulled phi b)z)"
definition encoded where
  "encoded=\<lparr>time_carrier=time_carrier d, law_indices=B,
    input_carrier=input_carrier d \<circ> g, output_carrier=output_carrier d \<circ> g,
    components=components d \<circ> g, admissible_common=admissible_common d,
    faithful_family=(\<lambda>psi. \<exists>phi. typed_reindex_family d phi \<and>
      faithful_family d phi \<and> index_agrees phi psi)\<rparr>"

lemma selectors [simp]:
  "time_carrier encoded=time_carrier d" "law_indices encoded=B"
  "input_carrier encoded b=input_carrier d (g b)"
  "output_carrier encoded b=output_carrier d (g b)"
  "components encoded b=components d (g b)"
  "admissible_common encoded=admissible_common d"
  "tuple_carrier encoded b=tuple_carrier d (g b)"
  by (simp_all add: encoded_def tuple_carrier_def)

lemma pulled_typed:
  "typed_reindex_family d phi \<Longrightarrow> typed_reindex_family encoded(pulled phi)"
  using index_ball_iff[of "\<lambda>a. reindex_on (tuple_carrier d a) (phi a)"]
  by (simp only: typed_reindex_family_def selectors pulled_def source_indices)

lemma index_agrees_invariance:
  assumes b: "b\<in>B" and eq: "index_agrees phi psi"
  shows "image_invariant(components encoded b)(psi b) =
    image_invariant(components d(g b))(pulled phi b)"
proof -
  have a: "g b\<in>law_indices d" using ix.inverse_typed b source_indices by blast
  have sub: "law_relation(components d(g b))\<subseteq>tuple_carrier d(g b)"
    by (rule relation_subset_tuple[OF wf a])
  have same: "\<And>z. z\<in>law_relation(components d(g b)) \<Longrightarrow>
    forward_map(psi b)z=forward_map(pulled phi b)z"
    using sub eq b unfolding index_agrees_def by blast
  have im: "forward_map(psi b) ` law_relation(components d(g b)) =
    forward_map(pulled phi b) ` law_relation(components d(g b))"
    by (rule image_cong[OF refl same])
  show ?thesis by (simp only: selectors image_invariant_def im)
qed

lemma condition1: "K1 encoded\<longleftrightarrow>K1 d"
  using index_ball_iff[of "\<lambda>a. individual_admissible(components d a)"]
  by (simp only: K1_def selectors source_indices)
lemma condition2: "K2 encoded\<longleftrightarrow>K2 d"
  using index_ball_iff[of "\<lambda>a. right_unique(components d a)"]
  by (simp only: K2_def selectors source_indices)
lemma condition3: "K3 encoded\<longleftrightarrow>K3 d"
  using index_ball_iff[of "\<lambda>a. generated_member(components d a)"]
  by (simp only: K3_def condition1 selectors source_indices)

lemma condition4: "K4 encoded\<longleftrightarrow>K4 d"
proof
  assume h: "K4 encoded"
  show "K4 d" unfolding K4_def
  proof (intro allI impI ballI)
    fix phi a
    assume phi: "typed_reindex_family d phi" and faith: "faithful_family d phi"
      and a: "a\<in>law_indices d"
    have aa: "a\<in>A" using a source_indices by simp
    have fb: "f a\<in>B" using ix.forward_typed aa by blast
    have pt: "typed_reindex_family encoded(pulled phi)" by (rule pulled_typed[OF phi])
    have pf: "faithful_family encoded(pulled phi)"
      using phi faith unfolding encoded_def index_agrees_def by auto
    have inv: "image_invariant(components encoded(f a))(pulled phi(f a))"
      using h pt pf fb unfolding K4_def by auto
    show "image_invariant(components d a)(phi a)"
      using inv by (simp add: pulled_def ix.left_inverse[OF aa])
  qed
next
  assume h: "K4 d"
  show "K4 encoded" unfolding K4_def
  proof (intro allI impI ballI)
    fix psi b
    assume psi: "typed_reindex_family encoded psi" and faith: "faithful_family encoded psi"
      and b: "b\<in>law_indices encoded"
    have bb: "b\<in>B" using b by simp
    have aa: "g b\<in>law_indices d" using ix.inverse_typed bb source_indices by blast
    obtain phi where phi: "typed_reindex_family d phi" and pf: "faithful_family d phi"
      and eq: "index_agrees phi psi" using faith unfolding encoded_def by auto
    have inv: "image_invariant(components d(g b))(phi(g b))"
      using h phi pf aa unfolding K4_def by blast
    show "image_invariant(components encoded b)(psi b)"
      using inv index_agrees_invariance[OF bb eq] by (simp only: pulled_def)
  qed
qed

lemma common_times_preserved: "common_times encoded=common_times d"
proof -
  have eq: "(\<forall>b\<in>B. t\<in>valid_times(components d(g b))) \<longleftrightarrow>
      (\<forall>a\<in>A. t\<in>valid_times(components d a))" for t
    by (rule index_ball_iff)
  show ?thesis by (simp only: common_times_def selectors source_indices eq)
qed
lemma condition5: "K5 encoded\<longleftrightarrow>K5 d"
  by (simp add: K5_def condition3 common_times_preserved)

lemma five_conditions:
  "(K1 encoded\<longleftrightarrow>K1 d) \<and> (K2 encoded\<longleftrightarrow>K2 d) \<and>
   (K3 encoded\<longleftrightarrow>K3 d) \<and> (K4 encoded\<longleftrightarrow>K4 d) \<and>
   (K5 encoded\<longleftrightarrow>K5 d)"
  using condition1 condition2 condition3 condition4 condition5 by blast
lemma all_conditions_preserved: "all_conditions encoded\<longleftrightarrow>all_conditions d"
  by (simp only: all_conditions_def condition1 condition2 condition3 condition4 condition5)

lemma encoded_well_typed: "well_typed_family encoded"
proof -
  have an: "A\<noteq>{}" using wf unfolding well_typed_family_def source_indices by blast
  have bn: "B\<noteq>{}" using ix.surjective an by auto
  have ext: "\<And>p q. same_reindex_family encoded p q \<Longrightarrow>
    faithful_family encoded p \<longleftrightarrow> faithful_family encoded q"
  proof -
    fix p q :: "'b\<Rightarrow>(('t\<times>'x)\<times>'y) carrier_reindex"
    assume same: "same_reindex_family encoded p q"
    have eq: "\<And>phi. index_agrees phi p \<longleftrightarrow> index_agrees phi q"
      using same unfolding same_reindex_family_def index_agrees_def by auto
    show "faithful_family encoded p \<longleftrightarrow> faithful_family encoded q"
      by (simp only: encoded_def law_family.select_convs eq)
  qed
  have bounds: "\<forall>b\<in>B.
    eval_times(components d(g b))\<subseteq>time_carrier d \<and>
    input_value(components d(g b)) ` eval_times(components d(g b))\<subseteq>input_carrier d(g b) \<and>
    output_value(components d(g b)) ` eval_times(components d(g b))\<subseteq>output_carrier d(g b) \<and>
    eval_domain(components d(g b))\<subseteq>time_carrier d\<times>input_carrier d(g b) \<and>
    law_relation(components d(g b))\<subseteq>eval_domain(components d(g b))\<times>output_carrier d(g b)"
  proof
    fix b assume b: "b\<in>B"
    have a: "g b\<in>law_indices d" using ix.inverse_typed b source_indices by blast
    show "eval_times(components d(g b))\<subseteq>time_carrier d \<and>
      input_value(components d(g b)) ` eval_times(components d(g b))\<subseteq>input_carrier d(g b) \<and>
      output_value(components d(g b)) ` eval_times(components d(g b))\<subseteq>output_carrier d(g b) \<and>
      eval_domain(components d(g b))\<subseteq>time_carrier d\<times>input_carrier d(g b) \<and>
      law_relation(components d(g b))\<subseteq>eval_domain(components d(g b))\<times>output_carrier d(g b)"
      using wf a unfolding well_typed_family_def by blast
  qed
  show ?thesis unfolding well_typed_family_def
  proof (intro conjI)
    show "law_indices encoded\<noteq>{}" using bn by simp
    show "\<forall>a\<in>law_indices encoded.
      eval_times(components encoded a)\<subseteq>time_carrier encoded \<and>
      input_value(components encoded a) ` eval_times(components encoded a)\<subseteq>input_carrier encoded a \<and>
      output_value(components encoded a) ` eval_times(components encoded a)\<subseteq>output_carrier encoded a \<and>
      eval_domain(components encoded a)\<subseteq>time_carrier encoded\<times>input_carrier encoded a \<and>
      law_relation(components encoded a)\<subseteq>eval_domain(components encoded a)\<times>output_carrier encoded a"
      using bounds by (simp only: selectors)
    show "\<forall>p q. typed_reindex_family encoded p \<longrightarrow> typed_reindex_family encoded q \<longrightarrow>
      same_reindex_family encoded p q \<longrightarrow>
      (faithful_family encoded p \<longleftrightarrow> faithful_family encoded q)"
      using ext by blast
  qed
qed

end

ML \<open>
val roots = @{thms law_index_encoding.index_ball_iff law_index_encoding.pulled_typed
 law_index_encoding.condition1 law_index_encoding.condition2 law_index_encoding.condition3
 law_index_encoding.condition4 law_index_encoding.common_times_preserved law_index_encoding.condition5
 law_index_encoding.five_conditions law_index_encoding.all_conditions_preserved
 law_index_encoding.encoded_well_typed};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
