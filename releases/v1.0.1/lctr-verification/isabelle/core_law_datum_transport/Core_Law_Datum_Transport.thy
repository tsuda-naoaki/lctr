theory Core_Law_Datum_Transport
 imports "LCTR_Core_Law_Datum_Assembly.Core_Law_Datum_Assembly"
   "LCTR_Core_Law_Transport.Core_Law_Family_Transport"
begin

context law_transport
begin
definition outer_moved where "outer_moved e=assemble e target"

lemma target_family_typed: "well_typed_family target"
proof -
 have ne: "law_indices d\<noteq>{}" using wf unfolding well_typed_family_def by blast
 have data: "\<forall>a\<in>law_indices d.
   eval_times(moved a)\<subseteq>U \<and>
   input_value(moved a) ` eval_times(moved a)\<subseteq>input_carrier d a \<and>
   output_value(moved a) ` eval_times(moved a)\<subseteq>output_carrier d a \<and>
   eval_domain(moved a)\<subseteq>U\<times>input_carrier d a \<and>
   law_relation(moved a)\<subseteq>eval_domain(moved a)\<times>output_carrier d a"
 proof (intro ballI)
  fix a assume a: "a\<in>law_indices d"
  have src: "eval_times(old a)\<subseteq>T \<and>
   input_value(old a) ` eval_times(old a)\<subseteq>input_carrier d a \<and>
   output_value(old a) ` eval_times(old a)\<subseteq>output_carrier d a \<and>
   eval_domain(old a)\<subseteq>T\<times>input_carrier d a \<and>
   law_relation(old a)\<subseteq>eval_domain(old a)\<times>output_carrier d a"
   using wf a unfolding well_typed_family_def source_time by blast
  have hs: "eval_times(old a)\<subseteq>T" using src by blast
  have ins: "input_value(old a) ` eval_times(old a)\<subseteq>input_carrier d a" using src by blast
  have outs: "output_value(old a) ` eval_times(old a)\<subseteq>output_carrier d a" using src by blast
  have es: "eval_domain(old a)\<subseteq>T\<times>input_carrier d a" using src by blast
  have rs: "law_relation(old a)\<subseteq>eval_domain(old a)\<times>output_carrier d a" using src by blast
  have times: "eval_times(moved a)\<subseteq>U"
  proof -
   have fi: "f ` eval_times(old a)\<subseteq>f ` T" by (rule image_mono[OF hs])
   have fu: "f ` eval_times(old a)\<subseteq>U" by (rule subset_trans[OF fi forward_typed])
   show ?thesis using fu by (simp only: component_transport_def law_component.select_convs)
  qed
  have preimage_eq: "g ` eval_times(moved a)=eval_times(old a)"
   using inverse_image[OF hs] by (simp add: component_transport_def)
  have intyped: "input_value(moved a) ` eval_times(moved a)\<subseteq>input_carrier d a"
  proof -
   have cmp: "input_value(moved a)=input_value(old a) \<circ> g"
    by (simp only: component_transport_def law_component.select_convs)
   show ?thesis by (simp only: cmp image_comp[symmetric] preimage_eq; rule ins)
  qed
  have outtyped: "output_value(moved a) ` eval_times(moved a)\<subseteq>output_carrier d a"
  proof -
   have cmp: "output_value(moved a)=output_value(old a) \<circ> g"
    by (simp only: component_transport_def law_component.select_convs)
   show ?thesis by (simp only: cmp image_comp[symmetric] preimage_eq; rule outs)
  qed
  have dom_typed: "eval_domain(moved a)\<subseteq>U\<times>input_carrier d a"
   using es forward_typed by (auto simp: component_transport_def pair_change_def; blast)
  have rel_typed: "law_relation(moved a)\<subseteq>eval_domain(moved a)\<times>output_carrier d a"
  proof -
   have image_member: "\<forall>z\<in>law_relation(old a).
     tuple_change f z\<in>(pair_change f ` eval_domain(old a))\<times>output_carrier d a"
   proof (intro ballI)
    fix z assume z: "z\<in>law_relation(old a)"
    have p: "fst z\<in>eval_domain(old a)" and y: "snd z\<in>output_carrier d a"
     using rs z by auto
    have fp: "pair_change f (fst z)\<in>pair_change f ` eval_domain(old a)" by (rule imageI[OF p])
    show "tuple_change f z\<in>(pair_change f ` eval_domain(old a))\<times>output_carrier d a"
     using fp y by (simp add: tuple_change_def pair_change_def)
   qed
   show ?thesis using image_member by (auto simp: component_transport_def)
  qed
  show "eval_times(moved a)\<subseteq>U \<and>
   input_value(moved a) ` eval_times(moved a)\<subseteq>input_carrier d a \<and>
   output_value(moved a) ` eval_times(moved a)\<subseteq>output_carrier d a \<and>
   eval_domain(moved a)\<subseteq>U\<times>input_carrier d a \<and>
   law_relation(moved a)\<subseteq>eval_domain(moved a)\<times>output_carrier d a"
   using times intyped outtyped dom_typed rel_typed by blast
 qed
 have ext: "\<forall>p q. typed_reindex_family target p \<longrightarrow> typed_reindex_family target q \<longrightarrow>
   same_reindex_family target p q \<longrightarrow> (faithful_family target p \<longleftrightarrow> faithful_family target q)"
 proof (intro allI impI)
  fix p q :: "'a \<Rightarrow> (('u \<times> 'x) \<times> 'y) carrier_reindex"
  assume pt: "typed_reindex_family target p" and qt: "typed_reindex_family target q"
   and eq: "same_reindex_family target p q"
  have maps: "\<forall>a\<in>law_indices d. \<forall>z\<in>(U\<times>input_carrier d a)\<times>output_carrier d a.
    forward_map(p a)z=forward_map(q a)z \<and> inverse_map(p a)z=inverse_map(q a)z"
   using eq by (simp add: same_reindex_family_def tuple_carrier_def)
  have cong: "\<And>phi. conjugates phi p \<longleftrightarrow> conjugates phi q"
  proof -
   fix phi
   have point: "\<And>a z. a\<in>law_indices d \<Longrightarrow>
     z\<in>(U\<times>input_carrier d a)\<times>output_carrier d a \<Longrightarrow>
     (forward_map(p a)z=forward_map(conjugated phi a)z \<and>
      inverse_map(p a)z=inverse_map(conjugated phi a)z) \<longleftrightarrow>
     (forward_map(q a)z=forward_map(conjugated phi a)z \<and>
      inverse_map(q a)z=inverse_map(conjugated phi a)z)"
   proof -
    fix a z
    assume a: "a\<in>law_indices d" and z: "z\<in>(U\<times>input_carrier d a)\<times>output_carrier d a"
    have fwd: "forward_map(p a)z=forward_map(q a)z"
     and inv: "inverse_map(p a)z=inverse_map(q a)z" using maps a z by blast+
    show "(forward_map(p a)z=forward_map(conjugated phi a)z \<and>
      inverse_map(p a)z=inverse_map(conjugated phi a)z) \<longleftrightarrow>
     (forward_map(q a)z=forward_map(conjugated phi a)z \<and>
      inverse_map(q a)z=inverse_map(conjugated phi a)z)" by (simp only: fwd inv)
   qed
   show "conjugates phi p \<longleftrightarrow> conjugates phi q"
    using point unfolding conjugates_def by blast
  qed
  have fp: "faithful_family target p \<longleftrightarrow>
    (\<exists>phi. typed_reindex_family d phi \<and> faithful_family d phi \<and> conjugates phi p)"
   by (simp add: target_def)
  have fq: "faithful_family target q \<longleftrightarrow>
    (\<exists>phi. typed_reindex_family d phi \<and> faithful_family d phi \<and> conjugates phi q)"
   by (simp add: target_def)
  show "faithful_family target p \<longleftrightarrow> faithful_family target q"
   by (simp only: fp fq cong)
 qed
 show ?thesis using ne data ext unfolding well_typed_family_def by (simp only: selectors; blast)
qed

lemma specification_preserved: "eval_spec(outer_moved e)=e"
 by (simp add: outer_moved_def assemble_def)

lemma condition_preserved:
 "Core_Native_Law_Family.condition (family(outer_moved e)) i \<longleftrightarrow>
  Core_Native_Law_Family.condition d i"
 by (cases i) (simp_all add: outer_moved_def assemble_def condition1 condition2 condition3 condition4 condition5)

lemma common_image: "common_times(family(outer_moved e))=f ` common_times d"
 by (simp add: outer_moved_def assemble_def common_domain_image)

lemma admissible_image:
 "admissible_common(family(outer_moved e)) P \<longleftrightarrow>
   (\<exists>R. R\<subseteq>T \<and> admissible_common d R \<and> P=f ` R)"
 by (simp add: outer_moved_def assemble_def admissible_family_image)

lemma evaluation_tuple_transport:
 assumes a: "a\<in>law_indices d" and t: "t\<in>eval_times(old a)"
 shows "Core_Law_Datum_Assembly.evaluation_tuple (outer_moved e) a (f t)=
   tuple_change f (Core_Law_Datum_Assembly.evaluation_tuple (assemble e d) a t)"
 using evaluation_tuple[OF a t]
 by (simp add: outer_moved_def assemble_def Core_Law_Datum_Assembly.evaluation_tuple_def)

lemma law_operative_preserved:
 "law_operative dyn joint Core_Native_Law_Family.condition (outer_moved e) \<longleftrightarrow>
   law_operative dyn joint Core_Native_Law_Family.condition (assemble e d)"
proof -
 have all_iff: "(\<forall>i. Core_Native_Law_Family.condition (family(outer_moved e)) i) \<longleftrightarrow>
   (\<forall>i. Core_Native_Law_Family.condition d i)"
  using condition_preserved[of e] by blast
 show ?thesis using all_iff
  by (simp add: law_operative_def Core_Law_Readiness.all_conditions_def specification_preserved assemble_def)
qed
end

lemma generated_common_representability:
 assumes compatible: "\<forall>t\<in>time_carrier(family d). value t\<in>rho ` D"
 and operative: "law_operative dyn joint Core_Native_Law_Family.condition d"
 shows "common_times(family d)\<noteq>{} \<and>
  (\<forall>t\<in>common_times(family d). value t\<in>rho ` D \<and>
   (\<forall>a\<in>law_indices(family d). t\<in>eval_times(components(family d)a) \<and>
    Core_Law_Datum_Assembly.evaluation_tuple d a t\<in>law_relation(components(family d)a)))"
proof -
 have k5: "K5(family d)" using operative
  unfolding law_operative_def Core_Law_Readiness.all_conditions_def
  by (metis Core_Native_Law_Family.condition.simps(5))
 note hc = common_valid_contract[OF k5]
 have sub: "common_times(family d)\<subseteq>time_carrier(family d)"
  unfolding common_times_def by auto
 show ?thesis using hc compatible sub by blast
qed

ML \<open>
val roots = @{thms law_transport.specification_preserved law_transport.condition_preserved
 law_transport.common_image law_transport.admissible_image law_transport.evaluation_tuple_transport
 law_transport.law_operative_preserved generated_common_representability};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = if null (Thm_Deps.all_oracles @{thms law_transport.target_family_typed})
 then () else error "Unexpected oracle dependency";
val _ = writeln("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
