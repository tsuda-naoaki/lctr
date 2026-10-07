theory Core_Continuum_Datum
 imports "HOL-Analysis.Abstract_Topology"
 "LCTR_Core_Continuum_Failure.Core_Continuum_Failure"
begin

record ('x,'y) approximation_map =
 domain_topology :: "'x topology"
 codomain_topology :: "'y topology"
 map_interval :: "'x set"
 map_samples :: "'x set"
 sample_value :: "'x\<Rightarrow>'y"
 map_candidate :: "'x\<Rightarrow>'y"
 map_deviation :: "'y\<Rightarrow>'y\<Rightarrow>ereal"
 fit_tolerance :: ereal
 before_order :: "'x\<Rightarrow>'x\<Rightarrow>bool"
 after_order :: "'y\<Rightarrow>'y\<Rightarrow>bool"

definition map_valid where
 "map_valid m \<longleftrightarrow> map_interval m\<subseteq>topspace(domain_topology m) \<and>
 finite(map_samples m) \<and> map_samples m\<subseteq>map_interval m \<and>
 (\<forall>x\<in>map_interval m. map_candidate m x\<in>topspace(codomain_topology m)) \<and>
 (\<forall>x\<in>map_samples m. sample_value m x\<in>topspace(codomain_topology m)) \<and>
 (\<forall>a\<in>topspace(codomain_topology m). \<forall>b\<in>topspace(codomain_topology m). 0\<le>map_deviation m a b) \<and>
 0\<le>fit_tolerance m"
definition strict_on where
 "strict_on A r \<longleftrightarrow> (\<forall>x\<in>A. \<not>r x x) \<and>
 (\<forall>x\<in>A. \<forall>y\<in>A. \<forall>z\<in>A. r x y \<longrightarrow> r y z \<longrightarrow> r x z)"
definition map_order_valid where
 "map_order_valid m \<longleftrightarrow> strict_on(topspace(domain_topology m))(before_order m) \<and>
 strict_on(topspace(codomain_topology m))(after_order m)"
definition continuous_component where
 "continuous_component m=continuous_map (subtopology(domain_topology m)(map_interval m))
 (codomain_topology m)(map_candidate m)"
definition sample_fit where
 "sample_fit m=(\<forall>x\<in>map_samples m. map_deviation m (map_candidate m x)(sample_value m x)\<le>fit_tolerance m)"
definition extension where
 "extension maps=(\<forall>t<5. continuous_component(maps t) \<and> sample_fit(maps t))"
definition order_condition where
 "order_condition maps=(\<forall>t<4. \<forall>x\<in>map_interval(maps t). \<forall>y\<in>map_interval(maps t).
 before_order(maps t)x y \<longrightarrow> after_order(maps t)(map_candidate(maps t)x)(map_candidate(maps t)y))"
lemma extension_failure_witness:
 "\<not>extension maps \<longleftrightarrow> (\<exists>t<5. \<not>continuous_component(maps t) \<or>
 (\<exists>x\<in>map_samples(maps t). fit_tolerance(maps t)<
 map_deviation(maps t)(map_candidate(maps t)x)(sample_value(maps t)x)))"
 by (auto simp: extension_def sample_fit_def not_le)
lemma order_failure_witness:
 "\<not>order_condition maps \<longleftrightarrow> (\<exists>t<4. \<exists>x\<in>map_interval(maps t).
 \<exists>y\<in>map_interval(maps t). before_order(maps t)x y \<and>
 \<not>after_order(maps t)(map_candidate(maps t)x)(map_candidate(maps t)y))"
 by (auto simp: order_condition_def)

record ('x,'y) relation_datum =
 relation_arity :: nat
 relation_domain :: "nat\<Rightarrow>'x set"
 relation_codomain :: "nat\<Rightarrow>'y set"
 source_relation :: "(nat\<Rightarrow>'x) set"
 candidate_relation :: "(nat\<Rightarrow>'y) set"
 relation_mapping :: "nat\<Rightarrow>'x\<Rightarrow>'y"
definition source_tuples where
 "source_tuples r=PiE {..<relation_arity r} (relation_domain r)"
definition target_tuples where
 "target_tuples r=PiE {..<relation_arity r} (relation_codomain r)"
definition tuple_map where
 "tuple_map r x=restrict(\<lambda>k. relation_mapping r k (x k)){..<relation_arity r}"
definition relation_valid where
 "relation_valid r \<longleftrightarrow> 0<relation_arity r \<and>
 source_relation r\<subseteq>source_tuples r \<and> candidate_relation r\<subseteq>target_tuples r \<and>
 (\<forall>k<relation_arity r. \<forall>x\<in>relation_domain r k.
 relation_mapping r k x\<in>relation_codomain r k)"
definition relation_condition where
 "relation_condition rels=(\<forall>t<5. \<forall>x\<in>source_tuples(rels t).
 (x\<in>source_relation(rels t))=(tuple_map(rels t)x\<in>candidate_relation(rels t)))"
lemma relation_failure_witness:
 "\<not>relation_condition rels \<longleftrightarrow> (\<exists>t<5. \<exists>x\<in>source_tuples(rels t).
 (x\<in>source_relation(rels t) \<and> tuple_map(rels t)x\<notin>candidate_relation(rels t)) \<or>
 (x\<notin>source_relation(rels t) \<and> tuple_map(rels t)x\<in>candidate_relation(rels t)))"
 unfolding relation_condition_def by blast

definition nnSup :: "ereal set\<Rightarrow>ereal" where "nnSup A=Sup(insert 0 A)"
lemma nnSup_nonnegative: "0\<le>nnSup A" unfolding nnSup_def by (rule Sup_upper) simp
lemma nnSup_bound: "0\<le>eps \<Longrightarrow> (nnSup A\<le>eps \<longleftrightarrow> (\<forall>a\<in>A. a\<le>eps))"
 unfolding nnSup_def by (simp add: Sup_le_iff)
definition diameter :: "('y\<Rightarrow>'y\<Rightarrow>ereal)\<Rightarrow>'y set\<Rightarrow>ereal" where
 "diameter dev A=nnSup {r. \<exists>x\<in>A. \<exists>y\<in>A. r=dev x y}"
lemma diameter_empty: "diameter dev {}=0"
 by (simp add: diameter_def nnSup_def)
lemma diameter_bound:
 "0\<le>eps \<Longrightarrow> (diameter dev A\<le>eps \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>A. dev x y\<le>eps))"
 by (auto simp: diameter_def nnSup_bound)
lemma diameter_excess:
 "0\<le>eps \<Longrightarrow> (eps<diameter dev A \<longleftrightarrow> (\<exists>x\<in>A. \<exists>y\<in>A. eps<dev x y))"
 using diameter_bound by (meson not_le)
lemma diameter_source:
 assumes dn: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> 0\<le>dev x y"
 shows "diameter dev A=(if A={} then 0 else Sup {r. \<exists>x\<in>A. \<exists>y\<in>A. r=dev x y})"
proof (cases "A={}")
 case True then show ?thesis by (simp add: diameter_empty)
next
 case False
 then obtain x where x: "x\<in>A" by blast
 let ?D="{r. \<exists>x\<in>A. \<exists>y\<in>A. r=dev x y}"
 have mem: "dev x x\<in>?D" using x by blast
 have lower: "0\<le>Sup ?D" using dn[OF x x] Sup_upper[OF mem] by order
 show ?thesis using False lower by (simp add: diameter_def nnSup_def sup_absorb2)
qed

definition cell_image where
 "cell_image maps cells t x=image(map_candidate(maps(Suc t)))(cells t x)"
definition cell_width where
 "cell_width maps indices cells=nnSup(image(\<lambda>t. nnSup(image
 (\<lambda>x. diameter(map_deviation(maps(Suc t)))(cell_image maps cells t x))
 (indices t))){..<2})"
lemma cell_width_nonnegative: "0\<le>cell_width maps indices cells"
 unfolding cell_width_def by (rule nnSup_nonnegative)
lemma cell_width_bound:
 assumes en: "0\<le>eps"
 shows "cell_width maps indices cells\<le>eps \<longleftrightarrow>
 (\<forall>t<2. \<forall>x\<in>indices t. \<forall>a\<in>cell_image maps cells t x.
 \<forall>b\<in>cell_image maps cells t x. map_deviation(maps(Suc t))a b\<le>eps)"
 by (auto simp: cell_width_def nnSup_bound[OF en] diameter_bound[OF en])
lemma cell_width_excess:
 assumes en: "0\<le>eps"
 shows "eps<cell_width maps indices cells \<longleftrightarrow>
 (\<exists>t<2. \<exists>x\<in>indices t. \<exists>a\<in>cell_image maps cells t x.
 \<exists>b\<in>cell_image maps cells t x. eps<map_deviation(maps(Suc t))a b)"
 using cell_width_bound[OF en, of maps indices cells] by (meson not_le)
lemma width_equals_source_supremum:
 "cell_width maps indices cells=Sup(insert 0 {r. \<exists>t<2. \<exists>x\<in>indices t.
 r=diameter(map_deviation(maps(Suc t)))(cell_image maps cells t x)})"
proof -
 let ?A="{r. \<exists>t<2. \<exists>x\<in>indices t.
 r=diameter(map_deviation(maps(Suc t)))(cell_image maps cells t x)}"
 have n: "0\<le>nnSup ?A" by (rule nnSup_nonnegative)
 have b: "\<And>t x. t<2 \<Longrightarrow> x\<in>indices t \<Longrightarrow>
 diameter(map_deviation(maps(Suc t)))(cell_image maps cells t x)\<le>nnSup ?A"
  unfolding nnSup_def by (rule Sup_upper) blast
 have le: "cell_width maps indices cells\<le>nnSup ?A"
  unfolding cell_width_def by (simp add: nnSup_bound[OF n] b)
 have n2: "0\<le>cell_width maps indices cells" by (rule cell_width_nonnegative)
 have b2: "\<forall>t<2. \<forall>x\<in>indices t.
 diameter(map_deviation(maps(Suc t)))(cell_image maps cells t x)\<le>cell_width maps indices cells"
 proof (intro allI impI ballI)
  fix t x assume t: "t<2" and x: "x\<in>indices t"
  let ?F="\<lambda>x. diameter(map_deviation(maps(Suc t)))(cell_image maps cells t x)"
  have one: "?F x\<le>nnSup(image ?F (indices t))"
   unfolding nnSup_def by (rule Sup_upper) (use x in auto)
  have two: "nnSup(image ?F (indices t))\<le>cell_width maps indices cells"
   unfolding cell_width_def nnSup_def by (rule Sup_upper) (use t in auto)
  show "?F x\<le>cell_width maps indices cells" using one two by order
 qed
 have ge: "nnSup ?A\<le>cell_width maps indices cells" using b2 by (auto simp: nnSup_bound[OF n2])
 show ?thesis using le ge unfolding nnSup_def by order
qed

record ('obj,'code,'val) record_datum =
 record_domains :: "nat\<Rightarrow>'obj set"
 code_relation :: "nat\<Rightarrow>'obj\<Rightarrow>'code\<Rightarrow>bool"
 record_mapping :: "'code\<Rightarrow>'val"
definition record_image where
 "record_image r t x=image(record_mapping r){z. code_relation r t x z}"
definition collision where
 "collision r=(\<exists>t<3. \<exists>x\<in>record_domains r t. \<exists>y\<in>record_domains r t.
 x\<noteq>y \<and> record_image r t x\<inter>record_image r t y\<noteq>{})"
definition separation_defect :: "('obj,'code,'val) record_datum\<Rightarrow>ereal" where
 "separation_defect r=(if collision r then 1 else 0)"
lemma collision_witness:
 "collision r \<longleftrightarrow> (\<exists>t<3. \<exists>x\<in>record_domains r t. \<exists>y\<in>record_domains r t.
 x\<noteq>y \<and> (\<exists>a b. code_relation r t x a \<and> code_relation r t y b \<and>
 record_mapping r a=record_mapping r b))"
 unfolding collision_def record_image_def by blast
lemma separation_defect_excess:
 "0\<le>eps \<Longrightarrow> (eps<separation_defect r \<longleftrightarrow> collision r \<and> eps<1)"
 by (auto simp: separation_defect_def)

record 's scalar_datum =
 scalar_carrier :: "'s set"
 scalar_order :: "'s\<Rightarrow>'s\<Rightarrow>bool"
 scalar_value :: 's
 scalar_evaluation :: "'s\<Rightarrow>ereal"
definition scalar_valid where
 "scalar_valid q \<longleftrightarrow> scalar_value q\<in>scalar_carrier q \<and>
 (\<forall>x\<in>scalar_carrier q. scalar_order q x x) \<and>
 (\<forall>x\<in>scalar_carrier q. \<forall>y\<in>scalar_carrier q.
 scalar_order q x y \<longrightarrow> scalar_order q y x \<longrightarrow> x=y) \<and>
 (\<forall>x\<in>scalar_carrier q. \<forall>y\<in>scalar_carrier q. \<forall>z\<in>scalar_carrier q.
 scalar_order q x y \<longrightarrow> scalar_order q y z \<longrightarrow> scalar_order q x z) \<and>
 (\<forall>x\<in>scalar_carrier q. 0\<le>scalar_evaluation q x) \<and>
 (\<forall>x\<in>scalar_carrier q. \<forall>y\<in>scalar_carrier q.
 scalar_order q x y \<longrightarrow> scalar_evaluation q x\<le>scalar_evaluation q y)"
definition scalar where "scalar q=scalar_evaluation q (scalar_value q)"

record ('x,'y,'idx,'obj,'code,'val,'s) continuum_packet =
 packet_maps :: "nat\<Rightarrow>('x,'y) approximation_map"
 packet_relations :: "nat\<Rightarrow>('x,'y) relation_datum"
 packet_indices :: "nat\<Rightarrow>'idx set"
 packet_cells :: "nat\<Rightarrow>'idx\<Rightarrow>'x set"
 packet_records :: "('obj,'code,'val) record_datum"
 packet_scalars :: "nat\<Rightarrow>'s scalar_datum"
 packet_tolerance :: "nat\<Rightarrow>ereal"
definition packet_valid where
 "packet_valid p \<longleftrightarrow> (\<forall>t<5. map_valid(packet_maps p t) \<and> relation_valid(packet_relations p t)) \<and>
 (\<forall>t<4. map_order_valid(packet_maps p t) \<and> scalar_valid(packet_scalars p t)) \<and>
 (\<forall>t<2. \<forall>x\<in>packet_indices p t. packet_cells p t x\<subseteq>map_interval(packet_maps p(Suc t))) \<and>
 (\<forall>i<6. 0\<le>packet_tolerance p i)"
definition first_defect where
 "first_defect p i=[scalar(packet_scalars p 0),scalar(packet_scalars p 1),
 cell_width(packet_maps p)(packet_indices p)(packet_cells p),separation_defect(packet_records p),
 scalar(packet_scalars p 2),scalar(packet_scalars p 3)]!i"
definition actual where
 "actual p i=(if i<6 then first_defect p i\<le>packet_tolerance p i
 else if i=6 then extension(packet_maps p)
 else if i=7 then order_condition(packet_maps p) else relation_condition(packet_relations p))"
definition condition where "condition p i=actual p i"
lemma condition_true: "condition p i \<longleftrightarrow> actual p i" by (simp add: condition_def)
lemma three_record_defects:
 "first_defect p 1=scalar(packet_scalars p 1) \<and>
 first_defect p 2=cell_width(packet_maps p)(packet_indices p)(packet_cells p) \<and>
 first_defect p 3=separation_defect(packet_records p)"
 by (simp add: first_defect_def)

locale packet_evaluation =
 fixes p :: "('x,'y,'idx,'obj,'code,'val,'s) continuum_packet"
 and f e c :: "token\<Rightarrow>bool" and s :: "token\<Rightarrow>eval_state"
 assumes valid: "packet_valid p"
 and rec: "s=eval_update Core_Token_Graph.edges f e c s"
 and matching: "\<And>i. i<9 \<Longrightarrow> c(approx_token i)=condition p i"
begin
lemma actual_failure:
 "i<9 \<Longrightarrow> approx_ready f e s i \<Longrightarrow> (fa s i \<longleftrightarrow> \<not>actual p i)"
 using ready_failure_iff[OF rec, where i=i] matching[of i] by (simp add: condition_def)
lemma extension_failure:
 "approx_ready f e s 6 \<Longrightarrow> (fa s 6 \<longleftrightarrow> \<not>extension(packet_maps p))"
 using actual_failure[where i=6] by (simp add: actual_def)
lemma order_failure:
 "approx_ready f e s 7 \<Longrightarrow> (fa s 7 \<longleftrightarrow> \<not>order_condition(packet_maps p))"
 using actual_failure[where i=7] by (simp add: actual_def)
lemma relation_failure:
 "approx_ready f e s 8 \<Longrightarrow> (fa s 8 \<longleftrightarrow> \<not>relation_condition(packet_relations p))"
 using actual_failure[where i=8] by (simp add: actual_def)
lemma width_failure:
 "approx_ready f e s 2 \<Longrightarrow>
 (fa s 2 \<longleftrightarrow> packet_tolerance p 2<cell_width(packet_maps p)(packet_indices p)(packet_cells p))"
 using actual_failure[where i=2] by (simp add: actual_def first_defect_def not_le)
lemma separation_failure:
 assumes r: "approx_ready f e s 3"
 shows "fa s 3 \<longleftrightarrow> collision(packet_records p) \<and> packet_tolerance p 3<1"
proof -
 have n: "0\<le>packet_tolerance p 3" using valid by (simp add: packet_valid_def)
 have a: "fa s 3 \<longleftrightarrow> packet_tolerance p 3<separation_defect(packet_records p)"
  using actual_failure[where i=3] r by (simp add: actual_def first_defect_def not_le)
 show ?thesis using a separation_defect_excess[OF n] by blast
qed
lemma zero_separation_tolerance:
 "approx_ready f e s 3 \<Longrightarrow> packet_tolerance p 3=0 \<Longrightarrow>
 (fa s 3 \<longleftrightarrow> collision(packet_records p))"
 using separation_failure by auto
lemma unit_separation_tolerance:
 "approx_ready f e s 3 \<Longrightarrow> 1\<le>packet_tolerance p 3 \<Longrightarrow> \<not>fa s 3"
 using separation_failure by auto
end

ML \<open>
val roots = @{thms extension_failure_witness order_failure_witness relation_failure_witness
 diameter_empty diameter_bound diameter_excess cell_width_bound cell_width_excess
 width_equals_source_supremum collision_witness separation_defect_excess condition_true
 three_record_defects packet_evaluation.actual_failure packet_evaluation.extension_failure
 packet_evaluation.order_failure packet_evaluation.relation_failure packet_evaluation.width_failure
 packet_evaluation.separation_failure packet_evaluation.zero_separation_tolerance
 packet_evaluation.unit_separation_tolerance};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
