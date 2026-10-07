theory Core_Continuum_Input
 imports LCTR_Core_Record_Cells.Core_Record_Cells
 LCTR_Core_Representation_Stages.Core_Representation_Stages
 "HOL.Topological_Spaces"
begin

record ('kc,'kd,'s,'d,'o) granularity =
 count_step :: 'kc
 stability :: 's
 cell_width :: 'kd
 discrimination :: 'd
 coupling :: 'o

definition granularity_valid where
 "granularity_valid g \<longleftrightarrow> (0\<le>count_step g \<and> 0\<le>cell_width g)"
definition granularity_tuple where
 "granularity_tuple g=(count_step g,stability g,cell_width g,discrimination g,coupling g)"

theorem granularity_components:
 fixes g :: "('kc::linordered_field,'kd::linordered_field,'s,'d,'o) granularity"
 assumes "granularity_valid g"
 shows "0\<le>count_step g \<and> 0\<le>cell_width g \<and>
  (\<exists>sv::'s. True) \<and> (\<exists>dv::'d. True) \<and> (\<exists>cv::'o. True)"
 using assms unfolding granularity_valid_def by simp
theorem granularity_tuple_components:
 "fst(granularity_tuple g)=count_step g \<and>
  fst(snd(granularity_tuple g))=stability g \<and>
  fst(snd(snd(granularity_tuple g)))=cell_width g \<and>
  fst(snd(snd(snd(granularity_tuple g))))=discrimination g \<and>
  snd(snd(snd(snd(granularity_tuple g))))=coupling g"
 by (simp add: granularity_tuple_def)

definition step_window where
 "step_window r x \<longleftrightarrow> admissible r x \<and> count_end x=count_start x+1"
theorem step_count_one:
 "step_window r x \<Longrightarrow> (count_difference x::'k::linordered_field)=1"
 by (simp add: step_window_def count_difference_def)
context affine_frequency
begin
theorem step_width_positive:
 assumes strict: "\<And>a b. r a b \<longleftrightarrow> rho a<rho b"
 and step: "step_window r x"
 shows "0<coordinate_difference rho x"
 by (rule coordinate_difference_positive[OF strict]) (use step in \<open>simp add: step_window_def\<close>)
definition count_evaluation_source where
 "count_evaluation_source r rho g=
  (({x. step_window r x}, coordinate_difference rho),count_step g)"
theorem count_evaluation_source_exact:
 "fst(fst(count_evaluation_source r rho g))={x. step_window r x} \<and>
  snd(fst(count_evaluation_source r rho g))=coordinate_difference rho \<and>
  snd(count_evaluation_source r rho g)=count_step g"
 by (simp add: count_evaluation_source_def)
end

datatype eval_index = CountStep | Stability | CellWidth | Discrimination | Coupling | OrderStability
theorem evaluation_indices_exhaustive:
 "k=CountStep \<or> k=Stability \<or> k=CellWidth \<or> k=Discrimination \<or> k=Coupling \<or> k=OrderStability"
 by (cases k) simp_all

record 'a evaluation =
 eval_carrier :: "'a set"
 eval_order :: "'a\<Rightarrow>'a\<Rightarrow>bool"
 eval_least :: 'a
 eval_value :: 'a
 eval_tolerance :: 'a
definition evaluation_valid where
 "evaluation_valid e \<longleftrightarrow> part_on(eval_carrier e)(eval_order e) \<and>
  eval_least e\<in>eval_carrier e \<and> eval_value e\<in>eval_carrier e \<and>
  eval_tolerance e\<in>eval_carrier e \<and> (\<forall>x\<in>eval_carrier e. eval_order e (eval_least e) x)"
definition evaluation_pass where
 "evaluation_pass e \<longleftrightarrow> eval_order e (eval_value e) (eval_tolerance e)"
theorem evaluation_component_contract:
 "evaluation_valid e \<Longrightarrow> eval_carrier e\<noteq>{} \<and>
  (\<forall>x\<in>eval_carrier e. eval_order e (eval_least e) x) \<and>
  (evaluation_pass e \<longleftrightarrow> eval_order e (eval_value e) (eval_tolerance e))"
 unfolding evaluation_valid_def evaluation_pass_def by blast
definition evaluation_from_source where
 "evaluation_from_source src A r z evaluate tol=
  \<lparr>eval_carrier=A,eval_order=r,eval_least=z,eval_value=evaluate src,eval_tolerance=tol\<rparr>"
theorem evaluation_uses_source:
 "eval_value(evaluation_from_source src A r z evaluate tol)=evaluate src"
 by (simp add: evaluation_from_source_def)
definition evaluation_family where
 "evaluation_family count remaining k=(if k=CountStep then count else remaining k)"
theorem evaluation_family_count:
 "evaluation_family count remaining CountStep=count"
 by (simp add: evaluation_family_def)
theorem evaluation_family_other:
 "k\<noteq>CountStep \<Longrightarrow> evaluation_family count remaining k=remaining k"
 by (simp add: evaluation_family_def)

datatype ('a,'b,'c,'d,'e,'f) eval_sum =
 ECount 'a | EStability 'b | EWidth 'c | EDiscrimination 'd | ECoupling 'e | EOrder 'f
definition lift_evaluation where
 "lift_evaluation f e=\<lparr>eval_carrier=image f (eval_carrier e),
  eval_order=(\<lambda>x y. eval_order e (inv f x) (inv f y)),
  eval_least=f(eval_least e),eval_value=f(eval_value e),eval_tolerance=f(eval_tolerance e)\<rparr>"
lemma lift_evaluation_preserves_contract:
 assumes inject: "inj f" and valid: "evaluation_valid e"
 shows "evaluation_valid(lift_evaluation f e) \<and>
  (evaluation_pass(lift_evaluation f e)\<longleftrightarrow>evaluation_pass e)"
proof -
 let ?A = "eval_carrier e"
 let ?r = "eval_order e"
 have undo: "\<And>x. inv f (f x)=x" by (rule inv_f_f[OF inject])
 have old: "part_on ?A ?r" using valid unfolding evaluation_valid_def by blast
 have maps: "image (inv f) (image f ?A) \<subseteq> ?A" by (auto simp: undo)
 have pre: "pre_on (image f ?A) (pullback (inv f) ?r)"
  by (rule preorder_pullback[OF maps]) (use old in \<open>simp add: part_on_def\<close>)
 have anti: "\<And>x y. x\<in>image f ?A \<Longrightarrow> y\<in>image f ?A \<Longrightarrow>
  ?r (inv f x) (inv f y) \<Longrightarrow> ?r (inv f y) (inv f x) \<Longrightarrow> x=y"
 proof -
  fix x y assume x: "x\<in>image f ?A" and y: "y\<in>image f ?A"
  and xy: "?r (inv f x) (inv f y)" and yx: "?r (inv f y) (inv f x)"
  obtain a where a: "a\<in>?A" and xa: "x=f a" using x by blast
  obtain b where b: "b\<in>?A" and yb: "y=f b" using y by blast
  have ab: "?r a b" using xy by (simp add: xa yb undo)
  have ba: "?r b a" using yx by (simp add: xa yb undo)
  have "a=b" using old a b ab ba unfolding part_on_def by blast
  then show "x=y" by (simp add: xa yb)
 qed
 have part: "part_on (image f ?A) (\<lambda>x y. ?r (inv f x) (inv f y))"
  using pre anti unfolding part_on_def pullback_def by blast
 have least: "eval_least e\<in>?A" and val: "eval_value e\<in>?A"
 and tol: "eval_tolerance e\<in>?A" and least_bound: "\<forall>x\<in>?A. ?r (eval_least e) x"
  using valid unfolding evaluation_valid_def by auto
 have new_bound: "\<forall>x\<in>image f ?A. ?r (inv f (f(eval_least e))) (inv f x)"
  using least_bound by (auto simp: undo)
 have valid_new: "evaluation_valid(lift_evaluation f e)"
  using part least val tol new_bound
  by (auto simp only: evaluation_valid_def lift_evaluation_def evaluation.select_convs)
 have pass: "evaluation_pass(lift_evaluation f e)\<longleftrightarrow>evaluation_pass e"
  by (simp add: evaluation_pass_def lift_evaluation_def undo)
 show ?thesis using valid_new pass by blast
qed
lemma six_component_embeddings:
 "inj ECount \<and> inj EStability \<and> inj EWidth \<and>
  inj EDiscrimination \<and> inj ECoupling \<and> inj EOrder"
 by (auto intro!: injI)

context representation_base
begin
theorem stage_to_coordinate_factorization:
 assumes h: third
 and emb: "\<And>a b. a\<in>QuSet C clt \<Longrightarrow> b\<in>QuSet C clt \<Longrightarrow>
  (rho a<rho b \<longleftrightarrow> qlt C clt a b)"
 shows "exact_structure.represented D f tr adm r rho x=rho(qproj C clt x)"
proof -
 have first by (use h in \<open>simp add: third_def second_def\<close>)
 then interpret E: exact_structure D f tr adm r by (rule exact_from_first)
 show ?thesis by (simp add: E.represented_def)
qed
end

context record_representation
begin
definition coordinate_candidate where
 "coordinate_candidate=(generate_topology {S. \<exists>a::'p. S={x. a<x} \<or> S={x. x<a}},represented emb)"
theorem coordinate_candidate_topology:
 "fst coordinate_candidate=generate_topology {S. \<exists>a::'p. S={x. a<x} \<or> S={x. x<a}}"
 by (simp add: coordinate_candidate_def)
theorem coordinate_candidate_map:
 "snd coordinate_candidate=emb \<circ> qproj canonical_carrier canonical_lt"
 by (auto simp: coordinate_candidate_def represented_def)
end

locale continuum_input =
 C: record_representation DC fC trC admC rC embC +
 D: record_affine DD fD trD admD rD embD actD diffD +
 AC: affine_frequency actC diffC
 for DC :: "'u\<Rightarrow>'c set" and fC :: "'u\<Rightarrow>'c\<Rightarrow>'vc"
 and trC :: "'u\<Rightarrow>'u\<Rightarrow>'vc\<Rightarrow>'vc\<Rightarrow>bool"
 and admC :: "'u\<Rightarrow>'u\<Rightarrow>bool" and rC
 and embC :: "(('u\<times>'vc) set) set\<Rightarrow>'pc::linorder"
 and DD :: "'u\<Rightarrow>'d set" and fD :: "'u\<Rightarrow>'d\<Rightarrow>'vd"
 and trD :: "'u\<Rightarrow>'u\<Rightarrow>'vd\<Rightarrow>'vd\<Rightarrow>bool"
 and admD :: "'u\<Rightarrow>'u\<Rightarrow>bool" and rD
 and embD :: "(('u\<times>'vd) set) set\<Rightarrow>'pd::linorder"
 and actD :: "'pd\<Rightarrow>'kd::linordered_field\<Rightarrow>'pd" and diffD :: "'pd\<Rightarrow>'pd\<Rightarrow>'kd"
 and actC :: "'pc\<Rightarrow>'kc::linordered_field\<Rightarrow>'pc" and diffC :: "'pc\<Rightarrow>'pc\<Rightarrow>'kc"
begin
definition generated_input where
 "generated_input W rel (g::('kc,'kd,'s,'disc,'coupl)granularity) (e::eval_index\<Rightarrow>'v evaluation)=
  (((actC,diffC),(actD,diffD)),g,e,
   (D.width_admissible W (cell_width g),D.R.separates DC fC trC admC rC W rel),
   (C.coordinate_candidate,D.R.coordinate_candidate))"
theorem generated_input_retains_inputs:
 "fst(generated_input W rel g e)=((actC,diffC),(actD,diffD)) \<and>
  fst(snd(generated_input W rel g e))=g \<and>
  fst(snd(snd(generated_input W rel g e)))=e"
 by (simp add: generated_input_def)
theorem generated_record_truths_exact:
 "(fst(fst(snd(snd(snd(generated_input W rel g e)))))=True \<longleftrightarrow>
   D.width_admissible W (cell_width g)) \<and>
  (snd(fst(snd(snd(snd(generated_input W rel g e)))))=True \<longleftrightarrow>
   D.R.separates DC fC trC admC rC W rel)"
 by (simp add: generated_input_def)
theorem generated_coordinate_candidates_exact:
 "snd(snd(snd(snd(generated_input W rel g e))))=(C.coordinate_candidate,D.R.coordinate_candidate)"
 by (simp add: generated_input_def)
end

definition closed_under where
 "closed_under dep S \<longleftrightarrow> (\<forall>rule\<in>dep. fst rule\<subseteq>S \<longrightarrow> snd rule\<in>S)"
definition generation_closure where
 "generation_closure dep inputs=\<Inter>{S. inputs\<subseteq>S \<and> closed_under dep S}"
theorem closure_contains_inputs: "inputs\<subseteq>generation_closure dep inputs"
 unfolding generation_closure_def by blast
theorem closure_is_closed: "closed_under dep (generation_closure dep inputs)"
 unfolding generation_closure_def closed_under_def by blast
theorem closure_is_least:
 "inputs\<subseteq>S \<Longrightarrow> closed_under dep S \<Longrightarrow> generation_closure dep inputs\<subseteq>S"
 unfolding generation_closure_def by blast
theorem tuple_generation_export: "tuple\<in>generation_closure {(inputs,tuple)} inputs"
 using closure_is_closed[of "{(inputs,tuple)}" inputs]
 closure_contains_inputs[of inputs "{(inputs,tuple)}"]
 unfolding closed_under_def by auto
theorem no_rule_adds_nothing: "generation_closure {} inputs=inputs"
 using closure_is_least[of inputs inputs "{}"] closure_contains_inputs[of inputs "{}"]
 by (auto simp: closed_under_def)

datatype ('i,'v) tuple_expr =
 Component 'i "'v set" 'v | Tuple "'i set" "'i\<Rightarrow>'v set" "'i\<Rightarrow>'v"
definition tuple_inputs where
 "tuple_inputs I V v=image(\<lambda>i. Component i (V i) (v i)) I"
theorem tuple_inputs_exact:
 "x\<in>tuple_inputs I V v \<longleftrightarrow> (\<exists>i\<in>I. Component i (V i) (v i)=x)"
 by (auto simp: tuple_inputs_def)
lemma tuple_inputs_typed:
 assumes typed: "\<And>i. i\<in>I \<Longrightarrow> v i\<in>V i"
 and member: "Component i A x\<in>tuple_inputs I V v"
 shows "i\<in>I \<and> A=V i \<and> x=v i \<and> x\<in>A"
 using assms by (auto simp: tuple_inputs_def)
theorem typed_tuple_generation_export:
 assumes typed: "\<And>i. i\<in>I \<Longrightarrow> v i\<in>V i"
 shows "Tuple I V v\<in>generation_closure {(tuple_inputs I V v,Tuple I V v)} (tuple_inputs I V v)"
 by (rule tuple_generation_export)

ML \<open>
val roots = @{thms granularity_components granularity_tuple_components step_count_one
 affine_frequency.step_width_positive affine_frequency.count_evaluation_source_exact
 evaluation_indices_exhaustive evaluation_component_contract evaluation_uses_source
 evaluation_family_count evaluation_family_other representation_base.stage_to_coordinate_factorization
 record_representation.coordinate_candidate_topology record_representation.coordinate_candidate_map
 continuum_input.generated_input_retains_inputs continuum_input.generated_record_truths_exact
 continuum_input.generated_coordinate_candidates_exact closure_contains_inputs closure_is_closed
 closure_is_least tuple_generation_export no_rule_adds_nothing tuple_inputs_exact typed_tuple_generation_export};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
