theory Core_Comparison_Stage
 imports "LCTR_Core_Paired_Comparison.Core_Paired_Comparison"
         "LCTR_Core_Local_Loop_Realization.Core_Local_Loop_Realization"
begin

record ('u,'vc,'vd) comparison_output =
 clock_loops :: "((('u,'vc) loop_spec\<times>('u\<times>'vc))\<times>('u\<times>'vc)) set"
 detector_loops :: "((('u,'vd) loop_spec\<times>('u\<times>'vd))\<times>('u\<times>'vd)) set"
 clock_projection :: "(('u\<times>'vc)\<times>('u\<times>'vc) set) set"
 detector_projection :: "(('u\<times>'vd)\<times>('u\<times>'vd) set) set"
 quotient_relation :: "(('u\<times>'vc) set\<times>('u\<times>'vd) set) set"

context native_comparison
begin
abbreviation loop_action where
 "loop_action s a b \<equiv> typed_actions.action (regions D f) {e. admitted adm e}
  initial terminal (cmp_act D f tr) (base s) (word s) (base s) a b"
definition loop_graph where
 "loop_graph (specs::('u,'v) loop_spec set) = {((s,a),b). s\<in>specs \<and> a\<in>specified s \<and> b=realize s a}"
definition valid_loop_graph where
 "valid_loop_graph (specs::('u,'v) loop_spec set) graph =
  ((\<forall>s\<in>specs. \<forall>a\<in>specified s. \<exists>b. ((s,a),b)\<in>graph) \<and>
   (\<forall>s a b. ((s,a),b)\<in>graph \<longrightarrow> s\<in>specs \<and> a\<in>specified s \<and> loop_action s a b))"

lemma loop_graph_valid:
 "(\<And>s. s\<in>specs \<Longrightarrow> realizable s) \<Longrightarrow> valid_loop_graph specs (loop_graph specs)"
 unfolding valid_loop_graph_def loop_graph_def using realization_correct by blast

lemma loop_graph_unique:
 assumes real: "\<And>s. s\<in>specs \<Longrightarrow> realizable s"
 and valid: "valid_loop_graph specs graph"
 shows "graph=loop_graph specs"
proof (rule set_eqI)
 fix p :: "(('u,'v) loop_spec\<times>('u\<times>'v))\<times>('u\<times>'v)"
 obtain s a b where p: "p=((s,a),b)" by (cases p; case_tac a) auto
 have right: "((s,a),b)\<in>loop_graph specs \<longleftrightarrow>
   s\<in>specs \<and> a\<in>specified s \<and> b=realize s a"
  by (simp add: loop_graph_def)
 have action: "\<And>b. s\<in>specs \<Longrightarrow> a\<in>specified s \<Longrightarrow>
   loop_action s a b \<longleftrightarrow> realize s a=b"
  using realization_graph[OF real] by blast
 have forward: "((s,a),b)\<in>graph \<Longrightarrow> ((s,a),b)\<in>loop_graph specs"
 proof -
  assume edge: "((s,a),b)\<in>graph"
  have facts: "s\<in>specs \<and> a\<in>specified s \<and> loop_action s a b"
   using valid edge unfolding valid_loop_graph_def by blast
  have eq: "realize s a=b" by (rule iffD1[OF action[OF facts[THEN conjunct1] facts[THEN conjunct2, THEN conjunct1]] facts[THEN conjunct2, THEN conjunct2]])
  show ?thesis using facts eq right by blast
 qed
 have backward: "((s,a),b)\<in>loop_graph specs \<Longrightarrow> ((s,a),b)\<in>graph"
 proof -
  assume member: "((s,a),b)\<in>loop_graph specs"
  have s: "s\<in>specs" and a: "a\<in>specified s" and eq: "b=realize s a"
   using member right by auto
  obtain c where edge: "((s,a),c)\<in>graph"
   using valid s a unfolding valid_loop_graph_def by blast
  have run: "loop_action s a c" using valid edge unfolding valid_loop_graph_def by blast
  have chosen: "realize s a=c" using action[OF s a] run by blast
  have "b=c" by (rule trans[OF eq chosen])
  then show ?thesis using edge by simp
 qed
 show "p\<in>graph \<longleftrightarrow> p\<in>loop_graph specs"
  unfolding p using forward backward by blast
qed

lemma loop_graph_requires_realizability:
 "valid_loop_graph specs graph \<Longrightarrow> s\<in>specs \<Longrightarrow> realizable s"
 unfolding valid_loop_graph_def realizable_def by blast
lemma loop_graph_identity:
 "realizable s \<Longrightarrow> id_on_specified s \<Longrightarrow>
  ((s,a),b)\<in>loop_graph specs \<Longrightarrow> b=a"
 using specified_identity_iff unfolding loop_graph_def by blast
end

context paired_comparison
begin
definition stage_L3 where
 "stage_L3 cs ds = ((\<forall>s\<in>cs. C.realizable s) \<and> (\<forall>s\<in>ds. D.realizable s))"
definition stage_L4 where
 "stage_L4 cs ds = ((\<forall>s\<in>cs. C.id_on_specified s) \<and> (\<forall>s\<in>ds. D.id_on_specified s))"
definition stage_L5 where
 "stage_L5 localRel sourceRel = (\<forall>p\<in>synchronized.
  (snd p\<in>localRel(fst p) \<longleftrightarrow>
  (recovery DC fC (fst p) (fst(snd p)),recovery DD fD (fst p) (snd(snd p)))\<in>sourceRel))"
definition residual_operative where
 "residual_operative cs ds localRel sourceRel =
  (stage_L3 cs ds \<and> stage_L4 cs ds \<and> stage_L5 localRel sourceRel \<and>
   saturated localRel \<and> C.irreducible_mixed_identity \<and> D.irreducible_mixed_identity \<and>
   C.pure_loop_identity \<and> D.pure_loop_identity)"
definition clock_projection_graph where
 "clock_projection_graph = {(p,Image ceq {p}) |p. p\<in>(\<Union>u. regions DC fC u)}"
definition detector_projection_graph where
 "detector_projection_graph = {(p,Image deq {p}) |p. p\<in>(\<Union>u. regions DD fD u)}"
definition contains_local where
 "contains_local localRel target = (\<forall>p\<in>synchronized. snd p\<in>localRel(fst p) \<longrightarrow> projection p\<in>target)"
definition valid_output where
 "valid_output cs ds localRel (out::('u,'vc,'vd) comparison_output) =
  (C.valid_loop_graph cs (clock_loops out) \<and>
   D.valid_loop_graph ds (detector_loops out) \<and>
   clock_projection out=clock_projection_graph \<and>
   detector_projection out=detector_projection_graph \<and>
   contains_local localRel (quotient_relation out) \<and>
   (\<forall>other. contains_local localRel other \<longrightarrow> quotient_relation out\<subseteq>other))"
definition generate where
 "generate cs ds localRel =
  \<lparr>clock_loops=C.loop_graph cs, detector_loops=D.loop_graph ds,
   clock_projection=clock_projection_graph, detector_projection=detector_projection_graph,
   quotient_relation=canonical_relation localRel\<rparr>"

lemma canonical_contains: "contains_local localRel (canonical_relation localRel)"
 unfolding contains_local_def canonical_relation_def pair_relation_def by blast
lemma canonical_least:
 "contains_local localRel target \<Longrightarrow> canonical_relation localRel\<subseteq>target"
 unfolding contains_local_def by (rule canonical_relation_least) blast

theorem generated_valid:
 assumes h: "stage_L3 cs ds"
 shows "valid_output cs ds localRel (generate cs ds localRel)"
proof -
 have c: "C.valid_loop_graph cs (C.loop_graph cs)"
  by (rule C.loop_graph_valid) (use h in \<open>auto simp: stage_L3_def\<close>)
 have d: "D.valid_loop_graph ds (D.loop_graph ds)"
  by (rule D.loop_graph_valid) (use h in \<open>auto simp: stage_L3_def\<close>)
 show ?thesis using c d canonical_contains canonical_least
  unfolding valid_output_def generate_def by auto
qed

theorem output_unique:
 assumes h: "stage_L3 cs ds" and valid: "valid_output cs ds localRel out"
 shows "out=generate cs ds localRel"
proof -
 have cl: "clock_loops out=C.loop_graph cs"
  by (rule C.loop_graph_unique) (use h valid in \<open>auto simp: stage_L3_def valid_output_def\<close>)
 have dl: "detector_loops out=D.loop_graph ds"
  by (rule D.loop_graph_unique) (use h valid in \<open>auto simp: stage_L3_def valid_output_def\<close>)
 have cp: "clock_projection out=clock_projection_graph"
 and dp: "detector_projection out=detector_projection_graph"
  using valid unfolding valid_output_def by auto
 have left: "quotient_relation out\<subseteq>canonical_relation localRel"
  using valid canonical_contains unfolding valid_output_def by blast
 have right: "canonical_relation localRel\<subseteq>quotient_relation out"
  using valid canonical_least unfolding valid_output_def by blast
 have rel: "quotient_relation out=canonical_relation localRel" by (rule antisym[OF left right])
 show ?thesis using cl dl cp dp rel by (cases out) (simp add: generate_def)
qed

theorem unique_generated_output:
 assumes h: "residual_operative cs ds localRel sourceRel"
 shows "\<exists>!out. valid_output cs ds localRel out"
proof -
 have l3: "stage_L3 cs ds" using h unfolding residual_operative_def by blast
 show ?thesis
 proof (rule ex1I[where a="generate cs ds localRel"])
  show "valid_output cs ds localRel (generate cs ds localRel)" by (rule generated_valid[OF l3])
 next
  fix out assume "valid_output cs ds localRel out"
  then show "out=generate cs ds localRel" by (rule output_unique[OF l3])
 qed
qed

theorem generated_local_injective:
 "residual_operative cs ds localRel sourceRel \<Longrightarrow>
  inj_on (\<lambda>p. Image ceq {p}) (regions DC fC u) \<and>
  inj_on (\<lambda>p. Image deq {p}) (regions DD fD u)"
 using C.gluing_iff_local_injectivity D.gluing_iff_local_injectivity
 unfolding residual_operative_def by blast
theorem generated_pair_injective:
 "residual_operative cs ds localRel sourceRel \<Longrightarrow>
  inj_on (\<lambda>a. projection(u,a)) ((image (fC u) (DC u))\<times>(image (fD u) (DD u)))"
 by (rule local_pair_projection_injective) (auto simp: residual_operative_def)
theorem generated_local_pullback:
 "residual_operative cs ds localRel sourceRel \<Longrightarrow> p\<in>synchronized \<Longrightarrow>
  (projection p\<in>quotient_relation(generate cs ds localRel) \<longleftrightarrow> snd p\<in>localRel(fst p))"
 using canonical_relation_pullback unfolding generate_def residual_operative_def by auto
theorem generated_source_pullback:
 "residual_operative cs ds localRel sourceRel \<Longrightarrow> p\<in>synchronized \<Longrightarrow>
  (projection p\<in>quotient_relation(generate cs ds localRel) \<longleftrightarrow>
   (recovery DC fC (fst p) (fst(snd p)),recovery DD fD (fst p) (snd(snd p)))\<in>sourceRel)"
 using generated_local_pullback unfolding residual_operative_def stage_L5_def by blast
theorem generated_loop_identity:
 assumes h: "residual_operative cs ds localRel sourceRel"
 shows "(\<forall>s a b. ((s,a),b)\<in>clock_loops(generate cs ds localRel) \<longrightarrow> b=a) \<and>
  (\<forall>s a b. ((s,a),b)\<in>detector_loops(generate cs ds localRel) \<longrightarrow> b=a)"
proof -
 have cr: "\<And>s. s\<in>cs \<Longrightarrow> C.realizable s"
 and dr: "\<And>s. s\<in>ds \<Longrightarrow> D.realizable s"
 and ci: "\<And>s. s\<in>cs \<Longrightarrow> C.id_on_specified s"
 and di: "\<And>s. s\<in>ds \<Longrightarrow> D.id_on_specified s"
  using h unfolding residual_operative_def stage_L3_def stage_L4_def by auto
 have c: "\<And>s a b. ((s,a),b)\<in>C.loop_graph cs \<Longrightarrow> b=a"
 proof -
  fix s a b assume edge: "((s,a),b)\<in>C.loop_graph cs"
  have s: "s\<in>cs" using edge unfolding C.loop_graph_def by simp
  show "b=a" by (rule C.loop_graph_identity[OF cr[OF s] ci[OF s] edge])
 qed
 have d: "\<And>s a b. ((s,a),b)\<in>D.loop_graph ds \<Longrightarrow> b=a"
 proof -
  fix s a b assume edge: "((s,a),b)\<in>D.loop_graph ds"
  have s: "s\<in>ds" using edge unfolding D.loop_graph_def by simp
  show "b=a" by (rule D.loop_graph_identity[OF dr[OF s] di[OF s] edge])
 qed
 show ?thesis using c d unfolding generate_def by simp
qed
theorem generated_relation_least:
 "residual_operative cs ds localRel sourceRel \<Longrightarrow> contains_local localRel other \<Longrightarrow>
  quotient_relation(generate cs ds localRel)\<subseteq>other"
 unfolding generate_def using canonical_least by simp
theorem valid_output_requires_realizability:
 "valid_output cs ds localRel out \<Longrightarrow> stage_L3 cs ds"
 unfolding valid_output_def stage_L3_def
 using C.loop_graph_requires_realizability D.loop_graph_requires_realizability by blast
theorem faithful_relation_requires_saturation:
 "(\<And>p. p\<in>synchronized \<Longrightarrow>
   (projection p\<in>quotient_relation out \<longleftrightarrow> snd p\<in>localRel(fst p))) \<Longrightarrow> saturated localRel"
 by (rule saturation_necessary_for_pullback)
end

ML \<open>
val roots = @{thms paired_comparison.generated_valid paired_comparison.output_unique
 paired_comparison.unique_generated_output paired_comparison.generated_local_injective
 paired_comparison.generated_pair_injective paired_comparison.generated_local_pullback
 paired_comparison.generated_source_pullback paired_comparison.generated_loop_identity
 paired_comparison.generated_relation_least paired_comparison.valid_output_requires_realizability
 paired_comparison.faithful_relation_requires_saturation};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
