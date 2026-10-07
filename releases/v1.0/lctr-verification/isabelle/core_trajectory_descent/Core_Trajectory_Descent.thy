theory Core_Trajectory_Descent
  imports Main
begin

definition least_equiv where "least_equiv A g = \<Inter>{E. equiv A E \<and> g\<subseteq>E}"
lemma least_equiv_minimal: "equiv A E \<Longrightarrow> g\<subseteq>E \<Longrightarrow> least_equiv A g\<subseteq>E"
  unfolding least_equiv_def by blast
lemma least_equiv_contains: "g\<subseteq>least_equiv A g"
  unfolding least_equiv_def by blast
lemma least_equiv_equivalence:
  assumes g: "g\<subseteq>A\<times>A"
  shows "equiv A (least_equiv A g)"
proof -
  have top: "equiv A (A\<times>A)" unfolding equiv_def refl_on_def sym_def trans_def by blast
  have bound: "least_equiv A g\<subseteq>A\<times>A" by (rule least_equiv_minimal[OF top g])
  have rf: "refl_on A (least_equiv A g)"
    unfolding refl_on_def least_equiv_def
    by (intro ballI InterI) (auto simp: equiv_def refl_on_def)
  have sy: "sym (least_equiv A g)"
  proof (rule symI)
    fix x y
    assume xy: "(x,y)\<in>least_equiv A g"
    show "(y,x)\<in>least_equiv A g"
    proof (unfold least_equiv_def, rule InterI)
      fix E
      assume e: "E\<in>{E. equiv A E \<and> g\<subseteq>E}"
      have "(x,y)\<in>E" using xy e unfolding least_equiv_def by blast
      then show "(y,x)\<in>E" using e unfolding equiv_def sym_def by blast
    qed
  qed
  have tr: "trans (least_equiv A g)"
  proof (rule transI)
    fix x y z
    assume xy: "(x,y)\<in>least_equiv A g" and yz: "(y,z)\<in>least_equiv A g"
    show "(x,z)\<in>least_equiv A g"
    proof (unfold least_equiv_def, rule InterI)
      fix E
      assume e: "E\<in>{E. equiv A E \<and> g\<subseteq>E}"
      have "(x,y)\<in>E" "(y,z)\<in>E" using xy yz e unfolding least_equiv_def by blast+
      then show "(x,z)\<in>E" using e unfolding equiv_def trans_def by blast
    qed
  qed
  show ?thesis by (rule equivI[OF bound rf sy tr])
qed

definition source_rel where "source_rel C D B R = {(c,b). c\<in>C \<and> b\<in>B \<and> (\<exists>d\<in>D. (c,d,b)\<in>R)}"
definition generator_c where "generator_c C D B R Bind = {(c,c'). c\<in>C \<and> c'\<in>C \<and>
  (\<exists>d\<in>D. \<exists>b\<in>B. \<exists>d'\<in>D. \<exists>b'\<in>B.
    (c,d,b)\<in>R \<and> (c',d',b')\<in>R \<and> ((c,d,b),(c',d',b'))\<in>Bind)}"
definition generator_b where "generator_b C D B R Bind = {(b,b'). b\<in>B \<and> b'\<in>B \<and>
  (\<exists>c\<in>C. \<exists>d\<in>D. \<exists>c'\<in>C. \<exists>d'\<in>D.
    (c,d,b)\<in>R \<and> (c',d',b')\<in>R \<and> ((c,d,b),(c',d',b'))\<in>Bind)}"
lemma source_generator_carriers:
 "source_rel C D B R\<subseteq>C\<times>B"
 "generator_c C D B R Bind\<subseteq>C\<times>C"
 "generator_b C D B R Bind\<subseteq>B\<times>B"
  unfolding source_rel_def generator_c_def generator_b_def by auto

definition image_rel where "image_rel EC EB S = (\<lambda>(c,b). (EC``{c},EB``{b})) ` S"
locale trajectory_descent =
  fixes C B S EC EB
  assumes ec: "equiv C EC" and eb: "equiv B EB" and typed: "S\<subseteq>C\<times>B"
begin
definition desc where "desc \<longleftrightarrow> (\<forall>c c' b b'. (c,c')\<in>EC \<longrightarrow> (b,b')\<in>EB \<longrightarrow> ((c,b)\<in>S) = ((c',b')\<in>S))"
lemma exact_membership:
  assumes h: desc and c: "c\<in>C" and b: "b\<in>B"
  shows "(EC``{c},EB``{b})\<in>image_rel EC EB S \<longleftrightarrow> (c,b)\<in>S"
proof
  assume "(EC``{c},EB``{b})\<in>image_rel EC EB S"
  then obtain c' b' where p: "(c',b')\<in>S" "EC``{c'}=EC``{c}" "EB``{b'}=EB``{b}"
    unfolding image_rel_def by auto
  have cc: "(c',c)\<in>EC" using eq_equiv_class[OF p(2) ec c] .
  have bb: "(b',b)\<in>EB" using eq_equiv_class[OF p(3) eb b] .
  show "(c,b)\<in>S" using h cc bb p unfolding desc_def by blast
next
  assume "(c,b)\<in>S"
  then show "(EC``{c},EB``{b})\<in>image_rel EC EB S" unfolding image_rel_def by force
qed
lemma image_descent:
  assumes "(c,c')\<in>EC" "(b,b')\<in>EB"
  shows "((EC``{c},EB``{b})\<in>image_rel EC EB S) = ((EC``{c'},EB``{b'})\<in>image_rel EC EB S)"
  using equiv_class_eq[OF ec assms(1)] equiv_class_eq[OF eb assms(2)] by simp
lemma image_typed: "image_rel EC EB S\<subseteq>(C//EC)\<times>(B//EB)"
  using typed unfolding image_rel_def quotient_def by auto
lemma exact_membership_implies_desc:
  assumes h: "\<And>c b. c\<in>C \<Longrightarrow> b\<in>B \<Longrightarrow>
    ((EC``{c},EB``{b})\<in>image_rel EC EB S) = ((c,b)\<in>S)"
  shows desc
proof (unfold desc_def, intro allI impI)
  fix c c' b b'
  assume cc: "(c,c')\<in>EC" and bb: "(b,b')\<in>EB"
  have cs: "c\<in>C" "c'\<in>C" using equiv_type[OF ec] cc by auto
  have bs: "b\<in>B" "b'\<in>B" using equiv_type[OF eb] bb by auto
  show "((c,b)\<in>S) = ((c',b')\<in>S)"
    using h[OF cs(1) bs(1)] h[OF cs(2) bs(2)] image_descent[OF cc bb] by blast
qed
end

lemma native_trajectory_interface:
 "trajectory_descent C B (source_rel C D B R)
   (least_equiv C (generator_c C D B R Bind))
   (least_equiv B (generator_b C D B R Bind))"
  by standard (rule least_equiv_equivalence[OF source_generator_carriers(2)],
    rule least_equiv_equivalence[OF source_generator_carriers(3)], rule source_generator_carriers(1))

definition graph_map where "graph_map S t = (SOME s. (t,s)\<in>S)"
lemma graph_map_member: "t\<in>Domain S \<Longrightarrow> (t,graph_map S t)\<in>S"
  unfolding graph_map_def by (rule someI_ex) blast
lemma native_graph_trajectory:
  fixes S :: "('a\<times>'b) set"
  assumes single: "\<And>t s s'. (t,s)\<in>S \<Longrightarrow> (t,s')\<in>S \<Longrightarrow> s=s'"
  shows "S = {(t,graph_map S t) |t. t\<in>Domain S}"
    and "\<And>G. (\<And>t. t\<in>Domain S \<Longrightarrow> (t,G t)\<in>S) \<Longrightarrow> \<forall>t\<in>Domain S. G t=graph_map S t"
proof -
  show "S = {(t,graph_map S t) |t. t\<in>Domain S}"
  proof (rule set_eqI)
    fix p :: "'a\<times>'b"
    obtain t s where p: "p=(t,s)" by (cases p) auto
    show "p\<in>S \<longleftrightarrow> p\<in>{(t,graph_map S t) |t. t\<in>Domain S}"
    proof
      assume ps: "p\<in>S"
      have ts: "(t,s)\<in>S" using ps p by simp
      have t: "t\<in>Domain S" using ts by blast
      have "s=graph_map S t" by (rule single[OF ts graph_map_member[OF t]])
      then show "p\<in>{(t,graph_map S t) |t. t\<in>Domain S}" using p t by blast
    next
      assume "p\<in>{(t,graph_map S t) |t. t\<in>Domain S}"
      then obtain x where x: "x\<in>Domain S" "p=(x,graph_map S x)" by blast
      show "p\<in>S" using graph_map_member[OF x(1)] x(2) by simp
    qed
  qed
  fix G
  assume h: "\<And>t. t\<in>Domain S \<Longrightarrow> (t,G t)\<in>S"
  show "\<forall>t\<in>Domain S. G t=graph_map S t"
    by (intro ballI, rule single[OF h graph_map_member])
qed
lemma empty_relation_control: "image_rel EC EB {} = {}" "Domain (image_rel EC EB {}) = {}"
  unfolding image_rel_def by simp_all
lemma missing_descent_control:
  defines "EC \<equiv> UNIV\<times>UNIV :: (bool\<times>bool) set"
  shows "(EC``{False},{()})\<in>image_rel EC {((),())} {(True,())} \<and> (False,())\<notin>{(True,())}"
  unfolding EC_def image_rel_def by auto

ML \<open>
val roots = @{thms least_equiv_minimal least_equiv_contains least_equiv_equivalence source_generator_carriers
  trajectory_descent.exact_membership trajectory_descent.image_descent trajectory_descent.image_typed
  trajectory_descent.exact_membership_implies_desc native_trajectory_interface
  native_graph_trajectory empty_relation_control missing_descent_control};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
