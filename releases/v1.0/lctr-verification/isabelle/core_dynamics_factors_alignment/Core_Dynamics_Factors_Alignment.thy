theory Core_Dynamics_Factors_Alignment
  imports LCTR_Core_Dynamics_Factors.Core_Dynamics_Factors
begin

lemmas native_generated_partial_order = Core_Dynamics_Factors.reach_partial_order
lemmas native_order_minimality = Core_Dynamics_Factors.reach_least

lemma trajectory_factor_image:
  assumes hc: "\<And>c. c\<in>C \<Longrightarrow> fC (EC``{c})=gC c"
    and hb: "\<And>b. b\<in>B \<Longrightarrow> fB (EB``{b})=gB b"
    and typed: "S\<subseteq>C\<times>B"
  shows "(\<lambda>(c,b). (gC c,gB b)) ` S =
    (\<lambda>(t,s). (fC t,fB s)) ` image_rel EC EB S"
  unfolding image_rel_def image_image
  by (rule image_cong[OF refl]) (use typed hc hb in auto)

context dynamics_factor_pair
begin
definition factor_conditions where
  "factor_conditions TC TB r L FC FB \<longleftrightarrow>
    FC`(A//EC)=TC \<and> FB`(B//EB)=TB \<and>
    (\<forall>c\<in>A. FC (EC``{c})=gC c) \<and>
    (\<forall>b\<in>B. FB (EB``{b})=gB b) \<and>
    (\<forall>x y. (x,y)\<in>reach_on (A//EC) (C.edges r) \<longrightarrow> (FC x,FC y)\<in>L) \<and>
    (\<lambda>(c,b). (gC c,gB b)) ` S = (\<lambda>(t,s). (FC t,FB s)) ` image_rel EC EB S"

lemma native_factor_pair_exists_unique:
  assumes ontoC: "gC`A=TC" and ontoB: "gB`B=TB"
    and lr: "refl_on TC L" and lt: "trans L"
    and mono: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> (x,y)\<in>r \<Longrightarrow> (gC x,gC y)\<in>L"
  shows "\<exists>FC FB. factor_conditions TC TB r L FC FB \<and>
    (\<forall>GC GB. factor_conditions TC TB r L GC GB \<longrightarrow>
      (\<forall>t\<in>A//EC. GC t=FC t) \<and> (\<forall>s\<in>B//EB. GB s=FB s))"
proof -
  have rf: "refl_on (gC`A) L" using lr ontoC by simp
  have monoF: "\<And>x y. (x,y)\<in>reach_on (A//EC) (C.edges r) \<Longrightarrow> (C.F x,C.F y)\<in>L"
    by (rule C.factor_monotone[OF rf lt mono])
  have conditions: "factor_conditions TC TB r L C.F B.F"
    unfolding factor_conditions_def
    using C.factor_image B.factor_image ontoC ontoB C.commutes B.commutes
      monoF dynamics_factor_pair.trajectory_factor_image[OF dynamics_factor_pair_axioms]
    by blast
  have unique: "\<And>GC GB. factor_conditions TC TB r L GC GB \<Longrightarrow>
       (\<forall>t\<in>A//EC. GC t=C.F t) \<and> (\<forall>s\<in>B//EB. GB s=B.F s)"
  proof -
    fix GC GB
    assume h: "factor_conditions TC TB r L GC GB"
    have hc: "\<And>x. x\<in>A \<Longrightarrow> GC (EC``{x})=gC x"
      and hb: "\<And>x. x\<in>B \<Longrightarrow> GB (EB``{x})=gB x"
      using h unfolding factor_conditions_def by blast+
    show "(\<forall>t\<in>A//EC. GC t=C.F t) \<and> (\<forall>s\<in>B//EB. GB s=B.F s)"
      by (rule pair_unique[OF hc hb])
  qed
  show ?thesis using conditions unique by blast
qed
end

lemma source_native_factor_pair:
  assumes cc: "\<And>x y. (x,y)\<in>least_equiv C (generator_c C D B R Bind) \<Longrightarrow> gC x=gC y"
    and cb: "\<And>x y. (x,y)\<in>least_equiv B (generator_b C D B R Bind) \<Longrightarrow> gB x=gB y"
    and ontoC: "gC`C=TC" and ontoB: "gB`B=TB"
    and lr: "refl_on TC L" and lt: "trans L"
    and mono: "\<And>x y. x\<in>C \<Longrightarrow> y\<in>C \<Longrightarrow> (x,y)\<in>r \<Longrightarrow> (gC x,gC y)\<in>L"
  shows "\<exists>FC FB.
    dynamics_factor_pair.factor_conditions C (least_equiv C (generator_c C D B R Bind)) gC
      B (least_equiv B (generator_b C D B R Bind)) gB (source_rel C D B R) TC TB r L FC FB \<and>
    (\<forall>GC GB.
      dynamics_factor_pair.factor_conditions C (least_equiv C (generator_c C D B R Bind)) gC
        B (least_equiv B (generator_b C D B R Bind)) gB (source_rel C D B R) TC TB r L GC GB
      \<longrightarrow>
      (\<forall>t\<in>C//least_equiv C (generator_c C D B R Bind). GC t=FC t) \<and>
      (\<forall>s\<in>B//least_equiv B (generator_b C D B R Bind). GB s=FB s))"
proof -
  interpret N: dynamics_factor_pair C "least_equiv C (generator_c C D B R Bind)" gC
    B "least_equiv B (generator_b C D B R Bind)" gB "source_rel C D B R"
    by (rule source_native_factor_interfaces[OF cc cb])
  show ?thesis by (rule N.native_factor_pair_exists_unique[OF ontoC ontoB lr lt mono])
qed

lemma canonical_projection_surjective: "(\<lambda>x. E``{x}) ` A = A//E"
  unfolding quotient_def by auto
lemmas canonical_projection_class = eq_equiv_class_iff
definition source_quotient_edges where
  "source_quotient_edges A E r =
    (\<lambda>(x,y). (E``{x},E``{y})) ` (r\<inter>(A\<times>A))"
lemma canonical_source_order_preserved:
  assumes x: "x\<in>A" and y: "y\<in>A" and xy: "(x,y)\<in>r"
  shows "(E``{x},E``{y})\<in>reach_on (A//E) (source_quotient_edges A E r)"
proof -
  have edge: "(E``{x},E``{y})\<in>source_quotient_edges A E r"
    using x y xy unfolding source_quotient_edges_def by force
  have xc: "E``{x}\<in>A//E" and yc: "E``{y}\<in>A//E"
    using x y by (auto intro: quotientI)
  show ?thesis using edge xc yc unfolding reach_on_def by auto
qed
context quotient_factor
begin
lemma source_quotient_edges_agree: "edges r = source_quotient_edges A E r"
  unfolding edges_def source_quotient_edges_def by simp
end

ML \<open>
val roots = @{thms native_generated_partial_order native_order_minimality trajectory_factor_image
  dynamics_factor_pair.native_factor_pair_exists_unique source_native_factor_pair
  canonical_projection_surjective canonical_projection_class canonical_source_order_preserved};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
if null (Thm_Deps.all_oracles @{thms quotient_factor.source_quotient_edges_agree}) then ()
else error "Unexpected edge-definition oracle";
\<close>
end
