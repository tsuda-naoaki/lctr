theory Core_Dynamics_Factors
  imports LCTR_Core_Trajectory_Descent.Core_Trajectory_Descent
    LCTR_Factorization_Isabelle.Factorization_Isabelle
begin

definition reach_on where "reach_on Q E = E\<^sup>* \<inter> (Q\<times>Q)"
lemma reach_refl: "refl_on Q (reach_on Q E)"
  unfolding reach_on_def refl_on_def by simp
lemma reach_trans: "trans (reach_on Q E)"
  unfolding reach_on_def trans_def by (blast intro: rtrancl_trans)
lemma reach_contains: "E\<subseteq>Q\<times>Q \<Longrightarrow> E\<subseteq>reach_on Q E"
  unfolding reach_on_def by auto
lemma reach_partial_order:
  "antisym (reach_on Q E) \<Longrightarrow> refl_on Q (reach_on Q E) \<and> trans (reach_on Q E) \<and> antisym (reach_on Q E)"
  using reach_refl[where Q=Q and E=E] reach_trans[where Q=Q and E=E] by simp
lemma reach_least:
  assumes lr: "refl_on Q L" and lt: "trans L" and contains: "E\<subseteq>L"
    and path: "(x,y)\<in>reach_on Q E"
  shows "(x,y)\<in>L"
proof -
  have x: "x\<in>Q" and xy: "(x,y)\<in>E\<^sup>*" using path unfolding reach_on_def by auto
  show ?thesis using xy
  proof (induction rule: rtrancl_induct)
    case base
    show ?case using lr x unfolding refl_on_def by blast
  next
    case (step y z)
    have yz: "(y,z)\<in>L" using contains step.hyps(2) by blast
    show ?case by (rule transD[OF lt step.IH yz])
  qed
qed

locale quotient_factor =
  fixes A :: "'a set" and E :: "('a\<times>'a) set" and g :: "'a\<Rightarrow>'t"
  assumes eqv: "equiv A E"
    and constancy: "\<And>x y. (x,y)\<in>E \<Longrightarrow> g x=g y"
begin
abbreviation q where "q x \<equiv> E``{x}"
definition F where "F = factor_choice A q g"
lemma kernel_inclusion: "eqker_on A q\<subseteq>eqker_on A g"
proof
  fix p
  assume "p\<in>eqker_on A q"
  then have p: "fst p\<in>A" "snd p\<in>A" "q (fst p)=q (snd p)" unfolding eqker_on_def by auto
  have "(fst p,snd p)\<in>E" using eq_equiv_class_iff[OF eqv p(1) p(2)] p(3) by simp
  then have "g (fst p)=g (snd p)" by (rule constancy)
  then show "p\<in>eqker_on A g" using p unfolding eqker_on_def by simp
qed
lemma commutes: "x\<in>A \<Longrightarrow> F (q x)=g x"
  unfolding F_def by (rule factor_choice_agrees[OF kernel_inclusion])
lemma projection_image: "q`A=A//E"
  unfolding quotient_def by auto
lemma factor_image: "F`(A//E)=g`A"
proof -
  have "F`(q`A)=(\<lambda>x. F(q x))`A" by (simp add: image_image)
  also have "...=g`A" by (rule image_cong[OF refl]) (rule commutes)
  finally show ?thesis by (simp only: projection_image)
qed
lemma unique_on:
  assumes h: "\<And>x. x\<in>A \<Longrightarrow> G(q x)=g x" and y: "y\<in>A//E"
  shows "G y=F y"
proof -
  obtain x where x: "x\<in>A" "y=q x" using y by (elim quotientE)
  show ?thesis using h[OF x(1)] commutes[OF x(1)] x(2) by simp
qed
definition edges where "edges r = (\<lambda>(x,y). (q x,q y)) ` (r\<inter>(A\<times>A))"
lemma edges_typed: "edges r\<subseteq>(A//E)\<times>(A//E)"
  unfolding edges_def by (auto intro: quotientI)
lemma source_monotone:
  "x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> (x,y)\<in>r \<Longrightarrow> (q x,q y)\<in>reach_on (A//E) (edges r)"
  using reach_contains[OF edges_typed, of r] unfolding edges_def by force
lemma factor_monotone:
  assumes lr: "refl_on (g`A) L" and lt: "trans L"
    and mono: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> (x,y)\<in>r \<Longrightarrow> (g x,g y)\<in>L"
    and path: "(x,y)\<in>reach_on (A//E) (edges r)"
  shows "(F x,F y)\<in>L"
proof -
  let ?l = "{(u,v). (F u,F v)\<in>L}"
  have rf: "refl_on (A//E) ?l"
  proof (rule refl_onI)
    fix u
    assume u: "u\<in>A//E"
    have "F u\<in>g`A" using imageI[OF u, where f=F] factor_image by simp
    then have "(F u,F u)\<in>L" by (rule refl_onD[OF lr])
    then show "(u,u)\<in>?l" by simp
  qed
  have tr: "trans ?l" using lt unfolding trans_def by blast
  have ed: "edges r\<subseteq>?l"
  proof
    fix p
    assume "p\<in>edges r"
    then obtain a b where ab: "a\<in>A" "b\<in>A" "(a,b)\<in>r" "p=(q a,q b)" unfolding edges_def by auto
    show "p\<in>?l" using mono[OF ab(1,2,3)] commutes[OF ab(1)] commutes[OF ab(2)] ab(4) by simp
  qed
  have "(x,y)\<in>?l" by (rule reach_least[OF rf tr ed path])
  then show ?thesis by simp
qed
end

locale dynamics_factor_pair =
  C: quotient_factor A EC gC + B: quotient_factor B EB gB
  for A :: "'a set" and EC :: "('a\<times>'a) set" and gC :: "'a\<Rightarrow>'t"
    and B :: "'b set" and EB :: "('b\<times>'b) set" and gB :: "'b\<Rightarrow>'s" +
  fixes S :: "('a\<times>'b) set"
  assumes typed: "S\<subseteq>A\<times>B"
begin
lemma trajectory_factor_image:
 "(\<lambda>(c,b). (gC c,gB b)) ` S = (\<lambda>(t,s). (C.F t,B.F s)) ` image_rel EC EB S"
proof -
  have eq: "\<And>p. p\<in>S \<Longrightarrow> (gC (fst p),gB (snd p)) = (C.F (EC``{fst p}),B.F (EB``{snd p}))"
  proof -
    fix p
    assume p: "p\<in>S"
    have a: "fst p\<in>A" and b: "snd p\<in>B" using typed p by auto
    show "(gC (fst p),gB (snd p)) = (C.F (EC``{fst p}),B.F (EB``{snd p}))"
      using C.commutes[OF a] B.commutes[OF b] by simp
  qed
  show ?thesis unfolding image_rel_def image_image
    by (rule image_cong[OF refl]) (use eq in auto)
qed
lemma pair_unique:
  assumes hc: "\<And>x. x\<in>A \<Longrightarrow> FC(EC``{x})=gC x"
    and hb: "\<And>x. x\<in>B \<Longrightarrow> FB(EB``{x})=gB x"
  shows "(\<forall>t\<in>A//EC. FC t=C.F t) \<and> (\<forall>s\<in>B//EB. FB s=B.F s)"
  by (intro conjI ballI; (rule C.unique_on[OF hc] | rule B.unique_on[OF hb]))
end

lemma source_native_factor_interfaces:
  assumes c: "\<And>x y. (x,y)\<in>least_equiv C (generator_c C D B R Bind) \<Longrightarrow> gC x=gC y"
    and b: "\<And>x y. (x,y)\<in>least_equiv B (generator_b C D B R Bind) \<Longrightarrow> gB x=gB y"
  shows "dynamics_factor_pair C (least_equiv C (generator_c C D B R Bind)) gC
    B (least_equiv B (generator_b C D B R Bind)) gB (source_rel C D B R)"
proof (unfold_locales)
  show "equiv C (least_equiv C (generator_c C D B R Bind))"
    by (rule least_equiv_equivalence[OF source_generator_carriers(2)])
  show "\<And>x y. (x,y)\<in>least_equiv C (generator_c C D B R Bind) \<Longrightarrow> gC x=gC y"
    by (rule c)
  show "equiv B (least_equiv B (generator_b C D B R Bind))"
    by (rule least_equiv_equivalence[OF source_generator_carriers(3)])
  show "\<And>x y. (x,y)\<in>least_equiv B (generator_b C D B R Bind) \<Longrightarrow> gB x=gB y"
    by (rule b)
  show "source_rel C D B R\<subseteq>C\<times>B" by (rule source_generator_carriers(1))
qed

lemma empty_reach_control: "reach_on {} E = {}"
  unfolding reach_on_def by simp
ML \<open>
val roots = @{thms reach_refl reach_trans reach_contains reach_partial_order reach_least
  quotient_factor.commutes quotient_factor.factor_image quotient_factor.unique_on
  quotient_factor.edges_typed quotient_factor.source_monotone quotient_factor.factor_monotone
  dynamics_factor_pair.trajectory_factor_image dynamics_factor_pair.pair_unique source_native_factor_interfaces empty_reach_control};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
