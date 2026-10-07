theory Dynamics_Refinement_Alignment
  imports "LCTR_Core_Dynamics_Refinement.Core_Dynamics_Refinement"
    "LCTR_Core_Dynamics_Factors_Alignment.Core_Dynamics_Factors_Alignment"
begin

context presentations
begin
lemmas alignment_refinement_refl = refinement_refl
lemmas alignment_refinement_trans = refinement_trans
lemmas alignment_mutual_factor_inverse = mutual_inverse
lemmas alignment_refinement_descends = refines_desc
lemmas alignment_isomorphism_class_partial_order = isomorphism_class_partial_order

definition structural_iso where
 "structural_iso i j f g h l \<longleftrightarrow>
  f`T i=T j \<and> g`S i=S j \<and> h`T j=T i \<and> l`S j=S i \<and>
  (\<forall>x\<in>T i. h(f x)=x) \<and> (\<forall>x\<in>T j. f(h x)=x) \<and>
  (\<forall>y\<in>S i. l(g y)=y) \<and> (\<forall>y\<in>S j. g(l y)=y) \<and>
  (\<forall>c\<in>C. f(qc i c)=qc j c) \<and> (\<forall>b\<in>B. g(qb i b)=qb j b) \<and>
  (\<forall>x\<in>T i. \<forall>y\<in>T i. le j (f x) (f y) \<longleftrightarrow> le i x y) \<and>
  (\<forall>x\<in>T i. \<forall>y\<in>S i. (f x,g y)\<in>trj j \<longleftrightarrow> (x,y)\<in>trj i)"

lemma structural_iso_forward:
  assumes e: "structural_iso i j f g h l"
  shows "arrow i j f g"
proof -
  have eq: "trj j=(\<lambda>(x,y). (f x,g y))`trj i"
  proof (rule set_eqI)
    fix p :: "'t\<times>'s"
    obtain x y where p: "p=(x,y)" by (cases p) auto
    show "p\<in>trj j \<longleftrightarrow> p\<in>(\<lambda>(x,y). (f x,g y))`trj i"
    proof
      assume hp: "p\<in>trj j"
      have xy: "x\<in>T j" "y\<in>S j" using typed[of j] hp p by auto
      have hx: "h x\<in>T i" and ly: "l y\<in>S i"
        using e xy unfolding structural_iso_def by blast+
      have returned: "(h x,l y)\<in>trj i"
        using e xy hx ly hp p unfolding structural_iso_def by metis
      have inv: "f(h x)=x" "g(l y)=y" using e xy unfolding structural_iso_def by blast+
      have member: "(f(h x),g(l y))\<in>(\<lambda>(a,b). (f a,g b))`trj i"
        using imageI[OF returned, where f="\<lambda>(a,b). (f a,g b)"] by simp
      show "p\<in>(\<lambda>(x,y). (f x,g y))`trj i" using member p inv by simp
    next
      assume "p\<in>(\<lambda>(x,y). (f x,g y))`trj i"
      then obtain a b where ab: "(a,b)\<in>trj i" "p=(f a,g b)" by auto
      have a: "a\<in>T i" and b: "b\<in>S i" using typed[of i] ab(1) by auto
      show "p\<in>trj j" using e a b ab unfolding structural_iso_def by blast
    qed
  qed
  show ?thesis using e eq unfolding structural_iso_def arrow_def by blast
qed

lemma structural_iso_backward:
  assumes e: "structural_iso i j f g h l"
  shows "arrow j i h l"
proof -
  have fc: "\<forall>c\<in>C. h(qc j c)=qc i c"
  proof
    fix c assume c: "c\<in>C"
    have mem: "qc i c\<in>T i" using imageI[OF c, where f="qc i"] ontoC[of i] by simp
    have comm: "f(qc i c)=qc j c" using e c unfolding structural_iso_def by blast
    have inv: "h(f(qc i c))=qc i c" using e mem unfolding structural_iso_def by blast
    show "h(qc j c)=qc i c" using inv comm by simp
  qed
  have fb: "\<forall>b\<in>B. l(qb j b)=qb i b"
  proof
    fix b assume b: "b\<in>B"
    have mem: "qb i b\<in>S i" using imageI[OF b, where f="qb i"] ontoB[of i] by simp
    have comm: "g(qb i b)=qb j b" using e b unfolding structural_iso_def by blast
    have inv: "l(g(qb i b))=qb i b" using e mem unfolding structural_iso_def by blast
    show "l(qb j b)=qb i b" using inv comm by simp
  qed
  have mo: "\<forall>x\<in>T j. \<forall>y\<in>T j. le j x y \<longrightarrow> le i (h x) (h y)"
  proof (intro ballI impI)
    fix x y assume xy: "x\<in>T j" "y\<in>T j" "le j x y"
    have hx: "h x\<in>T i" and hy: "h y\<in>T i" using e xy unfolding structural_iso_def by blast+
    show "le i (h x) (h y)" using e xy hx hy unfolding structural_iso_def by metis
  qed
  have forward: "arrow i j f g" by (rule structural_iso_forward[OF e])
  have image: "trj j=(\<lambda>(x,y). (f x,g y))`trj i" using forward unfolding arrow_def by blast
  have inv: "\<And>x y. (x,y)\<in>trj i \<Longrightarrow> (h(f x),l(g y))=(x,y)"
    using e typed[of i] unfolding structural_iso_def by auto
  have ident: "(\<lambda>p. (h(f(fst p)),l(g(snd p))))`trj i=trj i"
  proof -
    have "(\<lambda>p. (h(f(fst p)),l(g(snd p))))`trj i=id`trj i"
      by (rule image_cong[OF refl]) (use inv in \<open>auto\<close>)
    then show ?thesis by simp
  qed
  have eq: "trj i=(\<lambda>(x,y). (h x,l y))`trj j"
    by (simp only: image image_image case_prod_beta fst_conv snd_conv ident)
  show ?thesis using e fc fb mo eq unfolding structural_iso_def arrow_def by blast
qed

lemma alignment_mutual_iff_iso:
  "(refines i j \<and> refines j i) \<longleftrightarrow> (\<exists>f g h l. structural_iso i j f g h l)"
proof
  assume r: "refines i j \<and> refines j i"
  obtain f g h l where f: "arrow i j f g" and h: "arrow j i h l" using r unfolding refines_def by blast
  have inv: "(\<forall>x\<in>T i. h(f x)=x) \<and> (\<forall>x\<in>T j. f(h x)=x) \<and>
    (\<forall>y\<in>S i. l(g y)=y) \<and> (\<forall>y\<in>S j. g(l y)=y)" by (rule mutual_inverse[OF f h])
  have order: "\<forall>x\<in>T i. \<forall>y\<in>T i. le j (f x) (f y) \<longleftrightarrow> le i x y"
    using mutual_order_iso[OF f h] by blast
  have tr: "\<forall>x\<in>T i. \<forall>y\<in>S i. (f x,g y)\<in>trj j \<longleftrightarrow> (x,y)\<in>trj i"
    using mutual_trajectory_iso[OF f h] by blast
  have "structural_iso i j f g h l"
    using inv order tr f h unfolding structural_iso_def arrow_def
    by iprover
  then show "\<exists>f g h l. structural_iso i j f g h l" by blast
next
  assume "\<exists>f g h l. structural_iso i j f g h l"
  then obtain f g h l where e: "structural_iso i j f g h l" by blast
  show "refines i j \<and> refines j i" unfolding refines_def
    using structural_iso_forward[OF e] structural_iso_backward[OF e] by blast
qed
end

definition native_admissible where
 "native_admissible C B EC EB ord R qc qb L trj \<longleftrightarrow>
  (\<forall>x y. (x,y)\<in>EC \<longrightarrow> qc x=qc y) \<and>
  (\<forall>x y. (x,y)\<in>EB \<longrightarrow> qb x=qb y) \<and>
  (\<forall>x\<in>C. \<forall>y\<in>C. (x,y)\<in>ord \<longrightarrow> (qc x,qc y)\<in>L) \<and>
  trj=(\<lambda>(c,b). (qc c,qb b))`R"

lemma alignment_canonical_admissible:
  assumes ec: "equiv C EC" and eb: "equiv B EB"
  shows "native_admissible C B EC EB ord R (\<lambda>c. EC``{c}) (\<lambda>b. EB``{b})
    (reach_on (C//EC) (source_quotient_edges C EC ord)) (image_rel EC EB R)"
proof -
  have cc: "\<forall>x y. (x,y)\<in>EC \<longrightarrow> EC``{x}=EC``{y}"
    using equiv_class_eq[OF ec] by blast
  have cb: "\<forall>x y. (x,y)\<in>EB \<longrightarrow> EB``{x}=EB``{y}"
    using equiv_class_eq[OF eb] by blast
  have mono: "\<forall>x\<in>C. \<forall>y\<in>C. (x,y)\<in>ord \<longrightarrow>
    (EC``{x},EC``{y})\<in>reach_on (C//EC) (source_quotient_edges C EC ord)"
    by (intro ballI impI) (rule canonical_source_order_preserved)
  show ?thesis using cc cb mono unfolding native_admissible_def image_rel_def by simp
qed

lemma alignment_native_canonical_greatest:
  assumes ec: "equiv C EC" and eb: "equiv B EB" and typed: "R\<subseteq>C\<times>B"
    and adm: "native_admissible C B EC EB ord R qc qb L trj"
    and rf: "refl_on (qc`C) L" and tr: "trans L"
  shows "\<exists>FC FB. dynamics_factor_pair.factor_conditions C EC qc B EB qb R
      (qc`C) (qb`B) ord L FC FB \<and>
    (\<forall>GC GB. dynamics_factor_pair.factor_conditions C EC qc B EB qb R
      (qc`C) (qb`B) ord L GC GB \<longrightarrow>
      (\<forall>t\<in>C//EC. GC t=FC t) \<and> (\<forall>s\<in>B//EB. GB s=FB s))"
proof -
  interpret N: dynamics_factor_pair C EC qc B EB qb R
    by unfold_locales (use ec eb typed adm in \<open>auto simp: native_admissible_def\<close>)
  have mono: "\<And>x y. x\<in>C \<Longrightarrow> y\<in>C \<Longrightarrow> (x,y)\<in>ord \<Longrightarrow> (qc x,qc y)\<in>L"
    using adm unfolding native_admissible_def by blast
  show ?thesis by (rule N.native_factor_pair_exists_unique[OF refl refl rf tr mono])
qed

locale canonical_presentations =
  presentations C B T S qc qb le trj
  for C :: "'c set" and B :: "'b set"
    and T :: "'i \<Rightarrow> 'c set set" and S :: "'i \<Rightarrow> 'b set set"
    and qc :: "'i \<Rightarrow> 'c \<Rightarrow> 'c set" and qb :: "'i \<Rightarrow> 'b \<Rightarrow> 'b set"
    and le :: "'i \<Rightarrow> 'c set \<Rightarrow> 'c set \<Rightarrow> bool"
    and trj :: "'i \<Rightarrow> ('c set\<times>'b set) set" +
  fixes EC :: "('c\<times>'c) set" and EB :: "('b\<times>'b) set"
    and ord :: "('c\<times>'c) set" and R :: "('c\<times>'b) set" and k :: 'i
  assumes ec: "equiv C EC" and eb: "equiv B EB" and relation_typed: "R\<subseteq>C\<times>B"
    and canonical_C: "qc k=(\<lambda>c. EC``{c})"
    and canonical_B: "qb k=(\<lambda>b. EB``{b})"
    and canonical_order: "le k=(\<lambda>x y. (x,y)\<in>reach_on (C//EC) (source_quotient_edges C EC ord))"
    and canonical_trj: "trj k=image_rel EC EB R"
begin

lemma factor_is_arrow:
  assumes a: "native_admissible C B EC EB ord R (qc i) (qb i) L (trj i)"
    and law: "L={(x,y). x\<in>T i \<and> y\<in>T i \<and> le i x y}"
    and factors: "dynamics_factor_pair.factor_conditions C EC (qc i) B EB (qb i) R
      (qc i`C) (qb i`B) ord L FC FB"
  shows "arrow k i FC FB"
proof -
  interpret N: dynamics_factor_pair C EC "qc i" B EB "qb i" R
    by unfold_locales (use ec eb relation_typed a in \<open>auto simp: native_admissible_def\<close>)
  have TC: "T k=C//EC"
    using ontoC[of k] unfolding canonical_C canonical_projection_surjective by simp
  have TB: "S k=B//EB"
    using ontoB[of k] unfolding canonical_B canonical_projection_surjective by simp
  have f: "FC`(C//EC)=T i" "FB`(B//EB)=S i"
    and c: "\<forall>c\<in>C. FC (EC``{c})=qc i c"
    and b: "\<forall>b\<in>B. FB (EB``{b})=qb i b"
    and mono: "\<forall>x y. (x,y)\<in>reach_on (C//EC) (source_quotient_edges C EC ord) \<longrightarrow> (FC x,FC y)\<in>L"
    and image: "(\<lambda>(c,b). (qc i c,qb i b))`R=(\<lambda>(t,s). (FC t,FB s))`image_rel EC EB R"
    using factors
    unfolding N.factor_conditions_def N.C.source_quotient_edges_agree ontoC ontoB
    by iprover+
  have fC: "FC`T k=T i" and fB: "FB`S k=S i"
    using f TC TB by simp_all
  have cC: "\<forall>c\<in>C. FC(qc k c)=qc i c"
    using c by (simp only: canonical_C)
  have cB: "\<forall>b\<in>B. FB(qb k b)=qb i b"
    using b by (simp only: canonical_B)
  have mo: "\<forall>x\<in>T k. \<forall>y\<in>T k. le k x y \<longrightarrow> le i (FC x) (FC y)"
  proof (intro ballI impI)
    fix x y assume "x\<in>T k" "y\<in>T k" and h: "le k x y"
    have "(x,y)\<in>reach_on (C//EC) (source_quotient_edges C EC ord)"
      using h by (simp only: canonical_order)
    then have "(FC x,FC y)\<in>L" using mono by blast
    then show "le i (FC x) (FC y)" unfolding law by simp
  qed
  have ti: "trj i=(\<lambda>(c,b). (qc i c,qb i b))`R"
    using a unfolding native_admissible_def by iprover
  have trj_image: "trj i=(\<lambda>(t,s). (FC t,FB s))`trj k"
    by (simp only: ti image canonical_trj)
  show ?thesis unfolding arrow_def
    using fC fB cC cB mo trj_image by iprover
qed

lemma native_refinement:
  assumes a: "native_admissible C B EC EB ord R (qc i) (qb i) L (trj i)"
    and law: "L={(x,y). x\<in>T i \<and> y\<in>T i \<and> le i x y}"
    and rf: "refl_on (T i) L" and tr: "trans L"
  shows "refines i k"
proof -
  have rf': "refl_on (qc i`C) L" using rf ontoC[of i] by simp
  obtain FC FB where f: "dynamics_factor_pair.factor_conditions C EC (qc i) B EB (qb i) R
      (qc i`C) (qb i`B) ord L FC FB"
    using alignment_native_canonical_greatest[OF ec eb relation_typed a rf' tr] by blast
  have "arrow k i FC FB" by (rule factor_is_arrow[OF a law f])
  then show ?thesis unfolding refines_def by blast
qed

lemma alignment_native_canonical_class_greatest:
  "native_admissible C B EC EB ord R (qc i) (qb i) L (trj i) \<Longrightarrow>
   L={(x,y). x\<in>T i \<and> y\<in>T i \<and> le i x y} \<Longrightarrow>
   refl_on (T i) L \<Longrightarrow> trans L \<Longrightarrow>
   qrel UNIV E refines (E``{i}) (E``{k})"
  using native_refinement class_refinement_relation by blast

lemma alignment_source_native_canonical_class_greatest:
  assumes c: "EC=least_equiv C (generator_c C D B Rel Bind)"
    and b: "EB=least_equiv B (generator_b C D B Rel Bind)"
    and r: "R=source_rel C D B Rel"
    and a: "native_admissible C B
      (least_equiv C (generator_c C D B Rel Bind))
      (least_equiv B (generator_b C D B Rel Bind)) ord (source_rel C D B Rel)
      (qc i) (qb i) L (trj i)"
    and law: "L={(x,y). x\<in>T i \<and> y\<in>T i \<and> le i x y}"
    and rf: "refl_on (T i) L" and tr: "trans L"
  shows "qrel UNIV E refines (E``{i}) (E``{k})"
  by (rule alignment_native_canonical_class_greatest[OF _ law rf tr])
    (use a c b r in simp)
end

lemmas alignment_missing_projection_surjectivity_control = missing_projection_surjectivity_control

ML \<open>
val roots = @{thms presentations.alignment_refinement_refl presentations.alignment_refinement_trans
  presentations.alignment_mutual_factor_inverse presentations.alignment_mutual_iff_iso
  presentations.alignment_refinement_descends presentations.alignment_isomorphism_class_partial_order
  alignment_canonical_admissible alignment_native_canonical_greatest
  canonical_presentations.alignment_native_canonical_class_greatest
  canonical_presentations.alignment_source_native_canonical_class_greatest
  alignment_missing_projection_surjectivity_control};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
