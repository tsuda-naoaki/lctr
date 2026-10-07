theory Core_Dynamics_Refinement
  imports LCTR_Core_Dynamics_Factors.Core_Dynamics_Factors
    LCTR_Core_Preorder_Quotient.Core_Preorder_Quotient
begin

locale presentations =
  fixes C :: "'c set" and B :: "'b set"
    and T :: "'i \<Rightarrow> 't set" and S :: "'i \<Rightarrow> 's set"
    and qc :: "'i \<Rightarrow> 'c \<Rightarrow> 't" and qb :: "'i \<Rightarrow> 'b \<Rightarrow> 's"
    and le :: "'i \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> bool"
    and trj :: "'i \<Rightarrow> ('t\<times>'s) set"
  assumes ontoC: "\<And>i. qc i ` C = T i"
    and ontoB: "\<And>i. qb i ` B = S i"
    and typed: "\<And>i. trj i \<subseteq> T i \<times> S i"
begin

definition arrow where
 "arrow i j f g = (f`T i = T j \<and> g`S i = S j \<and>
   (\<forall>c\<in>C. f(qc i c)=qc j c) \<and> (\<forall>b\<in>B. g(qb i b)=qb j b) \<and>
   (\<forall>x\<in>T i. \<forall>y\<in>T i. le i x y \<longrightarrow> le j (f x) (f y)) \<and>
   trj j = (\<lambda>(x,y). (f x,g y)) ` trj i)"
definition refines where "refines i j = (\<exists>f g. arrow j i f g)"

lemma arrow_id: "arrow i i id id"
  unfolding arrow_def by simp
lemma arrow_comp:
  assumes f: "arrow i j f g" and h: "arrow j k h l"
  shows "arrow i k (h\<circ>f) (l\<circ>g)"
proof -
  have fo: "f`T i=T j" "g`S i=S j" and ho: "h`T j=T k" "l`S j=S k"
    using f h unfolding arrow_def by auto
  have fc: "\<forall>c\<in>C. (h\<circ>f)(qc i c)=qc k c"
    using f h unfolding arrow_def by auto
  have fb: "\<forall>b\<in>B. (l\<circ>g)(qb i b)=qb k b"
    using f h unfolding arrow_def by auto
  have mo: "\<forall>x\<in>T i. \<forall>y\<in>T i. le i x y \<longrightarrow> le k ((h\<circ>f)x) ((h\<circ>f)y)"
  proof (intro ballI impI)
    fix x y assume x: "x\<in>T i" and y: "y\<in>T i" and xy: "le i x y"
    have fx: "f x\<in>T j" using imageI[OF x, where f=f] fo(1) by simp
    have fy: "f y\<in>T j" using imageI[OF y, where f=f] fo(1) by simp
    have fj: "le j (f x) (f y)" using f x y xy unfolding arrow_def by blast
    have hk: "le k (h(f x)) (h(f y))" using h fx fy fj unfolding arrow_def by blast
    show "le k ((h\<circ>f)x) ((h\<circ>f)y)" using hk by simp
  qed
  have ti: "trj j=(\<lambda>(x,y). (f x,g y))`trj i" and tj: "trj k=(\<lambda>(x,y). (h x,l y))`trj j"
    using f h unfolding arrow_def by auto
  have tt: "trj k=(\<lambda>(x,y). ((h\<circ>f)x,(l\<circ>g)y))`trj i"
    by (simp only: tj ti image_image) (simp add: case_prod_beta)
  have oc: "(h\<circ>f)`T i=T k" by (simp only: comp_def image_image[symmetric] fo ho)
  have ob: "(l\<circ>g)`S i=S k" by (simp only: comp_def image_image[symmetric] fo ho)
  show ?thesis using oc ob fc fb mo tt unfolding arrow_def by blast
qed
lemma refinement_refl: "refines i i"
  unfolding refines_def using arrow_id[of i] by blast
lemma refinement_trans:
  assumes "refines i j" "refines j k"
  shows "refines i k"
proof -
  obtain f g where f: "arrow j i f g" using assms(1) unfolding refines_def by blast
  obtain h l where h: "arrow k j h l" using assms(2) unfolding refines_def by blast
  have "arrow k i (f\<circ>h) (g\<circ>l)" by (rule arrow_comp[OF h f])
  then show ?thesis unfolding refines_def by blast
qed

lemma mutual_inverse:
  assumes f: "arrow i j f g" and h: "arrow j i h l"
  shows "(\<forall>x\<in>T i. h(f x)=x) \<and> (\<forall>x\<in>T j. f(h x)=x) \<and>
         (\<forall>y\<in>S i. l(g y)=y) \<and> (\<forall>y\<in>S j. g(l y)=y)"
proof -
  have a: "\<forall>x\<in>T i. h(f x)=x"
  proof (intro ballI)
    fix x assume x: "x\<in>T i"
    obtain c where c: "c\<in>C" "x=qc i c" using x ontoC[of i] by blast
    show "h(f x)=x" using f h c unfolding arrow_def by auto
  qed
  have b: "\<forall>x\<in>T j. f(h x)=x"
  proof (intro ballI)
    fix x assume x: "x\<in>T j"
    obtain c where c: "c\<in>C" "x=qc j c" using x ontoC[of j] by blast
    show "f(h x)=x" using f h c unfolding arrow_def by auto
  qed
  have c: "\<forall>y\<in>S i. l(g y)=y"
  proof (intro ballI)
    fix y assume y: "y\<in>S i"
    obtain b where b: "b\<in>B" "y=qb i b" using y ontoB[of i] by blast
    show "l(g y)=y" using f h b unfolding arrow_def by auto
  qed
  have d: "\<forall>y\<in>S j. g(l y)=y"
  proof (intro ballI)
    fix y assume y: "y\<in>S j"
    obtain b where b: "b\<in>B" "y=qb j b" using y ontoB[of j] by blast
    show "g(l y)=y" using f h b unfolding arrow_def by auto
  qed
  show ?thesis using a b c d by simp
qed

lemma mutual_bijections:
  assumes f: "arrow i j f g" and h: "arrow j i h l"
  shows "bij_betw f (T i) (T j) \<and> bij_betw g (S i) (S j)"
proof -
  note inv = mutual_inverse[OF f h]
  have fi: "inj_on f (T i)" and gi: "inj_on g (S i)"
    using inv unfolding inj_on_def by metis+
  show ?thesis using fi gi f unfolding arrow_def bij_betw_def by auto
qed

lemma mutual_order_iso:
  assumes f: "arrow i j f g" and h: "arrow j i h l" and x: "x\<in>T i" and y: "y\<in>T i"
  shows "le j (f x) (f y) = le i x y"
proof -
  note inv = mutual_inverse[OF f h]
  have fx: "f x\<in>T j" and fy: "f y\<in>T j" using f x y unfolding arrow_def by auto
  show ?thesis using f h x y fx fy inv unfolding arrow_def by metis
qed

lemma mutual_trajectory_iso:
  assumes f: "arrow i j f g" and h: "arrow j i h l" and x: "x\<in>T i" and y: "y\<in>S i"
  shows "((f x,g y)\<in>trj j) = ((x,y)\<in>trj i)"
proof
  assume t: "(f x,g y)\<in>trj j"
  have eq: "trj j=(\<lambda>(a,b). (f a,g b))`trj i" using f unfolding arrow_def by blast
  obtain p where p: "p\<in>trj i" "(f x,g y)=(f(fst p),g(snd p))" using t unfolding eq by auto
  have pt: "fst p\<in>T i" "snd p\<in>S i" using typed[of i] p(1) by auto
  note inv = mutual_inverse[OF f h]
  have ic: "h(f(fst p))=fst p" "h(f x)=x" using inv pt(1) x by blast+
  have ib: "l(g(snd p))=snd p" "l(g y)=y" using inv pt(2) y by blast+
  have ceq: "f(fst p)=f x" and beq: "g(snd p)=g y" using p(2) by auto
  have px: "fst p=x" using ic ceq by metis
  have py: "snd p=y" using ib beq by metis
  show "(x,y)\<in>trj i" using p(1) px py by (metis surjective_pairing)
next
  assume t: "(x,y)\<in>trj i"
  show "(f x,g y)\<in>trj j" using f t unfolding arrow_def by force
qed

definition iso where
 "iso i j = (\<exists>f g h l. arrow i j f g \<and> arrow j i h l \<and>
  (\<forall>x\<in>T i. h(f x)=x) \<and> (\<forall>x\<in>T j. f(h x)=x) \<and>
  (\<forall>y\<in>S i. l(g y)=y) \<and> (\<forall>y\<in>S j. g(l y)=y))"
lemma mutual_iff_iso: "(refines i j \<and> refines j i) = iso i j"
  unfolding iso_def refines_def using mutual_inverse by blast

definition E where "E = {(i,j). refines i j \<and> refines j i}"
lemma E_equiv: "equiv UNIV E"
  unfolding equiv_def refl_on_def sym_def trans_def E_def
  using refinement_refl refinement_trans by blast
lemma refines_desc: "ord_desc UNIV E refines"
  unfolding ord_desc_def E_def using refinement_trans by blast
lemma refines_sep: "ord_sep UNIV E refines"
  unfolding ord_sep_def E_def by simp
lemma refines_pre: "pre_on UNIV refines"
  unfolding pre_on_def using refinement_refl refinement_trans by blast
lemma isomorphism_class_partial_order: "part_on (UNIV//E) (qrel UNIV E refines)"
  by (rule quotient_partial_order[OF E_equiv refines_desc refines_sep refines_pre])
lemma class_refinement_relation: "qrel UNIV E refines (E``{i}) (E``{j}) = refines i j"
  by (rule quotient_on_representatives[OF E_equiv refines_desc]) simp_all
lemma canonical_class_greatest:
  assumes factors: "\<And>i. \<exists>f g. arrow k i f g" and X: "X\<in>UNIV//E"
  shows "qrel UNIV E refines X (E``{k})"
proof -
  obtain i where i: "X=E``{i}" using X by (elim quotientE) auto
  have "refines i k" using factors[of i] unfolding refines_def by simp
  then show ?thesis by (simp only: i class_refinement_relation)
qed
end

lemma empty_carrier_inverse_control:
 "(\<forall>x\<in>{}. h(f x)=x) \<and> bij_betw f {} {}"
  by (simp add: bij_betw_def)
lemma missing_projection_surjectivity_control:
 "(\<forall>x::unit. (\<lambda>_::bool. False)((\<lambda>_::unit. False)x)=False) \<and>
  \<not>(\<forall>y::bool. (\<lambda>_::bool. False)y=y)"
  by auto

ML \<open>
val roots = @{thms presentations.arrow_id presentations.arrow_comp
  presentations.refinement_refl presentations.refinement_trans presentations.mutual_inverse
  presentations.mutual_bijections presentations.mutual_order_iso presentations.mutual_trajectory_iso
  presentations.mutual_iff_iso presentations.E_equiv presentations.refines_desc
  presentations.isomorphism_class_partial_order presentations.class_refinement_relation
  presentations.canonical_class_greatest empty_carrier_inverse_control missing_projection_surjectivity_control};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
