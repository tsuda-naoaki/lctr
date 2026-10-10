theory Core_Universal_Factorization
 imports LCTR_Core_Representation_Images.Core_Representation_Images
 LCTR_Order_Embedding_Isabelle.Order_Embedding_Isabelle "HOL.Equiv_Relations"
begin

lemma factor_agrees_on:
 assumes k: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> p x=p y \<Longrightarrow> f x=f y"
 and x: "x\<in>A"
 shows "factor_choice A p f (p x)=f x"
proof -
 have "eqker_on A p\<subseteq>eqker_on A f"
  using k unfolding eqker_on_def by auto
 then show ?thesis using x by (rule factor_choice_agrees)
qed

theorem surjective_factor_exists_unique:
 assumes onto: "image p A=Q"
 and k: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> p x=p y \<Longrightarrow> f x=f y"
 shows "\<exists>F. (\<forall>x\<in>A. F(p x)=f x) \<and>
  (\<forall>G. (\<forall>x\<in>A. G(p x)=f x) \<longrightarrow> (\<forall>q\<in>Q. G q=F q))"
proof -
 have incl: "eqker_on A p\<subseteq>eqker_on A f"
  using k unfolding eqker_on_def by auto
 show ?thesis using surjective_equality_kernel_factorization_on[OF incl] onto by simp
qed

theorem precomposition_cancellation:
 assumes onto: "image p A=Q" and same: "\<And>x. x\<in>A \<Longrightarrow> f(p x)=g(p x)"
 shows "\<forall>q\<in>Q. f q=g q"
 using onto same by blast

theorem comparison_factor_unique:
 assumes eqv: "equiv A E"
 and respects: "\<And>x y. (x,y)\<in>E \<Longrightarrow> f x=f y"
 shows "\<exists>F. (\<forall>x\<in>A. F(Image E {x})=f x) \<and>
  (\<forall>G. (\<forall>x\<in>A. G(Image E {x})=f x) \<longrightarrow> (\<forall>q\<in>A//E. G q=F q))"
proof -
 have onto: "image (\<lambda>x. Image E {x}) A=A//E"
  by (auto simp: quotient_def)
 have k: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> Image E {x}=Image E {y} \<Longrightarrow> f x=f y"
  using eq_equiv_class_iff[OF eqv] respects by blast
 show ?thesis by (rule surjective_factor_exists_unique[OF onto k])
qed

definition pair_projection where
 "pair_projection E H z=(Image E {fst z},Image H {snd z})"

theorem comparison_relation_factorization:
 assumes ea: "equiv A E" and eb: "equiv B H"
 and fa: "\<And>x y. (x,y)\<in>E \<Longrightarrow> f x=f y"
 and fb: "\<And>x y. (x,y)\<in>H \<Longrightarrow> g x=g y"
 and pt: "P\<subseteq>A\<times>B" and rt: "R\<subseteq>P"
 and sat: "\<And>x y. x\<in>P \<Longrightarrow> y\<in>P \<Longrightarrow>
  (fst x,fst y)\<in>E \<Longrightarrow> (snd x,snd y)\<in>H \<Longrightarrow> (x\<in>R \<longleftrightarrow> y\<in>R)"
 and compat: "\<And>x. x\<in>P \<Longrightarrow> ((f(fst x),g(snd x))\<in>T \<longleftrightarrow> x\<in>R)"
 and x: "x\<in>P"
 shows "(factor_choice A (\<lambda>a. Image E {a}) f (Image E {fst x}),
         factor_choice B (\<lambda>b. Image H {b}) g (Image H {snd x}))\<in>T
   \<longleftrightarrow> pair_projection E H x\<in>image (pair_projection E H) R"
proof -
 have xa: "fst x\<in>A" and xb: "snd x\<in>B" using pt x by auto
 have ka: "\<And>a b. a\<in>A \<Longrightarrow> b\<in>A \<Longrightarrow> Image E {a}=Image E {b} \<Longrightarrow> f a=f b"
  using eq_equiv_class_iff[OF ea] fa by blast
 have kb: "\<And>a b. a\<in>B \<Longrightarrow> b\<in>B \<Longrightarrow> Image H {a}=Image H {b} \<Longrightarrow> g a=g b"
  using eq_equiv_class_iff[OF eb] fb by blast
 have aa: "factor_choice A (\<lambda>a. Image E {a}) f (Image E {fst x})=f(fst x)"
  by (rule factor_agrees_on[OF ka xa])
 have bb: "factor_choice B (\<lambda>b. Image H {b}) g (Image H {snd x})=g(snd x)"
  by (rule factor_agrees_on[OF kb xb])
 have pull: "pair_projection E H x\<in>image (pair_projection E H) R \<longleftrightarrow> x\<in>R"
 proof
  assume "pair_projection E H x\<in>image (pair_projection E H) R"
  then obtain y where y: "y\<in>R" and same: "pair_projection E H x=pair_projection E H y"
   by (rule imageE)
  have yp: "y\<in>P" using rt y by blast
  have ya: "fst y\<in>A" and yb: "snd y\<in>B" using pt yp by auto
  have ex: "(fst y,fst x)\<in>E"
   using same eq_equiv_class_iff[OF ea ya xa] unfolding pair_projection_def by auto
  have hx: "(snd y,snd x)\<in>H"
   using same eq_equiv_class_iff[OF eb yb xb] unfolding pair_projection_def by auto
  show "x\<in>R" using sat[OF yp x ex hx] y by blast
 next
  assume "x\<in>R" then show "pair_projection E H x\<in>image (pair_projection E H) R" by blast
 qed
 show ?thesis using aa bb compat[OF x] pull by simp
qed

locale equal_kernel_factor =
 fixes A :: "'a set" and p :: "'a\<Rightarrow>'b" and f :: "'a\<Rightarrow>'c"
 assumes kernel: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> (p x=p y \<longleftrightarrow> f x=f y)"
begin
abbreviation fac where "fac \<equiv> factor_choice A p f"
lemma commute: "x\<in>A \<Longrightarrow> fac(p x)=f x"
 by (rule factor_agrees_on) (use kernel in blast)
lemma bijective: "bij_betw fac (image p A) (image f A)"
proof -
 have range: "image fac (image p A)=image f A" using commute by force
 have injective: "inj_on fac (image p A)"
 proof (rule inj_onI)
  fix u v assume "u\<in>image p A" "v\<in>image p A" and same: "fac u=fac v"
  then obtain x y where x: "x\<in>A" "u=p x" and y: "y\<in>A" "v=p y" by blast
  have "f x=f y" using same x y commute by simp
  then show "u=v" using kernel[OF x(1) y(1)] x y by simp
 qed
 show ?thesis using range injective by (simp add: bij_betw_def)
qed
lemma unique:
 assumes g: "\<And>x. x\<in>A \<Longrightarrow> G(p x)=f x"
 shows "\<forall>q\<in>image p A. G q=fac q"
 using commute g by fastforce
end

locale order_quotient_factor =
 fixes A :: "'a set" and r :: "'a\<Rightarrow>'a\<Rightarrow>bool" and f :: "'a\<Rightarrow>'b"
 assumes strict: "strict_on A r" and inc: "inc_trans_on A r"
 and kernel: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> (f x=f y \<longleftrightarrow> inc_on A r x y)"
begin
sublocale F: equal_kernel_factor A "qproj A r" f
 by standard (use qproj_class_iff[OF strict inc] kernel in blast)
abbreviation quotient_factor where "quotient_factor \<equiv> factor_choice A (qproj A r) f"
theorem quotient_factor_commutes: "x\<in>A \<Longrightarrow> quotient_factor(qproj A r x)=f x"
 by (rule F.commute)
theorem quotient_factor_strict_order:
 assumes ord: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> (lt(f x)(f y) \<longleftrightarrow> r x y)"
 and u: "u\<in>QuSet A r" and v: "v\<in>QuSet A r"
 shows "lt(quotient_factor u)(quotient_factor v) \<longleftrightarrow> qlt A r u v"
proof -
 obtain x y where x: "x\<in>A" "u=qproj A r x" and y: "y\<in>A" "v=qproj A r y"
  using u v unfolding QuSet_def by blast
 show ?thesis using ord[OF x(1) y(1)] qproj_order_iff[OF strict inc x(1) y(1)]
  x y F.commute by simp
qed
theorem quotient_factor_exists_unique:
 assumes ord: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> (lt(f x)(f y) \<longleftrightarrow> r x y)"
 shows "\<exists>F. bij_betw F (QuSet A r) (image f A) \<and>
  (\<forall>x\<in>A. F(qproj A r x)=f x) \<and>
  (\<forall>u\<in>QuSet A r. \<forall>v\<in>QuSet A r. lt(F u)(F v) \<longleftrightarrow> qlt A r u v) \<and>
  (\<forall>G. (\<forall>x\<in>A. G(qproj A r x)=f x) \<longrightarrow> (\<forall>q\<in>QuSet A r. G q=F q))"
proof (rule exI[where x=quotient_factor], intro conjI)
 show "bij_betw quotient_factor (QuSet A r) (image f A)"
  using F.bijective unfolding QuSet_def .
 show "\<forall>x\<in>A. quotient_factor(qproj A r x)=f x" using F.commute by blast
 show "\<forall>u\<in>QuSet A r. \<forall>v\<in>QuSet A r. lt(quotient_factor u)(quotient_factor v) \<longleftrightarrow> qlt A r u v"
  using quotient_factor_strict_order[OF ord] by blast
 show "\<forall>G. (\<forall>x\<in>A. G(qproj A r x)=f x) \<longrightarrow> (\<forall>q\<in>QuSet A r. G q=quotient_factor q)"
  using F.unique unfolding QuSet_def by blast
qed
end

theorem overlap_factor_naturality:
 assumes native: "\<And>x. x\<in>A \<Longrightarrow> c(p x)=q x"
 and target: "\<And>x. x\<in>A \<Longrightarrow> t(f(p x))=g(q x)"
 shows "\<forall>a\<in>image p A. g(c a)=t(f a)"
 using native target by force

lemmas reparametrization_unique = source_representation_image_uniqueness

ML \<open>
val roots = @{thms surjective_factor_exists_unique precomposition_cancellation
 comparison_factor_unique comparison_relation_factorization
 order_quotient_factor.quotient_factor_commutes order_quotient_factor.quotient_factor_strict_order
 order_quotient_factor.quotient_factor_exists_unique overlap_factor_naturality reparametrization_unique};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
