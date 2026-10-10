theory Core_Order_Atlas
 imports LCTR_Core_Universal_Factorization.Core_Universal_Factorization
begin

locale order_domain =
 fixes A :: "'a set" and r :: "'a\<Rightarrow>'a\<Rightarrow>bool"
 assumes strict: "strict_on A r" and inc: "inc_trans_on A r"
begin
theorem projection_onto: "image(qproj A r) A=QuSet A r" by (rule qproj_image)
theorem projection_kernel:
 "x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> (qproj A r x=qproj A r y \<longleftrightarrow> \<not>r x y \<and> \<not>r y x)"
 using qproj_class_iff[OF strict inc] by (simp add: inc_on_def)
theorem projection_order:
 "x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> (qlt A r (qproj A r x)(qproj A r y) \<longleftrightarrow> r x y)"
 by (rule qproj_order_iff[OF strict inc])
theorem quotient_strict_linear:
 "Order_Embedding_Isabelle.strict_linear_on (QuSet A r) (qlt A r)"
 using transitive_incomparability_quotient[OF strict inc] by blast

theorem composite_chart_contract:
 assumes onto: "image receive X=A"
 shows "image(qproj A r \<circ> receive) X=QuSet A r \<and>
  (\<forall>x\<in>X. \<forall>y\<in>X. qproj A r (receive x)=qproj A r (receive y)
      \<longleftrightarrow> \<not>r(receive x)(receive y) \<and> \<not>r(receive y)(receive x)) \<and>
  (\<forall>x\<in>X. \<forall>y\<in>X. qlt A r (qproj A r (receive x))(qproj A r (receive y))
      \<longleftrightarrow> r(receive x)(receive y))"
proof -
 have member: "\<And>x. x\<in>X \<Longrightarrow> receive x\<in>A" using onto by blast
 show ?thesis using projection_kernel[OF member member] projection_order[OF member member]
  projection_onto onto by (auto simp: image_comp)
qed

theorem native_order_factor:
 assumes kernel: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> (f x=f y \<longleftrightarrow> \<not>r x y \<and> \<not>r y x)"
 and ord: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> (lt(f x)(f y) \<longleftrightarrow> r x y)"
 shows "\<exists>F. bij_betw F (QuSet A r) (image f A) \<and>
  (\<forall>x\<in>A. F(qproj A r x)=f x) \<and>
  (\<forall>u\<in>QuSet A r. \<forall>v\<in>QuSet A r. lt(F u)(F v) \<longleftrightarrow> qlt A r u v) \<and>
  (\<forall>G. (\<forall>x\<in>A. G(qproj A r x)=f x) \<longrightarrow> (\<forall>q\<in>QuSet A r. G q=F q))"
proof -
 interpret F: order_quotient_factor A r f
  by standard (fact strict, fact inc, simp add: kernel inc_on_def)
 show ?thesis by (rule F.quotient_factor_exists_unique[OF ord])
qed
end

definition order_inclusion where
 "order_inclusion A B r=factor_choice A (qproj A r) (qproj B r)"
definition overlap_change where
 "overlap_change A B r=factor_choice (A\<inter>B) (qproj A r) (qproj B r)"

locale order_pair = A: order_domain A r + B: order_domain B r
 for A B :: "'a set" and r
begin
lemma nested_kernel:
 assumes sub: "A\<subseteq>B" and x: "x\<in>A" and y: "y\<in>A"
 shows "qproj A r x=qproj A r y \<longleftrightarrow> qproj B r x=qproj B r y"
proof -
 have xb: "x\<in>B" and yb: "y\<in>B" using sub x y by blast+
 show ?thesis using A.projection_kernel[OF x y] B.projection_kernel[OF xb yb] by simp
qed

theorem inclusion_commutes:
 assumes sub: "A\<subseteq>B" and x: "x\<in>A"
 shows "order_inclusion A B r (qproj A r x)=qproj B r x"
 unfolding order_inclusion_def
 by (rule factor_agrees_on[where A=A]) (use nested_kernel[OF sub] x in blast)+

lemma inclusion_maps:
 assumes sub: "A\<subseteq>B" and q: "q\<in>QuSet A r"
 shows "order_inclusion A B r q\<in>QuSet B r"
proof -
 obtain x where x: "x\<in>A" and qx: "q=qproj A r x" using q unfolding QuSet_def by blast
 have xb: "x\<in>B" using sub x by blast
 show ?thesis unfolding qx using inclusion_commutes[OF sub x] xb
  by (auto simp: QuSet_def)
qed

theorem inclusion_injective:
 assumes sub: "A\<subseteq>B"
 shows "inj_on (order_inclusion A B r) (QuSet A r)"
proof (rule inj_onI)
 fix p q assume p: "p\<in>QuSet A r" and q: "q\<in>QuSet A r"
 and eq: "order_inclusion A B r p=order_inclusion A B r q"
 obtain x where x: "x\<in>A" "p=qproj A r x" using p unfolding QuSet_def by blast
 obtain y where y: "y\<in>A" "q=qproj A r y" using q unfolding QuSet_def by blast
 have b: "qproj B r x=qproj B r y" using eq x y inclusion_commutes[OF sub] by simp
 show "p=q" using nested_kernel[OF sub x(1) y(1)] b x y by simp
qed

theorem inclusion_order:
 assumes sub: "A\<subseteq>B" and p: "p\<in>QuSet A r" and q: "q\<in>QuSet A r"
 shows "qlt B r (order_inclusion A B r p)(order_inclusion A B r q) \<longleftrightarrow> qlt A r p q"
proof -
 obtain x where x: "x\<in>A" "p=qproj A r x" using p unfolding QuSet_def by blast
 obtain y where y: "y\<in>A" "q=qproj A r y" using q unfolding QuSet_def by blast
 have xb: "x\<in>B" and yb: "y\<in>B" using sub x y by blast+
 show ?thesis using x y A.projection_order[OF x(1) y(1)] B.projection_order[OF xb yb]
  inclusion_commutes[OF sub] by simp
qed

theorem inclusion_unique:
 assumes sub: "A\<subseteq>B" and f: "\<And>x. x\<in>A \<Longrightarrow> F(qproj A r x)=qproj B r x"
 shows "\<forall>q\<in>QuSet A r. F q=order_inclusion A B r q"
 using f inclusion_commutes[OF sub] unfolding QuSet_def by fastforce

theorem overlap_kernel:
 assumes x: "x\<in>A\<inter>B" and y: "y\<in>A\<inter>B"
 shows "qproj A r x=qproj A r y \<longleftrightarrow> qproj B r x=qproj B r y"
 using A.projection_kernel[of x y] B.projection_kernel[of x y] x y by auto

theorem overlap_change_commutes:
 assumes x: "x\<in>A\<inter>B"
 shows "overlap_change A B r (qproj A r x)=qproj B r x"
 unfolding overlap_change_def
 by (rule factor_agrees_on) (use overlap_kernel x in blast)+

lemma overlap_bijective:
 "bij_betw (overlap_change A B r) (image(qproj A r)(A\<inter>B)) (image(qproj B r)(A\<inter>B))"
proof -
 interpret K: equal_kernel_factor "A\<inter>B" "qproj A r" "qproj B r"
  by standard (rule overlap_kernel)
 show ?thesis unfolding overlap_change_def by (rule K.bijective)
qed

theorem overlap_order:
 assumes p: "p\<in>image(qproj A r)(A\<inter>B)" and q: "q\<in>image(qproj A r)(A\<inter>B)"
 shows "qlt B r (overlap_change A B r p)(overlap_change A B r q) \<longleftrightarrow> qlt A r p q"
proof -
 obtain x where x: "x\<in>A\<inter>B" "p=qproj A r x" using p by blast
 obtain y where y: "y\<in>A\<inter>B" "q=qproj A r y" using q by blast
 have xa: "x\<in>A" and xb: "x\<in>B" and ya: "y\<in>A" and yb: "y\<in>B" using x y by auto
 show ?thesis using x y A.projection_order[OF xa ya] B.projection_order[OF xb yb]
  overlap_change_commutes by simp
qed

lemma reverse_change_commutes:
 assumes x: "x\<in>A\<inter>B"
 shows "overlap_change B A r (qproj B r x)=qproj A r x"
proof -
 interpret BA: order_pair B A r by unfold_locales
 have "x\<in>B\<inter>A" using x by auto
 then show ?thesis by (rule BA.overlap_change_commutes)
qed

theorem inverse_change_commutes:
 assumes x: "x\<in>A\<inter>B"
 shows "inv_into (image(qproj A r)(A\<inter>B)) (overlap_change A B r) (qproj B r x)=qproj A r x"
proof -
 have inj: "inj_on (overlap_change A B r) (image(qproj A r)(A\<inter>B))"
  using overlap_bijective by (simp add: bij_betw_def)
 have mem: "qproj A r x\<in>image(qproj A r)(A\<inter>B)" using x by blast
 have "inv_into (image(qproj A r)(A\<inter>B)) (overlap_change A B r)
   (overlap_change A B r (qproj A r x))=qproj A r x"
  by (rule inv_into_f_f[OF inj mem])
 then show ?thesis by (simp only: overlap_change_commutes[OF x])
qed
end

theorem self_change_identity:
 assumes d: "order_domain A r" and p: "p\<in>QuSet A r"
 shows "overlap_change A A r p=p"
proof -
 interpret D: order_domain A r by (rule d)
 interpret AA: order_pair A A r by unfold_locales
 obtain x where x: "x\<in>A" "p=qproj A r x" using p unfolding QuSet_def by blast
 show ?thesis using AA.overlap_change_commutes[of x] x by simp
qed

locale order_triple = AB: order_pair A B r + BC: order_pair B C r
 for A B C :: "'a set" and r
begin
interpretation AC: order_pair A C r by unfold_locales
theorem inclusion_compose:
 assumes ab: "A\<subseteq>B" and bc: "B\<subseteq>C" and p: "p\<in>QuSet A r"
 shows "order_inclusion B C r (order_inclusion A B r p)=order_inclusion A C r p"
proof -
 obtain x where x: "x\<in>A" "p=qproj A r x" using p unfolding QuSet_def by blast
 have xb: "x\<in>B" using ab x by blast
 have ac: "A\<subseteq>C" using ab bc by blast
 show ?thesis using AB.inclusion_commutes[OF ab x(1)] BC.inclusion_commutes[OF bc xb]
  AC.inclusion_commutes[OF ac x(1)] x by simp
qed

theorem continue_overlap_exact:
 assumes x: "x\<in>A\<inter>B\<inter>C"
 shows "overlap_change A B r (qproj A r x)=qproj B r x \<and>
  overlap_change A B r (qproj A r x)\<in>image(qproj B r)(B\<inter>C)"
proof -
 have ab: "x\<in>A\<inter>B" and bc: "x\<in>B\<inter>C" using x by auto
 have eq: "overlap_change A B r (qproj A r x)=qproj B r x"
  by (rule AB.overlap_change_commutes[OF ab])
 show ?thesis using eq bc by blast
qed

theorem triple_overlap_cocycle:
 assumes x: "x\<in>A\<inter>B\<inter>C"
 shows "overlap_change B C r (overlap_change A B r (qproj A r x))=
  overlap_change A C r (qproj A r x)"
proof -
 have ab: "x\<in>A\<inter>B" and bc: "x\<in>B\<inter>C" and ac: "x\<in>A\<inter>C" using x by auto
 show ?thesis by (simp only: AB.overlap_change_commutes[OF ab]
  BC.overlap_change_commutes[OF bc] AC.overlap_change_commutes[OF ac])
qed
end

ML \<open>
val roots = @{thms order_domain.projection_onto order_domain.projection_kernel
 order_domain.projection_order order_domain.quotient_strict_linear
 order_pair.inclusion_commutes order_pair.inclusion_injective order_pair.inclusion_order
 order_triple.inclusion_compose order_pair.inclusion_unique order_domain.composite_chart_contract
 order_pair.overlap_kernel order_pair.overlap_change_commutes order_pair.overlap_order
 order_domain.native_order_factor order_pair.inverse_change_commutes self_change_identity
 order_triple.continue_overlap_exact order_triple.triple_overlap_cocycle};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
