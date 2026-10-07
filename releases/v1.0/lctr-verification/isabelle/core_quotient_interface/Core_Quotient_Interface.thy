theory Core_Quotient_Interface
 imports "LCTR_Core_Source_Loops.Core_Source_Loops"
begin
locale class_interface =
 fixes A :: "'a set" and E :: "('a\<times>'a) set"
 assumes equivalence: "equiv A E"
begin
definition class_projection where "class_projection a=Image E {a}"
definition class_quotient where "class_quotient=image class_projection A"
definition class_to_native where
 "class_to_native c=Image E {SOME a. a\<in>A \<and> class_projection a=c}"

theorem class_kernel:
 "a\<in>A \<Longrightarrow> b\<in>A \<Longrightarrow> (Image E {a}=Image E {b} \<longleftrightarrow> (a,b)\<in>E)"
 by (rule eq_equiv_class_iff[OF equivalence])
theorem class_projection_kernel:
 "a\<in>A \<Longrightarrow> b\<in>A \<Longrightarrow> (class_projection a=class_projection b \<longleftrightarrow> (a,b)\<in>E)"
 unfolding class_projection_def by (rule class_kernel)
theorem class_projection_surjective:
 "image class_projection A=class_quotient"
 by (simp add: class_quotient_def)

lemma chosen_recovers:
 assumes c: "c\<in>class_quotient"
 shows "class_to_native c=c"
proof -
 have ex: "\<exists>a. a\<in>A \<and> class_projection a=c"
  using c unfolding class_quotient_def by blast
 have pick: "(SOME a. a\<in>A \<and> class_projection a=c)\<in>A \<and>
   class_projection(SOME a. a\<in>A \<and> class_projection a=c)=c"
  by (rule someI_ex[OF ex])
 show ?thesis using pick unfolding class_to_native_def class_projection_def by simp
qed

theorem class_native_commutes:
 "a\<in>A \<Longrightarrow> class_to_native(class_projection a)=Image E {a}"
 using chosen_recovers by (simp add: class_quotient_def class_projection_def)

lemma quotient_agrees: "class_quotient=A//E"
 by (auto simp: class_quotient_def class_projection_def quotient_def)

theorem class_native_bijective:
 "bij_betw class_to_native class_quotient (A//E)"
 using chosen_recovers quotient_agrees
 by (auto simp: bij_betw_def inj_on_def)

theorem class_native_unique:
 assumes f: "\<And>a. a\<in>A \<Longrightarrow> f(class_projection a)=Image E {a}"
 shows "\<forall>c\<in>class_quotient. f c=class_to_native c"
proof (intro ballI)
 fix c assume "c\<in>class_quotient"
 then obtain a where a: "a\<in>A" and c: "c=class_projection a"
  unfolding class_quotient_def by blast
 show "f c=class_to_native c" unfolding c using f[OF a] class_native_commutes[OF a] by simp
qed
end

definition saturated_on where
 "saturated_on A E P=(\<forall>a\<in>A. \<forall>b\<in>A. (a,b)\<in>E \<longrightarrow> (a\<in>P \<longleftrightarrow> b\<in>P))"

theorem image_pullback:
 assumes kernel: "\<And>a b. a\<in>A \<Longrightarrow> b\<in>A \<Longrightarrow> (p a=p b \<longleftrightarrow> (a,b)\<in>E)"
 and subset: "P\<subseteq>A" and sat: "saturated_on A E P" and a: "a\<in>A"
 shows "p a\<in>image p P \<longleftrightarrow> a\<in>P"
proof
 assume "p a\<in>image p P"
 then obtain b where b: "b\<in>P" and eq: "p a=p b" by blast
 have ba: "b\<in>A" using b subset by blast
 have ab: "(a,b)\<in>E" by (rule iffD1[OF kernel[OF a ba] eq])
 show "a\<in>P" using sat a ba ab b unfolding saturated_on_def by blast
next
 assume "a\<in>P"
 then show "p a\<in>image p P" by blast
qed
theorem image_least:
 "(\<And>a. a\<in>P \<Longrightarrow> p a\<in>T) \<Longrightarrow> image p P\<subseteq>T"
 by blast
theorem image_unique_least:
 "\<exists>!T. (\<forall>a\<in>P. p a\<in>T) \<and> (\<forall>R. (\<forall>a\<in>P. p a\<in>R) \<longrightarrow> T\<subseteq>R)"
proof (rule ex1I[where a="image p P"])
 show "(\<forall>a\<in>P. p a\<in>image p P) \<and>
  (\<forall>R. (\<forall>a\<in>P. p a\<in>R) \<longrightarrow> image p P\<subseteq>R)" by blast
next
 fix T assume h: "(\<forall>a\<in>P. p a\<in>T) \<and> (\<forall>R. (\<forall>a\<in>P. p a\<in>R) \<longrightarrow> T\<subseteq>R)"
 have l: "T\<subseteq>image p P" using h by blast
 have r: "image p P\<subseteq>T" using h by blast
 show "T=image p P" by (rule antisym[OF l r])
qed
theorem exact_pullback_requires_saturation:
 assumes kernel: "\<And>a b. a\<in>A \<Longrightarrow> b\<in>A \<Longrightarrow> (p a=p b \<longleftrightarrow> (a,b)\<in>E)"
 and pull: "\<And>a. a\<in>A \<Longrightarrow> (p a\<in>T \<longleftrightarrow> a\<in>P)"
 shows "saturated_on A E P"
proof (unfold saturated_on_def, intro ballI impI)
 fix a b assume a: "a\<in>A" and b: "b\<in>A" and ab: "(a,b)\<in>E"
 have eq: "p a=p b" by (rule iffD2[OF kernel[OF a b] ab])
 show "a\<in>P \<longleftrightarrow> b\<in>P"
  by (simp only: pull[OF a, symmetric] pull[OF b, symmetric] eq)
qed
theorem empty_class_quotient:
 "image (\<lambda>a. Image E {a}) {} = {} \<and> {}//E={}"
 by (simp add: quotient_def)

context native_comparison
begin
interpretation W: typed_actions "regions D f" "{e. admitted adm e}" initial terminal inverted "cmp_act D f tr"
proof
  fix e assume "e\<in>{e. admitted adm e}"
  then show "inverted e\<in>{e. admitted adm e}" by (cases e) auto
next
  fix e assume "e\<in>{e. admitted adm e}"
  show "initial (inverted e)=terminal e" by (cases e) auto
next
  fix e assume "e\<in>{e. admitted adm e}"
  show "terminal (inverted e)=initial e" by (cases e) auto
next
  fix e assume "e\<in>{e. admitted adm e}"
  show "inverted (inverted e)=e" by (cases e) auto
next
  fix e p q assume "e\<in>{e. admitted adm e}" and pq: "cmp_act D f tr e p q"
  show "p\<in>regions D f (initial e) \<and> q\<in>regions D f (terminal e)" by (rule atom_type[OF pq])
next
  fix e p q r assume "e\<in>{e. admitted adm e}" and "cmp_act D f tr e p q" and "cmp_act D f tr e p r"
  then show "q=r" using atom_functional by auto
next
  fix e p q assume "e\<in>{e. admitted adm e}"
  show "cmp_act D f tr (inverted e) q p = cmp_act D f tr e p q" by (rule atom_inverse)
qed

theorem native_comparison_projection:
 "image (\<lambda>a. Image {(x,y). W.orbit x y} {a}) W.carrier = W.carrier//{(x,y). W.orbit x y} \<and>
  (\<forall>a\<in>W.carrier. \<forall>b\<in>W.carrier.
   (Image {(x,y). W.orbit x y} {a}=Image {(x,y). W.orbit x y} {b}) \<longleftrightarrow> W.orbit a b)"
 using eq_equiv_class_iff[OF comparison_equivalence] by (auto simp: quotient_def)
end
ML \<open>
val roots = @{thms class_interface.class_kernel class_interface.class_projection_kernel
 class_interface.class_projection_surjective class_interface.class_native_commutes
 class_interface.class_native_bijective class_interface.class_native_unique
 image_pullback image_least image_unique_least exact_pullback_requires_saturation
 native_comparison.native_comparison_projection empty_class_quotient};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
