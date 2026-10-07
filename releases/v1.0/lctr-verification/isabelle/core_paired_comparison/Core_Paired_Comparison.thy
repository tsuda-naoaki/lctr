theory Core_Paired_Comparison
 imports "LCTR_Core_Source_Loops.Core_Source_Loops"
begin

locale paired_comparison =
 C: native_comparison DC fC trC admC +
 D: native_comparison DD fD trD admD
 for DC :: "'u \<Rightarrow> 'sc set" and fC :: "'u \<Rightarrow> 'sc \<Rightarrow> 'vc"
 and trC :: "'u \<Rightarrow> 'u \<Rightarrow> 'vc \<Rightarrow> 'vc \<Rightarrow> bool"
 and admC :: "'u \<Rightarrow> 'u \<Rightarrow> bool"
 and DD :: "'u \<Rightarrow> 'sd set" and fD :: "'u \<Rightarrow> 'sd \<Rightarrow> 'vd"
 and trD :: "'u \<Rightarrow> 'u \<Rightarrow> 'vd \<Rightarrow> 'vd \<Rightarrow> bool"
 and admD :: "'u \<Rightarrow> 'u \<Rightarrow> bool"
begin

interpretation CW: typed_actions "regions DC fC" "{e. admitted admC e}" initial terminal inverted "cmp_act DC fC trC"
proof
  fix e assume "e\<in>{e. admitted admC e}"
  then show "inverted e\<in>{e. admitted admC e}" by (cases e) auto
next
  fix e assume "e\<in>{e. admitted admC e}"
  show "initial (inverted e)=terminal e" by (cases e) auto
next
  fix e assume "e\<in>{e. admitted admC e}"
  show "terminal (inverted e)=initial e" by (cases e) auto
next
  fix e assume "e\<in>{e. admitted admC e}"
  show "inverted (inverted e)=e" by (cases e) auto
next
  fix e p q assume "e\<in>{e. admitted admC e}" and pq: "cmp_act DC fC trC e p q"
  show "p\<in>regions DC fC (initial e) \<and> q\<in>regions DC fC (terminal e)" by (rule C.atom_type[OF pq])
next
  fix e p q r assume "e\<in>{e. admitted admC e}" and "cmp_act DC fC trC e p q" and "cmp_act DC fC trC e p r"
  then show "q=r" using C.atom_functional by auto
next
  fix e p q assume "e\<in>{e. admitted admC e}"
  show "cmp_act DC fC trC (inverted e) q p = cmp_act DC fC trC e p q" by (rule C.atom_inverse)
qed
interpretation DW: typed_actions "regions DD fD" "{e. admitted admD e}" initial terminal inverted "cmp_act DD fD trD"
proof
  fix e assume "e\<in>{e. admitted admD e}"
  then show "inverted e\<in>{e. admitted admD e}" by (cases e) auto
next
  fix e assume "e\<in>{e. admitted admD e}"
  show "initial (inverted e)=terminal e" by (cases e) auto
next
  fix e assume "e\<in>{e. admitted admD e}"
  show "terminal (inverted e)=initial e" by (cases e) auto
next
  fix e assume "e\<in>{e. admitted admD e}"
  show "inverted (inverted e)=e" by (cases e) auto
next
  fix e p q assume "e\<in>{e. admitted admD e}" and pq: "cmp_act DD fD trD e p q"
  show "p\<in>regions DD fD (initial e) \<and> q\<in>regions DD fD (terminal e)" by (rule D.atom_type[OF pq])
next
  fix e p q r assume "e\<in>{e. admitted admD e}" and "cmp_act DD fD trD e p q" and "cmp_act DD fD trD e p r"
  then show "q=r" using D.atom_functional by auto
next
  fix e p q assume "e\<in>{e. admitted admD e}"
  show "cmp_act DD fD trD (inverted e) q p = cmp_act DD fD trD e p q" by (rule D.atom_inverse)
qed

abbreviation c_orbit where
 "c_orbit \<equiv> typed_actions.orbit (regions DC fC) {e. admitted admC e} initial terminal (cmp_act DC fC trC)"
abbreviation d_orbit where
 "d_orbit \<equiv> typed_actions.orbit (regions DD fD) {e. admitted admD e} initial terminal (cmp_act DD fD trD)"
abbreviation ceq where "ceq \<equiv> {(a,b). c_orbit a b}"
abbreviation deq where "deq \<equiv> {(a,b). d_orbit a b}"

definition synchronized where
 "synchronized = {p. fst(snd p)\<in>fC (fst p) ` DC (fst p) \<and> snd(snd p)\<in>fD (fst p) ` DD (fst p)}"
definition projection where
 "projection p = (ceq``{(fst p,fst(snd p))}, deq``{(fst p,snd(snd p))})"
definition same where
 "same p q = (c_orbit (fst p,fst(snd p)) (fst q,fst(snd q)) \<and>
  d_orbit (fst p,snd(snd p)) (fst q,snd(snd q)))"

lemma projection_kernel:
 assumes p: "p\<in>synchronized" and q: "q\<in>synchronized"
 shows "projection p = projection q \<longleftrightarrow> same p q"
proof -
 have c:
  "(ceq``{(fst p,fst(snd p))}=ceq``{(fst q,fst(snd q))}) =
   c_orbit (fst p,fst(snd p)) (fst q,fst(snd q))"
  using eq_equiv_class_iff[OF C.comparison_equivalence] p q
  unfolding synchronized_def CW.carrier_def regions_def by auto
 have d:
  "(deq``{(fst p,snd(snd p))}=deq``{(fst q,snd(snd q))}) =
   d_orbit (fst p,snd(snd p)) (fst q,snd(snd q))"
  using eq_equiv_class_iff[OF D.comparison_equivalence] p q
  unfolding synchronized_def DW.carrier_def regions_def by auto
 show ?thesis unfolding projection_def same_def using c d by simp
qed

theorem paired_equivalence:
 "equiv synchronized {(p,q). p\<in>synchronized \<and> q\<in>synchronized \<and> same p q}"
 unfolding equiv_def refl_on_def sym_def trans_def
 by (auto simp: projection_kernel[symmetric])

definition pair_relation where
 "pair_relation localRel = {p\<in>synchronized. snd p\<in>localRel(fst p)}"
definition saturated where
 "saturated localRel = (\<forall>p\<in>synchronized. \<forall>q\<in>synchronized.
   same p q \<longrightarrow> (snd p\<in>localRel(fst p) \<longleftrightarrow> snd q\<in>localRel(fst q)))"
definition canonical_relation where
 "canonical_relation localRel = projection ` pair_relation localRel"

theorem canonical_relation_typed:
 "canonical_relation localRel \<subseteq> projection ` synchronized"
 unfolding canonical_relation_def pair_relation_def by blast

theorem canonical_relation_pullback:
 assumes sat: "saturated localRel" and p: "p\<in>synchronized"
 shows "projection p\<in>canonical_relation localRel \<longleftrightarrow> snd p\<in>localRel(fst p)"
proof
 assume "projection p\<in>canonical_relation localRel"
 then obtain q where q: "q\<in>synchronized" and qr: "snd q\<in>localRel(fst q)"
  and eq: "projection q=projection p" unfolding canonical_relation_def pair_relation_def by auto
 have "same q p" by (rule iffD1[OF projection_kernel[OF q p] eq])
 then show "snd p\<in>localRel(fst p)" using sat p q qr unfolding saturated_def by blast
next
 assume "snd p\<in>localRel(fst p)"
 then show "projection p\<in>canonical_relation localRel" using p unfolding canonical_relation_def pair_relation_def by blast
qed

theorem source_relation_pullback:
 assumes sat: "saturated localRel" and p: "p\<in>synchronized"
 and compatible: "\<And>u c d. c\<in>fC u ` DC u \<Longrightarrow> d\<in>fD u ` DD u \<Longrightarrow>
   ((c,d)\<in>localRel u \<longleftrightarrow> (recovery DC fC u c,recovery DD fD u d)\<in>sourceRel)"
 shows "projection p\<in>canonical_relation localRel \<longleftrightarrow>
  (recovery DC fC (fst p) (fst(snd p)),recovery DD fD (fst p) (snd(snd p)))\<in>sourceRel"
 using canonical_relation_pullback[OF sat p] compatible[where u="fst p" and c="fst(snd p)" and d="snd(snd p)"] p
 unfolding synchronized_def by auto

theorem canonical_relation_least:
 "(\<And>p. p\<in>synchronized \<Longrightarrow> snd p\<in>localRel(fst p) \<Longrightarrow> projection p\<in>target)
  \<Longrightarrow> canonical_relation localRel\<subseteq>target"
 unfolding canonical_relation_def pair_relation_def by blast

theorem canonical_relation_unique_minimal:
 "\<exists>!target. (\<forall>p\<in>synchronized. snd p\<in>localRel(fst p) \<longrightarrow> projection p\<in>target) \<and>
   (\<forall>other. (\<forall>p\<in>synchronized. snd p\<in>localRel(fst p) \<longrightarrow> projection p\<in>other) \<longrightarrow> target\<subseteq>other)"
proof -
 have contains: "\<forall>p\<in>synchronized. snd p\<in>localRel(fst p) \<longrightarrow> projection p\<in>canonical_relation localRel"
  unfolding canonical_relation_def pair_relation_def by blast
 have least: "\<And>other. (\<forall>p\<in>synchronized. snd p\<in>localRel(fst p) \<longrightarrow> projection p\<in>other)
  \<Longrightarrow> canonical_relation localRel\<subseteq>other" using canonical_relation_least by blast
 show ?thesis
 proof (rule ex1I[where a="canonical_relation localRel"])
  show "(\<forall>p\<in>synchronized. snd p\<in>localRel(fst p) \<longrightarrow> projection p\<in>canonical_relation localRel) \<and>
   (\<forall>other. (\<forall>p\<in>synchronized. snd p\<in>localRel(fst p) \<longrightarrow> projection p\<in>other) \<longrightarrow> canonical_relation localRel\<subseteq>other)"
   using contains least by blast
 next
  fix target
  assume h: "(\<forall>p\<in>synchronized. snd p\<in>localRel(fst p) \<longrightarrow> projection p\<in>target) \<and>
   (\<forall>other. (\<forall>p\<in>synchronized. snd p\<in>localRel(fst p) \<longrightarrow> projection p\<in>other) \<longrightarrow> target\<subseteq>other)"
  have l: "canonical_relation localRel\<subseteq>target" using least h by blast
  have r: "target\<subseteq>canonical_relation localRel" using contains h by blast
  show "target=canonical_relation localRel" by (rule antisym[OF r l])
 qed
qed

theorem saturation_necessary_for_pullback:
 assumes pull: "\<And>p. p\<in>synchronized \<Longrightarrow>
   (projection p\<in>target \<longleftrightarrow> snd p\<in>localRel(fst p))"
 shows "saturated localRel"
proof (unfold saturated_def, intro ballI impI)
 fix p q
 assume p: "p\<in>synchronized" and q: "q\<in>synchronized" and pq: "same p q"
 have eq: "projection p=projection q" by (rule iffD2[OF projection_kernel[OF p q] pq])
 have left: "(projection p\<in>target)=(snd p\<in>localRel(fst p))" by (rule pull[OF p])
 have right: "(projection q\<in>target)=(snd q\<in>localRel(fst q))" by (rule pull[OF q])
 show "snd p\<in>localRel(fst p) \<longleftrightarrow> snd q\<in>localRel(fst q)"
  by (simp only: left[symmetric] right[symmetric] eq)
qed

theorem local_pair_projection_injective:
 assumes cm: "C.irreducible_mixed_identity" and dm: "D.irreducible_mixed_identity"
 and cp: "C.pure_loop_identity" and dp: "D.pure_loop_identity"
 shows "inj_on (\<lambda>a. projection(u,a)) ((fC u ` DC u)\<times>(fD u ` DD u))"
proof (rule inj_onI)
 fix a b
 assume a: "a\<in>(fC u ` DC u)\<times>(fD u ` DD u)"
 and b: "b\<in>(fC u ` DC u)\<times>(fD u ` DD u)" and eq: "projection(u,a)=projection(u,b)"
 have ci: "inj_on (\<lambda>p. ceq``{p}) (regions DC fC u)"
  using C.gluing_iff_local_injectivity[OF cm] cp by blast
 have di: "inj_on (\<lambda>p. deq``{p}) (regions DD fD u)"
  using D.gluing_iff_local_injectivity[OF dm] dp by blast
 have ca: "(u,fst a)\<in>regions DC fC u" and cb: "(u,fst b)\<in>regions DC fC u"
 and da: "(u,snd a)\<in>regions DD fD u" and db: "(u,snd b)\<in>regions DD fD u"
  using a b unfolding regions_def by auto
 have ce: "ceq``{(u,fst a)}=ceq``{(u,fst b)}" and de: "deq``{(u,snd a)}=deq``{(u,snd b)}"
  using eq unfolding projection_def by auto
 have c: "(u,fst a)=(u,fst b)" by (rule inj_onD[OF ci ce ca cb])
 have d: "(u,snd a)=(u,snd b)" by (rule inj_onD[OF di de da db])
 show "a=b" using c d by (cases a; cases b) auto
qed

theorem empty_relation: "canonical_relation (\<lambda>_. {}) = {}"
 unfolding canonical_relation_def pair_relation_def by simp

end

ML \<open>
val roots = @{thms paired_comparison.paired_equivalence paired_comparison.projection_kernel
 paired_comparison.canonical_relation_typed paired_comparison.canonical_relation_pullback
 paired_comparison.source_relation_pullback paired_comparison.canonical_relation_least
 paired_comparison.canonical_relation_unique_minimal paired_comparison.saturation_necessary_for_pullback
 paired_comparison.local_pair_projection_injective paired_comparison.empty_relation};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
