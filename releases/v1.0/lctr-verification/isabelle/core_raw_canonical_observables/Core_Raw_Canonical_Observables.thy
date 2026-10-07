theory Core_Raw_Canonical_Observables
 imports "LCTR_Core_Observable_Interfaces.Core_Observable_Interfaces"
begin
context raw_observables
begin
definition raw_canonical where "raw_canonical = factor_choice samples projection comparison"
definition raw_range where "raw_range q=val_range(SOME l. l\<in>L \<and> idx l=q)"
lemma range_representative_independence:
 assumes h: descends and q: "q\<in>Q" and l: "l\<in>L" and eq: "idx l=q"
 shows "val_range l=raw_range q"
proof -
 note onto = conjunct1[OF h[unfolded descends_def]]
 note ranges = conjunct1[OF conjunct2[OF h[unfolded descends_def]]]
 have ex: "\<exists>k. k\<in>L \<and> idx k=q" using q onto by blast
 have chosen: "(SOME k. k\<in>L \<and> idx k=q)\<in>L \<and> idx(SOME k. k\<in>L \<and> idx k=q)=q"
   by (rule someI_ex[OF ex])
 show ?thesis unfolding raw_range_def
   using ranges[rule_format, OF l conjunct1[OF chosen]] eq conjunct2[OF chosen] by simp
qed
lemma canonical_representative_value:
 assumes h: descends and i: "i\<in>U" and l: "l\<in>L" and a: "a\<in>A i"
 and qi: "idx l=q" and si: "state i a=s"
 shows "raw_canonical(q,s)=common i l a"
proof -
 have ker: "eqker_on samples projection \<subseteq> eqker_on samples comparison"
 proof (rule subsetI)
  fix p assume p: "p\<in>eqker_on samples projection"
  have x: "fst p\<in>samples" and y: "snd p\<in>samples" and eq: "projection(fst p)=projection(snd p)"
    using p unfolding eqker_on_def by auto
  have same: "comparison(fst p)=comparison(snd p)"
    by (rule raw_comparison_fiber_invariant[OF h x y eq])
  show "p\<in>eqker_on samples comparison" using x y same unfolding eqker_on_def by auto
 qed
 have mem: "(i,l,a)\<in>samples" using i l a unfolding samples_def by simp
 have fac: "factor_choice samples projection comparison (projection(i,l,a))=comparison(i,l,a)"
   by (rule factor_choice_agrees[OF ker mem])
 show ?thesis using fac qi si unfolding raw_canonical_def projection_def comparison_def by simp
qed
lemma canonical_value_typed:
 assumes h: descends and q: "q\<in>Q" and s: "s\<in>State"
 shows "raw_canonical(q,s)\<in>raw_range q"
proof -
 note covers = conjunct1[OF conjunct2[OF conjunct2[OF h[unfolded descends_def]]]]
 obtain i l a where w: "i\<in>U" "l\<in>L" "a\<in>A i" and eq: "idx l=q" "state i a=s"
   using bspec[OF bspec[OF covers q] s] by blast
 have val: "raw_canonical(q,s)=common i l a" by (rule canonical_representative_value[OF h w eq])
 have ran: "val_range l=raw_range q" by (rule range_representative_independence[OF h q w(2) eq(1)])
 show ?thesis using common_value_typed[OF w] val ran by simp
qed
lemma canonical_unique:
 assumes h: descends
 and agrees: "\<And>i l a. i\<in>U \<Longrightarrow> l\<in>L \<Longrightarrow> a\<in>A i \<Longrightarrow> g(idx l,state i a)=common i l a"
 shows "\<forall>p\<in>Q\<times>State. g p=raw_canonical p"
proof (intro ballI)
 fix p assume p: "p\<in>Q\<times>State"
 have ps: "fst p\<in>Q" "snd p\<in>State" using p by auto
 note covers = conjunct1[OF conjunct2[OF conjunct2[OF h[unfolded descends_def]]]]
 obtain i l a where w: "i\<in>U" "l\<in>L" "a\<in>A i" and eq: "idx l=fst p" "state i a=snd p"
   using bspec[OF bspec[OF covers ps(1)] ps(2)] by blast
 show "g p=raw_canonical p" using agrees[OF w] canonical_representative_value[OF h w eq] eq by simp
qed
lemma local_change_compatibility:
 assumes h: descends and hc: change_commutes and i: "i\<in>U" and j: "j\<in>U" and l: "l\<in>L"
 and a: "a\<in>changed_domain i j l"
 shows "raw_canonical(idx l,state i a)=changed i j l a"
proof -
 have ai: "a\<in>A i" using a unfolding changed_domain_def by simp
 have comm: "changed i j l a=common i l a"
   by (rule change_commutes_iff[THEN iffD1, OF hc, rule_format, OF i j l a])
 show ?thesis using canonical_representative_value[OF h i l ai refl refl] comm by simp
qed
lemma whole_family_representation:
 assumes h: descends
 shows "(\<forall>q\<in>Q. \<forall>l\<in>L. idx l=q \<longrightarrow> val_range l=raw_range q) \<and>
  (\<forall>i\<in>U. \<forall>l\<in>L. \<forall>a\<in>A i. raw_canonical(idx l,state i a)=common i l a)"
 by (intro conjI ballI impI)
   (rule range_representative_independence[OF h], assumption, assumption, assumption,
    rule canonical_representative_value[OF h], assumption, assumption, assumption, rule refl, rule refl)
end
ML \<open>
val roots = @{thms raw_observables.range_representative_independence
 raw_observables.canonical_representative_value raw_observables.canonical_value_typed
 raw_observables.canonical_unique raw_observables.local_change_compatibility
 raw_observables.whole_family_representation};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
