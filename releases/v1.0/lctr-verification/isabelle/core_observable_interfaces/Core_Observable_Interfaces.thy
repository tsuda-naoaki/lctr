theory Core_Observable_Interfaces
 imports "LCTR_Core_Native_Observables.Core_Native_Observables"
begin

lemma trajectory_single_domain_iff:
 assumes ty: "rel \<subseteq> T \<times> S"
 shows "(\<forall>t\<in>Domain rel. \<forall>s0\<in>S. \<forall>s1\<in>S.
   (t,s0)\<in>rel \<longrightarrow> (t,s1)\<in>rel \<longrightarrow> s0=s1) \<longleftrightarrow>
   (\<forall>t\<in>T. \<forall>s0\<in>S. \<forall>s1\<in>S.
   (t,s0)\<in>rel \<longrightarrow> (t,s1)\<in>rel \<longrightarrow> s0=s1)"
 using ty by blast

locale raw_observables = observer_seed C D B R Bind source_order
 for C :: "'c set" and D :: "'d set" and B :: "'b set"
 and R :: "('c \<times> 'd \<times> 'b) set"
 and Bind :: "(('c \<times> 'd \<times> 'b) \<times> ('c \<times> 'd \<times> 'b)) set"
 and source_order :: "('c \<times> 'c) set" +
 fixes U :: "'u set" and L :: "'l set" and Q :: "'q set"
 and A :: "'u \<Rightarrow> 'a set" and idx :: "'l \<Rightarrow> 'q"
 and record_map :: "'u \<Rightarrow> 'a \<Rightarrow> 'b"
 and local_values :: "'u \<Rightarrow> 'l \<Rightarrow> 'w set"
 and local_obs :: "'u \<Rightarrow> 'l \<Rightarrow> 'a \<Rightarrow> 'w"
 and compare :: "'u \<Rightarrow> 'l \<Rightarrow> 'w \<Rightarrow> 'v"
 and val_range :: "'l \<Rightarrow> 'v set"
 and change_dom :: "'u \<Rightarrow> 'u \<Rightarrow> 'l \<Rightarrow> 'w set"
 and change :: "'u \<Rightarrow> 'u \<Rightarrow> 'l \<Rightarrow> 'w \<Rightarrow> 'w"
 assumes idx_typed: "idx`L \<subseteq> Q"
 and record_typed: "\<And>i a. i\<in>U \<Longrightarrow> a\<in>A i \<Longrightarrow> record_map i a\<in>B"
 and local_typed: "\<And>i l a. i\<in>U \<Longrightarrow> l\<in>L \<Longrightarrow> a\<in>A i \<Longrightarrow> local_obs i l a\<in>local_values i l"
 and compare_typed: "\<And>i l w. i\<in>U \<Longrightarrow> l\<in>L \<Longrightarrow> w\<in>local_values i l \<Longrightarrow> compare i l w\<in>val_range l"
 and change_dom_typed: "\<And>i j l. i\<in>U \<Longrightarrow> j\<in>U \<Longrightarrow> l\<in>L \<Longrightarrow> change_dom i j l\<subseteq>local_values i l"
 and change_typed: "\<And>i j l w. i\<in>U \<Longrightarrow> j\<in>U \<Longrightarrow> l\<in>L \<Longrightarrow> w\<in>change_dom i j l \<Longrightarrow> change i j l w\<in>local_values j l"
begin
definition common where "common i l a=compare i l(local_obs i l a)"
definition changed_domain where "changed_domain i j l={a\<in>A i. local_obs i l a\<in>change_dom i j l}"
definition changed where "changed i j l a=compare j l(change i j l(local_obs i l a))"
definition state where "state i a=Image EB {record_map i a}"
definition descends where "descends \<longleftrightarrow>
 idx`L=Q \<and>
 (\<forall>l\<in>L. \<forall>k\<in>L. idx l=idx k \<longrightarrow> val_range l=val_range k) \<and>
 (\<forall>q\<in>Q. \<forall>s\<in>State. \<exists>i\<in>U. \<exists>l\<in>L. \<exists>a\<in>A i. idx l=q \<and> state i a=s) \<and>
 (\<forall>i\<in>U. \<forall>j\<in>U. \<forall>l\<in>L. \<forall>k\<in>L. \<forall>a\<in>A i. \<forall>b\<in>A j.
   idx l=idx k \<longrightarrow> state i a=state j b \<longrightarrow> common i l a=common j k b)"
definition change_commutes where "change_commutes \<longleftrightarrow>
 (\<forall>i\<in>U. \<forall>j\<in>U. \<forall>l\<in>L. \<forall>a\<in>A i.
   local_obs i l a\<in>change_dom i j l \<longrightarrow> compare j l(change i j l(local_obs i l a))=compare i l(local_obs i l a))"
definition samples where "samples={w. fst w\<in>U \<and> fst(snd w)\<in>L \<and> snd(snd w)\<in>A(fst w)}"
definition projection where "projection w=(idx(fst(snd w)),state(fst w)(snd(snd w)))"
definition comparison where "comparison w=common(fst w)(fst(snd w))(snd(snd w))"

lemma common_value_formula: "common i l=compare i l \<circ> local_obs i l"
 unfolding common_def by (rule ext) simp
lemma common_value_typed:
 "i\<in>U \<Longrightarrow> l\<in>L \<Longrightarrow> a\<in>A i \<Longrightarrow> common i l a\<in>val_range l"
 unfolding common_def by (rule compare_typed; (assumption | rule local_typed); assumption)
lemma changed_domain_iff:
 "a\<in>A i \<Longrightarrow> (a\<in>changed_domain i j l \<longleftrightarrow> local_obs i l a\<in>change_dom i j l)"
 unfolding changed_domain_def by simp
lemma changed_value_formula:
 "a\<in>changed_domain i j l \<Longrightarrow> changed i j l a=compare j l(change i j l(local_obs i l a))"
 unfolding changed_def by (rule refl)
lemma changed_value_typed:
 assumes i: "i\<in>U" and j: "j\<in>U" and l: "l\<in>L" and a: "a\<in>changed_domain i j l"
 shows "changed i j l a\<in>val_range l"
proof -
 have dm: "local_obs i l a\<in>change_dom i j l" using a unfolding changed_domain_def by simp
 show ?thesis unfolding changed_def by (rule compare_typed[OF j l change_typed[OF i j l dm]])
qed
lemma local_state_formula: "state i = (\<lambda>b. Image EB {b}) \<circ> record_map i"
 unfolding state_def by (rule ext) simp
lemma local_state_kernel:
 assumes i: "i\<in>U" and j: "j\<in>U" and a: "a\<in>A i" and b: "b\<in>A j"
 shows "state i a=state j b \<longleftrightarrow> (record_map i a,record_map j b)\<in>EB"
proof -
 have eqv: "equiv B EB" unfolding EB_def by (rule least_equiv_equivalence[OF source_generator_carriers(3)])
 show ?thesis unfolding state_def
   using eq_equiv_class_iff[OF eqv record_typed[OF i a] record_typed[OF j b]] by blast
qed
lemma descent_conditions_iff:
 "descends \<longleftrightarrow>
 idx`L=Q \<and>
 (\<forall>l\<in>L. \<forall>k\<in>L. idx l=idx k \<longrightarrow> val_range l=val_range k) \<and>
 (\<forall>q\<in>Q. \<forall>s\<in>State. \<exists>i\<in>U. \<exists>l\<in>L. \<exists>a\<in>A i. idx l=q \<and> state i a=s) \<and>
 (\<forall>i\<in>U. \<forall>j\<in>U. \<forall>l\<in>L. \<forall>k\<in>L. \<forall>a\<in>A i. \<forall>b\<in>A j.
   idx l=idx k \<longrightarrow> state i a=state j b \<longrightarrow> common i l a=common j k b)"
 unfolding descends_def by (rule refl)
lemma change_commutes_iff:
 "change_commutes \<longleftrightarrow> (\<forall>i\<in>U. \<forall>j\<in>U. \<forall>l\<in>L. \<forall>a\<in>changed_domain i j l. changed i j l a=common i l a)"
 unfolding change_commutes_def changed_domain_def changed_def common_def by blast
lemma state_typed: "i\<in>U \<Longrightarrow> a\<in>A i \<Longrightarrow> state i a\<in>State"
 using record_typed unfolding state_def State_def quotient_def by auto
lemma raw_projection_surjective:
 assumes h: descends
 shows "projection`samples=Q\<times>State"
proof
 show "projection`samples\<subseteq>Q\<times>State"
   using idx_typed state_typed unfolding projection_def samples_def by auto
 show "Q\<times>State\<subseteq>projection`samples"
 proof (rule subsetI)
  fix p assume p: "p\<in>Q\<times>State"
  note covers = conjunct1[OF conjunct2[OF conjunct2[OF h[unfolded descends_def]]]]
  have ps: "fst p\<in>Q" "snd p\<in>State" using p by auto
  obtain i l a where w: "i\<in>U" "l\<in>L" "a\<in>A i"
    and eq: "idx l=fst p" "state i a=snd p"
    using bspec[OF bspec[OF covers ps(1)] ps(2)] by blast
  have mem: "(i,l,a)\<in>samples" using w unfolding samples_def by simp
  have peq: "projection(i,l,a)=p" using eq unfolding projection_def by simp
  show "p\<in>projection`samples" using imageI[OF mem, of projection] peq by simp
 qed
qed
lemma raw_comparison_fiber_invariant:
 assumes h: descends and x: "x\<in>samples" and y: "y\<in>samples" and eq: "projection x=projection y"
 shows "comparison x=comparison y"
proof -
 note vk = conjunct2[OF conjunct2[OF conjunct2[OF h[unfolded descends_def]]]]
 have xt: "fst x\<in>U" "fst(snd x)\<in>L" "snd(snd x)\<in>A(fst x)"
   using x unfolding samples_def by auto
 have yt: "fst y\<in>U" "fst(snd y)\<in>L" "snd(snd y)\<in>A(fst y)"
   using y unfolding samples_def by auto
 have ix: "idx(fst(snd x))=idx(fst(snd y))"
   and st: "state(fst x)(snd(snd x))=state(fst y)(snd(snd y))"
   using eq unfolding projection_def by auto
 show ?thesis unfolding comparison_def
   by (rule vk[rule_format, OF xt(1) yt(1) xt(2) yt(2) xt(3) yt(3) ix st])
qed
lemma raw_factor_exists_unique:
 assumes h: descends
 shows "\<exists>f. (\<forall>x\<in>samples. comparison x=f(projection x)) \<and>
   (\<forall>g. (\<forall>x\<in>samples. comparison x=g(projection x)) \<longrightarrow> (\<forall>p\<in>Q\<times>State. g p=f p))"
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
 let ?f = "factor_choice samples projection comparison"
 have comm: "\<And>x. x\<in>samples \<Longrightarrow> comparison x=?f(projection x)"
   using factor_choice_agrees[OF ker] by simp
 have uniq: "\<And>g p. (\<forall>x\<in>samples. comparison x=g(projection x)) \<Longrightarrow> p\<in>Q\<times>State \<Longrightarrow> g p=?f p"
 proof -
  fix g p assume agrees: "\<forall>x\<in>samples. comparison x=g(projection x)" and p: "p\<in>Q\<times>State"
  obtain x where x: "x\<in>samples" and eq: "p=projection x" using p raw_projection_surjective[OF h] by blast
  show "g p=?f p" using bspec[OF agrees x] comm[OF x] eq by simp
 qed
 show ?thesis by (rule exI[where x="?f"]; intro conjI ballI allI impI)
   (rule comm, assumption, rule uniq, assumption, assumption)
qed
end
ML \<open>
val roots = @{thms trajectory_single_domain_iff
 raw_observables.common_value_formula raw_observables.common_value_typed
 raw_observables.changed_domain_iff raw_observables.changed_value_formula raw_observables.changed_value_typed
 raw_observables.local_state_formula raw_observables.local_state_kernel
 raw_observables.descent_conditions_iff raw_observables.change_commutes_iff
 raw_observables.raw_projection_surjective raw_observables.raw_comparison_fiber_invariant
 raw_observables.raw_factor_exists_unique};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
