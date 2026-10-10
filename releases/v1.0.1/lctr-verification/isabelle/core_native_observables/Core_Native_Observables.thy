theory Core_Native_Observables
  imports "LCTR_Core_Native_Curves.Core_Native_Curves"
    "LCTR_Core_Observable_Descent.Core_Observable_Descent"
begin
locale native_observables = observer_seed C D B R Bind source_order
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
  assumes record_typed: "\<And>u a. u\<in>U \<Longrightarrow> a\<in>A u \<Longrightarrow> record_map u a\<in>B"
    and local_typed: "\<And>u l a. u\<in>U \<Longrightarrow> l\<in>L \<Longrightarrow> a\<in>A u \<Longrightarrow> local_obs u l a\<in>local_values u l"
    and compare_typed: "\<And>u l v. u\<in>U \<Longrightarrow> l\<in>L \<Longrightarrow> v\<in>local_values u l \<Longrightarrow> compare u l v\<in>val_range l"
    and index_onto: "image idx L=Q"
    and range_kernel: "\<And>l k. l\<in>L \<Longrightarrow> k\<in>L \<Longrightarrow> idx l=idx k \<Longrightarrow> val_range l=val_range k"
    and covers: "\<And>q s. q\<in>Q \<Longrightarrow> s\<in>State \<Longrightarrow>
      \<exists>u\<in>U. \<exists>l\<in>L. \<exists>a\<in>A u. idx l=q \<and> Image EB {record_map u a}=s"
    and value_kernel: "\<And>u v l k a b. u\<in>U \<Longrightarrow> v\<in>U \<Longrightarrow> l\<in>L \<Longrightarrow> k\<in>L \<Longrightarrow>
      a\<in>A u \<Longrightarrow> b\<in>A v \<Longrightarrow> idx l=idx k \<Longrightarrow>
      Image EB {record_map u a}=Image EB {record_map v b} \<Longrightarrow>
      compare u l(local_obs u l a)=compare v k(local_obs v k b)"
begin
definition local_state where "local_state u a=Image EB {record_map u a}"
definition common_compare where "common_compare u l a=compare u l(local_obs u l a)"
definition samples where "samples={w. fst w\<in>U \<and> fst(snd w)\<in>L \<and> snd(snd w)\<in>A(fst w)}"
definition projection where "projection w=(idx(fst(snd w)),local_state(fst w)(snd(snd w)))"
definition comparison where "comparison w=common_compare(fst w)(fst(snd w))(snd(snd w))"

lemma state_typed: "u\<in>U \<Longrightarrow> a\<in>A u \<Longrightarrow> local_state u a\<in>State"
  using record_typed unfolding local_state_def State_def quotient_def by auto
lemma comparison_typed: "u\<in>U \<Longrightarrow> l\<in>L \<Longrightarrow> a\<in>A u \<Longrightarrow> common_compare u l a\<in>val_range l"
  unfolding common_compare_def by (rule compare_typed; (assumption | rule local_typed); assumption)
sublocale obs: observable_descent U L Q State A idx local_state val_range common_compare
proof
  show "image idx L=Q" by (rule index_onto)
  show "\<And>u a. u\<in>U \<Longrightarrow> a\<in>A u \<Longrightarrow> local_state u a\<in>State" by (rule state_typed)
  show "\<And>u l a. u\<in>U \<Longrightarrow> l\<in>L \<Longrightarrow> a\<in>A u \<Longrightarrow> common_compare u l a\<in>val_range l" by (rule comparison_typed)
  show "\<And>l k. l\<in>L \<Longrightarrow> k\<in>L \<Longrightarrow> idx l=idx k \<Longrightarrow> val_range l=val_range k" by (rule range_kernel)
  show "\<And>q s. q\<in>Q \<Longrightarrow> s\<in>State \<Longrightarrow> \<exists>u\<in>U. \<exists>l\<in>L. \<exists>a\<in>A u. idx l=q \<and> local_state u a=s"
    unfolding local_state_def by (rule covers)
  show "\<And>u v l k a b. u\<in>U \<Longrightarrow> v\<in>U \<Longrightarrow> l\<in>L \<Longrightarrow> k\<in>L \<Longrightarrow> a\<in>A u \<Longrightarrow>
    b\<in>A v \<Longrightarrow> idx l=idx k \<Longrightarrow> local_state u a=local_state v b \<Longrightarrow>
    common_compare u l a=common_compare v k b"
    unfolding local_state_def common_compare_def by (rule value_kernel)
qed
lemma actual_projection_surjective: "image projection samples=Q\<times>State"
proof
  show "image projection samples\<subseteq>Q\<times>State"
    using state_typed index_onto unfolding projection_def samples_def by auto
  show "Q\<times>State\<subseteq>image projection samples"
  proof (rule subsetI)
    fix p assume p: "p\<in>Q\<times>State"
    obtain u l a where ua: "u\<in>U" "l\<in>L" "a\<in>A u"
      and ps: "idx l=fst p" "local_state u a=snd p"
      using obs.coverage[of "fst p" "snd p"] p by auto
    have w: "(u,l,a)\<in>samples" using ua unfolding samples_def by simp
    have eq: "projection(u,l,a)=p" using ps unfolding projection_def by simp
    show "p\<in>image projection samples" using imageI[OF w, of projection] eq by simp
  qed
qed
lemma actual_comparison_fiber_invariant:
  "x\<in>samples \<Longrightarrow> y\<in>samples \<Longrightarrow> projection x=projection y \<Longrightarrow> comparison x=comparison y"
  unfolding comparison_def by (rule obs.value_fiber) (auto simp: projection_def samples_def)
lemma canonical_representative_value:
  assumes u: "u\<in>U" and l: "l\<in>L" and a: "a\<in>A u" and qi: "idx l=q" and si: "local_state u a=s"
  shows "obs.canonical q s=compare u l(local_obs u l a)"
proof -
  have q: "q\<in>Q" using l qi index_onto by blast
  have s: "s\<in>State" using state_typed[OF u a] si by simp
  have w: "(u,l,a)\<in>obs.representatives q s"
    using u l a qi si unfolding obs.representatives_def by simp
  show ?thesis using obs.canonical_representative[OF q s w]
    unfolding obs.comparison_def common_compare_def by simp
qed
lemma canonical_sample:
  assumes w: "w\<in>samples"
  shows "comparison w=obs.canonical(fst(projection w))(snd(projection w))"
proof -
  have ua: "fst w\<in>U" "fst(snd w)\<in>L" "snd(snd w)\<in>A(fst w)"
    using w unfolding samples_def by auto
  have eq: "obs.canonical(idx(fst(snd w)))(local_state(fst w)(snd(snd w)))=
    compare(fst w)(fst(snd w))(local_obs(fst w)(fst(snd w))(snd(snd w)))"
    by (rule canonical_representative_value[OF ua refl refl])
  show ?thesis using eq unfolding comparison_def common_compare_def projection_def by simp
qed
lemma canonical_unique:
  assumes commute: "\<And>u l a. u\<in>U \<Longrightarrow> l\<in>L \<Longrightarrow> a\<in>A u \<Longrightarrow>
    g(idx l,local_state u a)=compare u l(local_obs u l a)"
  shows "\<forall>p\<in>Q\<times>State. g p=obs.canonical(fst p)(snd p)"
proof (intro ballI)
  fix p assume p: "p\<in>Q\<times>State"
  obtain w where w: "w\<in>samples" and pw: "p=projection w"
    using actual_projection_surjective p by blast
  show "g p=obs.canonical(fst p)(snd p)"
    using commute[of "fst w" "fst(snd w)" "snd(snd w)"] canonical_sample[OF w] w pw
    unfolding samples_def projection_def comparison_def common_compare_def by simp
qed
lemma native_factor_exists_unique:
  "\<exists>f. (\<forall>w\<in>samples. comparison w=f(projection w)) \<and>
    (\<forall>g. (\<forall>w\<in>samples. comparison w=g(projection w)) \<longrightarrow>
      (\<forall>p\<in>Q\<times>State. g p=f p))"
proof -
  let ?f = "\<lambda>p. obs.canonical(fst p)(snd p)"
  have commute: "\<forall>w\<in>samples. comparison w=?f(projection w)" using canonical_sample by blast
  have unique: "\<And>g. (\<forall>w\<in>samples. comparison w=g(projection w)) \<Longrightarrow>
    (\<forall>p\<in>Q\<times>State. g p=?f p)"
  proof -
    fix g assume h: "\<forall>w\<in>samples. comparison w=g(projection w)"
    show "\<forall>p\<in>Q\<times>State. g p=?f p"
    proof (rule canonical_unique)
      fix u l a assume ua: "u\<in>U" "l\<in>L" "a\<in>A u"
      have w: "(u,l,a)\<in>samples" using ua unfolding samples_def by simp
      show "g(idx l,local_state u a)=compare u l(local_obs u l a)"
        using bspec[OF h w] unfolding comparison_def projection_def common_compare_def by simp
    qed
  qed
  show ?thesis by (rule exI[where x="?f"]; intro conjI allI impI)
    (rule commute, rule unique, assumption)
qed
lemma range_representative_independence:
  "q\<in>Q \<Longrightarrow> l\<in>L \<Longrightarrow> idx l=q \<Longrightarrow> val_range l=obs.canonical_range q"
  by (rule obs.range_independent)
lemma canonical_value_typed:
  "q\<in>Q \<Longrightarrow> s\<in>State \<Longrightarrow> obs.canonical q s\<in>obs.canonical_range q"
  by (rule obs.canonical_typed)
lemma local_change_compatibility:
  assumes u: "u\<in>U" and v: "v\<in>U" and l: "l\<in>L" and a: "a\<in>A u"
    and dom: "local_obs u l a\<in>change_domain u v l"
    and commutes: "\<And>u v l a. u\<in>U \<Longrightarrow> v\<in>U \<Longrightarrow> l\<in>L \<Longrightarrow> a\<in>A u \<Longrightarrow>
      local_obs u l a\<in>change_domain u v l \<Longrightarrow>
      compare v l(change u v l(local_obs u l a))=compare u l(local_obs u l a)"
  shows "obs.canonical(idx l)(local_state u a)=compare v l(change u v l(local_obs u l a))"
  using canonical_representative_value[OF u l a refl refl] commutes[OF u v l a dom] by simp
end

locale native_observable_curves =
  native_observables C D B R Bind source_order U L Q A idx record_map local_values local_obs compare val_range +
  observer_real C D B R Bind source_order rho
  for C :: "'c set" and D :: "'d set" and B :: "'b set"
    and R :: "('c \<times> 'd \<times> 'b) set"
    and Bind :: "(('c \<times> 'd \<times> 'b) \<times> ('c \<times> 'd \<times> 'b)) set"
    and source_order :: "('c \<times> 'c) set"
    and U :: "'u set" and L :: "'l set" and Q :: "'q set"
    and A :: "'u \<Rightarrow> 'a set" and idx :: "'l \<Rightarrow> 'q"
    and record_map :: "'u \<Rightarrow> 'a \<Rightarrow> 'b"
    and local_values :: "'u \<Rightarrow> 'l \<Rightarrow> 'w set"
    and local_obs :: "'u \<Rightarrow> 'l \<Rightarrow> 'a \<Rightarrow> 'w"
    and compare :: "'u \<Rightarrow> 'l \<Rightarrow> 'w \<Rightarrow> 'v"
    and val_range :: "'l \<Rightarrow> 'v set" and rho :: "'c set set \<Rightarrow> real"
begin
lemma native_curve_local_value:
  assumes fiber: fiber_condition and t: "t\<in>trajectory_domain"
    and u: "u\<in>U" and l: "l\<in>L" and a: "a\<in>A u"
    and state_eq: "local_state u a=canonical_trajectory t"
  shows "real_curve(obs.canonical(idx l))(rho(restricted_projection t))=compare u l(local_obs u l a)"
proof -
  have fac: "obs.canonical(idx l)(canonical_trajectory t)=
    real_curve(obs.canonical(idx l))(rho(restricted_projection t))"
    using bspec[OF conjunct1[OF observable_factorization[OF fiber, of "obs.canonical(idx l)"]] t] by simp
  show ?thesis using fac canonical_representative_value[OF u l a refl state_eq] by simp
qed
end
ML \<open>
val roots = @{thms native_observables.actual_projection_surjective native_observables.actual_comparison_fiber_invariant
 native_observables.native_factor_exists_unique native_observables.range_representative_independence
 native_observables.canonical_representative_value native_observables.canonical_value_typed
 native_observables.canonical_unique native_observables.local_change_compatibility native_observable_curves.native_curve_local_value};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
