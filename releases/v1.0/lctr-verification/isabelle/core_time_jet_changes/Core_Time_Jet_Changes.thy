theory Core_Time_Jet_Changes
  imports "LCTR_Core_Curve_Regularity.Core_Curve_Regularity"
begin

definition time_acts where
  "time_acts k a b V g J \<longleftrightarrow> g b=a \<and>
    J ` jet_domain k V \<subseteq> jet_domain k V \<and>
    (\<forall>c. curve_ck_at k a c \<longrightarrow> c a\<in>V \<longrightarrow>
      J (jet k a c) = jet k b (c \<circ> g))"

lemma time_acts_apply:
  "time_acts k a b V g J \<Longrightarrow> curve_ck_at k a c \<Longrightarrow> c a\<in>V \<Longrightarrow>
    J (jet k a c) = jet k b (c \<circ> g)"
  unfolding time_acts_def by blast

lemma lift_unique:
  assumes j: "time_acts k a b V g J" and h: "time_acts k a b V g K"
  shows "\<forall>v\<in>jet_domain k V. J v=K v"
proof (intro ballI)
  fix v assume v: "v\<in>jet_domain k V"
  obtain c where c: "curve_ck_at k a c" "c a\<in>V" "jet k a c=v"
    by (rule jet_domain_realization[OF v])
  show "J v=K v" using time_acts_apply[OF j c(1,2)] time_acts_apply[OF h c(1,2)] c(3) by simp
qed

lemma lift_identity:
  assumes j: "time_acts k a a V id J"
  shows "\<forall>v\<in>jet_domain k V. J v=v"
proof (intro ballI)
  fix v assume v: "v\<in>jet_domain k V"
  obtain c where c: "curve_ck_at k a c" "c a\<in>V" "jet k a c=v"
    by (rule jet_domain_realization[OF v])
  show "J v=v" using time_acts_apply[OF j c(1,2)] c(3) by simp
qed

lemma lift_left_inverse:
  assumes ou: "open U" and au: "a\<in>U"
    and fa: "f a=b" and gb: "g b=a"
    and gs: "curve_ck_at k b g"
    and inv: "\<forall>x\<in>U. g (f x)=x"
    and j: "time_acts k a b V g J" and h: "time_acts k b a V f K"
  shows "\<forall>v\<in>jet_domain k V. K (J v)=v"
proof (intro ballI)
  fix v assume v: "v\<in>jet_domain k V"
  obtain c where c: "curve_ck_at k a c" "c a\<in>V" "jet k a c=v"
    by (rule jet_domain_realization[OF v])
  have cs: "curve_ck_at k (g b) c" using c(1) gb by simp
  have cgs: "curve_ck_at k b (c \<circ> g)" by (rule curve_ck_comp[OF cs gs])
  have cv: "(c \<circ> g) b\<in>V" using c(2) gb by simp
  have e: "eventually (\<lambda>x. ((c \<circ> g) \<circ> f) x=c x) (nhds a)"
    using eventually_nhds_in_open[OF ou au]
    by eventually_elim (use inv in auto)
  have eq: "jet k a ((c \<circ> g) \<circ> f)=jet k a c" by (rule jet_germ[OF e])
  show "K (J v)=v"
    using time_acts_apply[OF j c(1,2)] time_acts_apply[OF h cgs cv] eq c(3) by (simp add: o_def)
qed

lemma lift_bijective:
  assumes ou: "open U" and ow: "open W" and au: "a\<in>U" and bw: "b\<in>W"
    and fa: "f a=b" and gb: "g b=a"
    and fs: "higher_differentiable_on U f k" and gs: "higher_differentiable_on W g k"
    and li: "\<forall>x\<in>U. g (f x)=x" and ri: "\<forall>y\<in>W. f (g y)=y"
    and j: "time_acts k a b V g J" and h: "time_acts k b a V f K"
  shows "bij_betw J (jet_domain k V) (jet_domain k V)"
proof -
  have f: "curve_ck_at k a f" by (rule curve_ck_on_at[OF ou au fs])
  have g: "curve_ck_at k b g" by (rule curve_ck_on_at[OF ow bw gs])
  have l: "\<forall>v\<in>jet_domain k V. K (J v)=v"
    by (rule lift_left_inverse[OF ou au fa gb g li j h])
  have r: "\<forall>v\<in>jet_domain k V. J (K v)=v"
    by (rule lift_left_inverse[OF ow bw gb fa f ri h j])
  show ?thesis by (rule bij_betw_byWitness[where f=J and f'=K, OF l r])
    (use j h in \<open>auto simp: time_acts_def\<close>)
qed

lemma lift_composition:
  assumes gb: "g b=a" and hd: "h d=b" and gs: "curve_ck_at k b g"
    and j: "time_acts k a b V g J" and kk: "time_acts k b d V h K"
    and hh: "time_acts k a d V (g \<circ> h) H"
  shows "\<forall>v\<in>jet_domain k V. (K \<circ> J) v=H v"
proof (intro ballI)
  fix v assume v: "v\<in>jet_domain k V"
  obtain c where c: "curve_ck_at k a c" "c a\<in>V" "jet k a c=v"
    by (rule jet_domain_realization[OF v])
  have cs: "curve_ck_at k (g b) c" using c(1) gb by simp
  have cgs: "curve_ck_at k b (c \<circ> g)" by (rule curve_ck_comp[OF cs gs])
  have cv: "(c \<circ> g) b\<in>V" using c(2) gb by simp
  show "(K \<circ> J) v=H v"
    using time_acts_apply[OF j c(1,2)] time_acts_apply[OF kk cgs cv]
      time_acts_apply[OF hh c(1,2)] c(3)
    by (simp add: o_def)
qed

lemma base_and_fiber_bijective:
  assumes b: "bij_betw base X Y" and f: "\<forall>x\<in>X. bij_betw (fiber x) Z W"
  shows "bij_betw (\<lambda>(x,z). (base x, fiber x z)) (X\<times>Z) (Y\<times>W)"
proof -
  let ?F = "\<lambda>(x,z). (base x, fiber x z)"
  have bi: "inj_on base X" and bo: "base ` X=Y" using b by (auto simp: bij_betw_def)
  have fi: "inj_on (fiber x) Z" and fo: "fiber x ` Z=W" if "x\<in>X" for x
    using f that by (auto simp: bij_betw_def)
  have inj: "inj_on ?F (X\<times>Z)"
  proof (rule inj_onI)
    fix p q assume p: "p\<in>X\<times>Z" and q: "q\<in>X\<times>Z" and eq: "?F p=?F q"
    obtain x z where px: "p=(x,z)" by (cases p) auto
    obtain y w where qy: "q=(y,w)" by (cases q) auto
    have xy: "x=y" using bi p q eq by (auto simp: px qy inj_on_def)
    have zw: "z=w" using fi[of x] p q eq xy by (auto simp: px qy inj_on_def)
    show "p=q" by (simp add: px qy xy zw)
  qed
  have image: "?F ` (X\<times>Z)=Y\<times>W"
  proof (rule set_eqI, rule iffI)
    fix q assume "q\<in>?F ` (X\<times>Z)"
    then show "q\<in>Y\<times>W" using bo fo by auto
  next
    fix q assume q: "q\<in>Y\<times>W"
    obtain y w where qw: "q=(y,w)" by (cases q) auto
    obtain x where x: "x\<in>X" "base x=y" using bo q by (auto simp: qw)
    obtain z where z: "z\<in>Z" "fiber x z=w" using fo[OF x(1)] q by (auto simp: qw)
    show "q\<in>?F ` (X\<times>Z)" by (rule image_eqI[where x="(x,z)"]) (simp_all add: qw x z)
  qed
  show ?thesis using inj image by (simp add: bij_betw_def)
qed

lemma time_jet_full_domain_bijective:
  assumes ou: "open U" and ow: "open W"
    and fm: "f ` U\<subseteq>W" and gm: "g ` W\<subseteq>U"
    and fs: "higher_differentiable_on U f k" and gs: "higher_differentiable_on W g k"
    and li: "\<forall>x\<in>U. g (f x)=x" and ri: "\<forall>y\<in>W. f (g y)=y"
    and j: "\<forall>a\<in>U. time_acts k a (f a) V g (J a)"
    and h: "\<forall>a\<in>U. time_acts k (f a) a V f (K (f a))"
  shows "bij_betw (\<lambda>(a,v). (f a,J a v)) (U\<times>jet_domain k V) (W\<times>jet_domain k V)"
proof -
  have b: "bij_betw f U W" by (rule bij_betw_byWitness[OF li ri fm gm])
  have fibers: "bij_betw (J a) (jet_domain k V) (jet_domain k V)" if a: "a\<in>U" for a
  proof -
    have fw: "f a\<in>W" using fm a by blast
    have ga: "g (f a)=a" using li a by blast
    have jj: "time_acts k a (f a) V g (J a)" using j a by blast
    have kk: "time_acts k (f a) a V f (K (f a))" using h a by blast
    show ?thesis by (rule lift_bijective[OF ou ow a fw refl ga fs gs li ri jj kk])
  qed
  show ?thesis by (rule base_and_fiber_bijective[OF b]) (use fibers in blast)
qed

lemma full_domain_relation_image:
  assumes b: "bij_betw base X Y" and f: "\<forall>x\<in>X. bij_betw (fiber x) Z W"
    and a: "A\<subseteq>X\<times>Z" and bb: "B\<subseteq>Y\<times>W"
    and cov: "\<forall>p\<in>X\<times>Z. p\<in>A \<longleftrightarrow> (base (fst p),fiber (fst p) (snd p))\<in>B"
  shows "(\<lambda>(x,z). (base x,fiber x z)) ` A=B"
proof -
  let ?F = "\<lambda>(x,z). (base x,fiber x z)"
  have onto: "?F ` (X\<times>Z)=Y\<times>W"
    using base_and_fiber_bijective[OF b f] by (simp add: bij_betw_def)
  have c: "p\<in>A \<longleftrightarrow> ?F p\<in>B" if "p\<in>X\<times>Z" for p
    using cov that by (cases p) auto
  show ?thesis
  proof (rule set_eqI, rule iffI)
    fix y assume "y\<in>?F ` A"
    then obtain p where p: "p\<in>A" "?F p=y" by blast
    have px: "p\<in>X\<times>Z" using a p(1) by blast
    show "y\<in>B" using c[OF px] p by simp
  next
    fix y assume y: "y\<in>B"
    have yw: "y\<in>Y\<times>W" using bb y by blast
    have yi: "y\<in>?F ` (X\<times>Z)" using yw by (simp only: onto)
    obtain p where p: "p\<in>X\<times>Z" "?F p=y" using yi by (auto simp only: image_iff)
    have pa: "p\<in>A" using c[OF p(1)] p(2) y by simp
    show "y\<in>?F ` A" by (rule image_eqI[where x=p]) (use p(2) pa in auto)
  qed
qed

ML \<open>
val roots = @{thms lift_unique lift_identity lift_left_inverse lift_bijective lift_composition
  base_and_fiber_bijective time_jet_full_domain_bijective full_domain_relation_image};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
