theory Core_Scale_Transport
  imports LCTR_Core_Continuum_Boundary.Core_Continuum_Boundary
begin

lemma image_of_iff:
  assumes bij: "bij_betw c I J" and pi: "P\<subseteq>I" and qj: "Q\<subseteq>J"
    and iff: "\<And>i. i\<in>I \<Longrightarrow> (i\<in>P) = (c i\<in>Q)"
  shows "image c P = Q"
proof (rule set_eqI)
  fix j
  show "(j\<in>image c P) = (j\<in>Q)"
  proof
    assume "j\<in>image c P"
    then obtain i where ip: "i\<in>P" and j: "j=c i" by blast
    have ii: "i\<in>I" using ip pi by blast
    show "j\<in>Q" using iff[OF ii] ip j by simp
  next
    assume jq: "j\<in>Q"
    have "j\<in>J" using jq qj by blast
    then obtain i where ii: "i\<in>I" and ci: "c i=j"
      using bij unfolding bij_betw_def by blast
    have "i\<in>P" using iff[OF ii] ci jq by simp
    then show "j\<in>image c P" using ci by blast
  qed
qed

locale data_transport =
  fixes I :: "'i set" and J :: "'j set" and c :: "'i\<Rightarrow>'j"
    and v :: "ereal\<Rightarrow>ereal"
    and d0 e0 :: "'i\<Rightarrow>ereal" and d1 e1 :: "'j\<Rightarrow>ereal"
  assumes bij_c: "bij_betw c I J"
    and value_order: "\<And>a b. 0\<le>a \<Longrightarrow> 0\<le>b \<Longrightarrow> (v a\<le>v b) = (a\<le>b)"
    and d0_nn: "\<And>i. i\<in>I \<Longrightarrow> 0\<le>d0 i"
    and e0_nn: "\<And>i. i\<in>I \<Longrightarrow> 0\<le>e0 i"
    and d1_nn: "\<And>j. j\<in>J \<Longrightarrow> 0\<le>d1 j"
    and e1_nn: "\<And>j. j\<in>J \<Longrightarrow> 0\<le>e1 j"
    and hd: "\<And>i. i\<in>I \<Longrightarrow> d1 (c i)=v (d0 i)"
    and he: "\<And>i. i\<in>I \<Longrightarrow> e1 (c i)=v (e0 i)"
begin
lemma c_in: "i\<in>I \<Longrightarrow> c i\<in>J"
  using bij_c unfolding bij_betw_def by blast
lemma value_equal:
  "0\<le>a \<Longrightarrow> 0\<le>b \<Longrightarrow> (v a=v b) = (a=b)"
  using value_order by (metis antisym eq_iff)
lemma value_less:
  assumes a: "0\<le>a" and b: "0\<le>b"
  shows "(v a<v b) = (a<b)"
  using value_order[OF a b] value_order[OF b a] by (simp add: less_le_not_le)
lemma validity_under_data_iso:
  "valid I d0 e0 = valid J d1 e1"
proof
  assume v0: "valid I d0 e0"
  show "valid J d1 e1"
  proof (unfold valid_def, intro ballI)
    fix j
    assume jj: "j\<in>J"
    obtain i where ii: "i\<in>I" and ci: "c i=j"
      using bij_c jj unfolding bij_betw_def by blast
    have old: "d0 i\<le>e0 i" using v0 ii unfolding valid_def by blast
    have "v (d0 i)\<le>v (e0 i)"
      using value_order[OF d0_nn[OF ii] e0_nn[OF ii]] old by simp
    then show "d1 j\<le>e1 j" using hd[OF ii] he[OF ii] ci by simp
  qed
next
  assume v1: "valid J d1 e1"
  show "valid I d0 e0"
  proof (unfold valid_def, intro ballI)
    fix i
    assume ii: "i\<in>I"
    have "d1 (c i)\<le>e1 (c i)" using v1 c_in[OF ii] unfolding valid_def by blast
    then have "v (d0 i)\<le>v (e0 i)" using hd[OF ii] he[OF ii] by simp
    then show "d0 i\<le>e0 i" using value_order[OF d0_nn[OF ii] e0_nn[OF ii]] by simp
  qed
qed

lemma saturation_image: "image c (saturated I d0 e0) = saturated J d1 e1"
proof (rule image_of_iff[OF bij_c])
  show "saturated I d0 e0\<subseteq>I" by (simp add: saturated_def)
  show "saturated J d1 e1\<subseteq>J" by (simp add: saturated_def)
  fix i
  assume ii: "i\<in>I"
  have ci: "c i\<in>J" by (rule c_in[OF ii])
  have old: "(margin (e0 i) (d0 i)=0) = (d0 i=e0 i)"
    by (rule margin_zero[OF e0_nn[OF ii] d0_nn[OF ii]])
  have new: "(margin (e1 (c i)) (d1 (c i))=0) = (d1 (c i)=e1 (c i))"
    by (rule margin_zero[OF e1_nn[OF ci] d1_nn[OF ci]])
  have eq: "(d1 (c i)=e1 (c i)) = (d0 i=e0 i)"
    using value_equal[OF d0_nn[OF ii] e0_nn[OF ii]] hd[OF ii] he[OF ii] by simp
  show "(i\<in>saturated I d0 e0) = (c i\<in>saturated J d1 e1)"
    using ii ci old new eq unfolding saturated_def by simp
qed

lemma exceeded_image: "image c (exceeded I d0 e0) = exceeded J d1 e1"
proof (rule image_of_iff[OF bij_c])
  show "exceeded I d0 e0\<subseteq>I" by (simp add: exceeded_def)
  show "exceeded J d1 e1\<subseteq>J" by (simp add: exceeded_def)
  fix i
  assume ii: "i\<in>I"
  have ci: "c i\<in>J" by (rule c_in[OF ii])
  have old: "(0<excess (e0 i) (d0 i)) = (e0 i<d0 i)"
    by (rule excess_positive[OF e0_nn[OF ii] d0_nn[OF ii]])
  have new: "(0<excess (e1 (c i)) (d1 (c i))) = (e1 (c i)<d1 (c i))"
    by (rule excess_positive[OF e1_nn[OF ci] d1_nn[OF ci]])
  have eq: "(e1 (c i)<d1 (c i)) = (e0 i<d0 i)"
    using value_less[OF e0_nn[OF ii] d0_nn[OF ii]] hd[OF ii] he[OF ii] by simp
  show "(i\<in>exceeded I d0 e0) = (c i\<in>exceeded J d1 e1)"
    using ii ci old new eq unfolding exceeded_def by simp
qed
end

definition least_pre :: "'a::preorder set\<Rightarrow>'a\<Rightarrow>bool" where
  "least_pre A a = (a\<in>A \<and> (\<forall>x\<in>A. a\<le>x))"

locale order_transport =
  fixes e :: "'a::preorder\<Rightarrow>'b::preorder"
  assumes bij_e: "bij e" and order_e: "\<And>x y. (e x\<le>e y) = (x\<le>y)"
begin
lemma inj_e: "inj e" using bij_e unfolding bij_def by blast
lemma surj_e: "surj e" using bij_e unfolding bij_def by blast
lemma initial_image:
  assumes iv: "initial V"
  shows "initial (image e V)"
proof (unfold initial_def, intro allI impI)
  fix x y :: 'b
  assume xy: "x\<le>y" and yv: "y\<in>image e V"
  obtain a where av: "a\<in>V" and ey: "e a=y" using yv by blast
  obtain b where ex: "e b=x" using surjD[OF surj_e, of x] by blast
  have ba: "b\<le>a" using order_e[of b a] xy ex ey by simp
  have "b\<in>V" using iv ba av unfolding initial_def by blast
  then show "x\<in>image e V" using ex by blast
qed

lemma maximal_initial_image:
  "image e (maximal_initial V) = maximal_initial (image e V)"
proof (rule subset_antisym)
  have sub: "maximal_initial V\<subseteq>V" and ini: "initial (maximal_initial V)"
    using maximal_initial_greatest[of V] unfolding initial_family_def by auto
  have imsub: "image e (maximal_initial V)\<subseteq>image e V" by (rule image_mono[OF sub])
  have imini: "initial (image e (maximal_initial V))" by (rule initial_image[OF ini])
  have mem: "image e (maximal_initial V)\<in>initial_family (image e V)"
    using imsub imini by (simp add: initial_family_def)
  have greatest: "\<forall>A\<in>initial_family (image e V). A\<subseteq>maximal_initial (image e V)"
    by (rule conjunct2[OF maximal_initial_greatest])
  show "image e (maximal_initial V)\<subseteq>maximal_initial (image e V)"
    by (rule bspec[OF greatest mem])
next
  have sub: "maximal_initial (image e V)\<subseteq>image e V"
    and ini: "initial (maximal_initial (image e V))"
    using maximal_initial_greatest[of "image e V"] unfolding initial_family_def by auto
  have pre_sub: "vimage e (maximal_initial (image e V))\<subseteq>V"
    using sub inj_e unfolding inj_def by blast
  have pre_ini: "initial (vimage e (maximal_initial (image e V)))"
    using ini order_e unfolding initial_def by blast
  have mem: "vimage e (maximal_initial (image e V))\<in>initial_family V"
    using pre_sub pre_ini by (simp add: initial_family_def)
  have greatest: "\<forall>A\<in>initial_family V. A\<subseteq>maximal_initial V"
    by (rule conjunct2[OF maximal_initial_greatest])
  have pre_max: "vimage e (maximal_initial (image e V))\<subseteq>maximal_initial V"
    by (rule bspec[OF greatest mem])
  show "maximal_initial (image e V)\<subseteq>image e (maximal_initial V)"
  proof
    fix y :: 'b
    assume ym: "y\<in>maximal_initial (image e V)"
    obtain x where ex: "e x=y" using surjD[OF surj_e, of y] by blast
    have "x\<in>maximal_initial V" using pre_max ym ex by blast
    then show "y\<in>image e (maximal_initial V)" using ex by blast
  qed
qed

lemma least_image_iff:
  "least_pre V a = least_pre (image e V) (e a)"
proof
  assume l: "least_pre V a"
  have a: "a\<in>V" and low: "\<And>x. x\<in>V \<Longrightarrow> a\<le>x"
    using l unfolding least_pre_def by auto
  have ea: "e a\<in>image e V" using a by blast
  have elow: "\<And>y. y\<in>image e V \<Longrightarrow> e a\<le>y"
  proof -
    fix y
    assume "y\<in>image e V"
    then obtain x where xv: "x\<in>V" and ex: "e x=y" by blast
    show "e a\<le>y" using order_e[of a x] low[OF xv] ex by simp
  qed
  show "least_pre (image e V) (e a)" using ea elow unfolding least_pre_def by blast
next
  assume l: "least_pre (image e V) (e a)"
  have ea: "e a\<in>image e V" and low: "\<And>y. y\<in>image e V \<Longrightarrow> e a\<le>y"
    using l unfolding least_pre_def by auto
  have a: "a\<in>V" using ea inj_e unfolding inj_def by blast
  have alow: "\<And>x. x\<in>V \<Longrightarrow> a\<le>x"
  proof -
    fix x
    assume "x\<in>V"
    then have exv: "e x\<in>image e V" by blast
    show "a\<le>x" using low[OF exv] order_e[of a x] by simp
  qed
  show "least_pre V a" using a alow unfolding least_pre_def by blast
qed

lemma least_exists_iff:
  "(\<exists>a. least_pre V a) = (\<exists>b. least_pre (image e V) b)"
proof
  assume "\<exists>a. least_pre V a"
  then obtain a where "least_pre V a" by blast
  then show "\<exists>b. least_pre (image e V) b" using least_image_iff[of V a] by blast
next
  assume "\<exists>b. least_pre (image e V) b"
  then obtain b where lb: "least_pre (image e V) b" by blast
  obtain a where ea: "e a=b" using surjD[OF surj_e, of b] by blast
  show "\<exists>a. least_pre V a" using least_image_iff[of V a] lb ea by blast
qed
end

locale scale_transport = order_transport e
  for e :: "'a::linorder\<Rightarrow>'b::linorder" +
  fixes I :: "'i set" and J :: "'j set" and c :: "'i\<Rightarrow>'j"
    and v :: "ereal\<Rightarrow>ereal"
    and d0 :: "'a\<Rightarrow>'i\<Rightarrow>ereal" and d1 :: "'b\<Rightarrow>'j\<Rightarrow>ereal"
    and eps0 :: "'i\<Rightarrow>ereal" and eps1 :: "'j\<Rightarrow>ereal"
  assumes bij_c: "bij_betw c I J"
    and value_order: "\<And>x y. 0\<le>x \<Longrightarrow> 0\<le>y \<Longrightarrow> (v x\<le>v y) = (x\<le>y)"
    and d0_nn: "\<And>a i. i\<in>I \<Longrightarrow> 0\<le>d0 a i"
    and eps0_nn: "\<And>i. i\<in>I \<Longrightarrow> 0\<le>eps0 i"
    and d1_nn: "\<And>b j. j\<in>J \<Longrightarrow> 0\<le>d1 b j"
    and eps1_nn: "\<And>j. j\<in>J \<Longrightarrow> 0\<le>eps1 j"
    and hd: "\<And>a i. i\<in>I \<Longrightarrow> d1 (e a) (c i)=v (d0 a i)"
    and he: "\<And>i. i\<in>I \<Longrightarrow> eps1 (c i)=v (eps0 i)"
begin
lemma scale_domain_and_boundary_transport:
  "image e (maximal_initial {a. valid I (d0 a) eps0}) = maximal_initial {b. valid J (d1 b) eps1}
   \<and> (\<forall>a. least_pre {x. \<not>valid I (d0 x) eps0} a =
      least_pre {y. \<not>valid J (d1 y) eps1} (e a))
   \<and> (\<forall>a. image c (exceeded I (d0 a) eps0) = exceeded J (d1 (e a)) eps1)"
proof -
  have transport: "\<And>a. data_transport I J c v (d0 a) eps0 (d1 (e a)) eps1"
    by unfold_locales (fact bij_c, fact value_order, fact d0_nn, fact eps0_nn,
      fact d1_nn, fact eps1_nn, fact hd, fact he)
  have valid_iff: "\<And>a. valid I (d0 a) eps0 = valid J (d1 (e a)) eps1"
    by (rule data_transport.validity_under_data_iso[OF transport])
  have valid_image: "image e {a. valid I (d0 a) eps0} = {b. valid J (d1 b) eps1}"
    by (rule image_of_iff[OF bij_e]) (auto simp: valid_iff)
  have fail_image: "image e {a. \<not>valid I (d0 a) eps0} = {b. \<not>valid J (d1 b) eps1}"
    by (rule image_of_iff[OF bij_e]) (auto simp: valid_iff)
  have domain: "image e (maximal_initial {a. valid I (d0 a) eps0}) =
      maximal_initial {b. valid J (d1 b) eps1}"
    using maximal_initial_image[of "{a. valid I (d0 a) eps0}"] valid_image by simp
  have boundary: "\<forall>a. least_pre {x. \<not>valid I (d0 x) eps0} a =
      least_pre {y. \<not>valid J (d1 y) eps1} (e a)"
    using least_image_iff[of "{x. \<not>valid I (d0 x) eps0}"] fail_image by simp
  have exceeded: "\<forall>a. image c (exceeded I (d0 a) eps0) = exceeded J (d1 (e a)) eps1"
    by (intro allI, rule data_transport.exceeded_image[OF transport])
  show ?thesis by (intro conjI; fact)
qed
end

ML \<open>
val roots = @{thms image_of_iff data_transport.validity_under_data_iso
  data_transport.saturation_image data_transport.exceeded_image
  order_transport.initial_image order_transport.maximal_initial_image
  order_transport.least_image_iff order_transport.least_exists_iff
  scale_transport.scale_domain_and_boundary_transport};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
