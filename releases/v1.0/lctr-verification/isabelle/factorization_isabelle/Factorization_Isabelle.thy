theory Factorization_Isabelle
  imports "HOL.Real" "HOL.Hilbert_Choice"
begin











definition eqker_on ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'a) set"
where
  "eqker_on A f =
    {p. fst p \<in> A \<and> snd p \<in> A \<and> f (fst p) = f (snd p)}"

definition factor_choice ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'c"
where
  "factor_choice A pi Phi y =
    Phi (SOME x. x \<in> A \<and> pi x = y)"

lemma projection_surjective_onto_its_image:
  "y \<in> pi ` A \<Longrightarrow> \<exists>x\<in>A. pi x = y"
  by blast

lemma factor_choice_agrees:
  assumes ker: "eqker_on A pi \<subseteq> eqker_on A Phi"
    and xA: "x \<in> A"
  shows "factor_choice A pi Phi (pi x) = Phi x"
proof -
  have ex: "\<exists>u. u \<in> A \<and> pi u = pi x"
    using xA by blast
  have w:
    "(SOME u. u \<in> A \<and> pi u = pi x) \<in> A \<and>
     pi (SOME u. u \<in> A \<and> pi u = pi x) = pi x"
    using someI_ex[OF ex] .
  have pair_pi:
    "((SOME u. u \<in> A \<and> pi u = pi x), x) \<in> eqker_on A pi"
    using w xA unfolding eqker_on_def by auto
  have pair_Phi:
    "((SOME u. u \<in> A \<and> pi u = pi x), x) \<in> eqker_on A Phi"
    using ker pair_pi by blast
  have
    "Phi (SOME u. u \<in> A \<and> pi u = pi x) = Phi x"
    using pair_Phi unfolding eqker_on_def by auto
  then show ?thesis
    unfolding factor_choice_def by simp
qed

theorem surjective_equality_kernel_factorization_on:
  assumes ker: "eqker_on A pi \<subseteq> eqker_on A Phi"
  shows
    "\<exists>g.
       (\<forall>x\<in>A. g (pi x) = Phi x) \<and>
       (\<forall>h.
          (\<forall>x\<in>A. h (pi x) = Phi x) \<longrightarrow>
          (\<forall>y\<in>pi ` A. h y = g y))"
proof
  let ?g = "factor_choice A pi Phi"
  show
    "(\<forall>x\<in>A. ?g (pi x) = Phi x) \<and>
     (\<forall>h.
        (\<forall>x\<in>A. h (pi x) = Phi x) \<longrightarrow>
        (\<forall>y\<in>pi ` A. h y = ?g y))"
  proof
    show "\<forall>x\<in>A. ?g (pi x) = Phi x"
      using factor_choice_agrees[OF ker] by blast
  next
    show
      "\<forall>h.
         (\<forall>x\<in>A. h (pi x) = Phi x) \<longrightarrow>
         (\<forall>y\<in>pi ` A. h y = ?g y)"
    proof (intro allI impI ballI)
      fix h y
      assume hfac: "\<forall>x\<in>A. h (pi x) = Phi x"
        and yimg: "y \<in> pi ` A"
      obtain x where xA: "x \<in> A" and y: "y = pi x"
        using yimg by blast
      have "h (pi x) = Phi x"
        using hfac xA by blast
      moreover have "?g (pi x) = Phi x"
        using factor_choice_agrees[OF ker xA] .
      ultimately show "h y = ?g y"
        using y by simp
    qed
  qed
qed

lemma factor_map_range_on:
  assumes typed: "Phi ` A \<subseteq> Q"
    and fac: "\<forall>x\<in>A. g (pi x) = Phi x"
  shows "g ` (pi ` A) \<subseteq> Q"
proof
  fix z
  assume "z \<in> g ` (pi ` A)"
  then obtain x where xA: "x \<in> A" and z: "z = g (pi x)"
    by blast
  have "Phi x \<in> Q"
    using typed xA by blast
  moreover have "g (pi x) = Phi x"
    using fac xA by blast
  ultimately show "z \<in> Q"
    using z by simp
qed










theorem prop_scalar_time_trajectory_factorization:
  fixes dyn_can inc_trans :: bool
  assumes dyn: dyn_can
    and inc: inc_trans
    and typed: "TrjMap_can ` TrjDom_can \<subseteq> QuB"
    and fact:
      "eqker_on TrjDom_can Prj_ord
       \<subseteq> eqker_on TrjDom_can TrjMap_can"
  shows
    "\<exists>TrjMap_ord.
       TrjMap_ord ` (Prj_ord ` TrjDom_can) \<subseteq> QuB \<and>
       (\<forall>T\<in>TrjDom_can.
          TrjMap_can T = TrjMap_ord (Prj_ord T)) \<and>
       (\<forall>h.
          (\<forall>T\<in>TrjDom_can.
             TrjMap_can T = h (Prj_ord T)) \<longrightarrow>
          (\<forall>q\<in>Prj_ord ` TrjDom_can.
             h q = TrjMap_ord q))"
proof -
  obtain g where
    gfac: "\<forall>T\<in>TrjDom_can. g (Prj_ord T) = TrjMap_can T"
    and guniq:
      "\<forall>h.
         (\<forall>T\<in>TrjDom_can. h (Prj_ord T) = TrjMap_can T) \<longrightarrow>
         (\<forall>q\<in>Prj_ord ` TrjDom_can. h q = g q)"
    using surjective_equality_kernel_factorization_on[OF fact] by blast
  have grange: "g ` (Prj_ord ` TrjDom_can) \<subseteq> QuB"
    using factor_map_range_on[where g=g and pi=Prj_ord and Phi=TrjMap_can and A=TrjDom_can and Q=QuB, OF typed gfac] .
  have fac:
    "\<forall>T\<in>TrjDom_can. TrjMap_can T = g (Prj_ord T)"
    using gfac by auto
  have uniq:
    "\<forall>h.
       (\<forall>T\<in>TrjDom_can. TrjMap_can T = h (Prj_ord T)) \<longrightarrow>
       (\<forall>q\<in>Prj_ord ` TrjDom_can. h q = g q)"
    using guniq by auto
  show ?thesis
    using grange fac uniq by blast
qed

definition strict_linear_on ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "strict_linear_on S r \<longleftrightarrow>
    (\<forall>x\<in>S. \<not> r x x) \<and>
    (\<forall>x\<in>S. \<forall>y\<in>S. \<forall>z\<in>S.
       r x y \<longrightarrow> r y z \<longrightarrow> r x z) \<and>
    (\<forall>x\<in>S. \<forall>y\<in>S.
       x \<noteq> y \<longrightarrow> r x y \<or> r y x)"

definition order_embedding_on ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('a \<Rightarrow> real) \<Rightarrow> bool"
where
  "order_embedding_on S r rho \<longleftrightarrow>
    (\<forall>x\<in>S. \<forall>y\<in>S.
       (r x y \<longleftrightarrow> rho x < rho y))"

lemma order_embedding_on_injective:
  assumes lin: "strict_linear_on S r"
    and emb: "order_embedding_on S r rho"
  shows "inj_on rho S"
  unfolding inj_on_def
proof (intro ballI impI)
  fix x y
  assume xS: "x \<in> S"
    and yS: "y \<in> S"
    and eq: "rho x = rho y"
  show "x = y"
  proof (rule ccontr)
    assume ne: "x \<noteq> y"
    have "r x y \<or> r y x"
      using lin xS yS ne unfolding strict_linear_on_def by blast
    then show False
      using emb xS yS eq unfolding order_embedding_on_def by auto
  qed
qed

definition image_inverse_on ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a"
where
  "image_inverse_on S f y =
    (THE x. x \<in> S \<and> f x = y)"

lemma image_inverse_on_left:
  assumes inj: "inj_on f S"
    and xS: "x \<in> S"
  shows "image_inverse_on S f (f x) = x"
  unfolding image_inverse_on_def
proof (rule the_equality)
  show "x \<in> S \<and> f x = f x"
    using xS by simp
next
  fix y
  assume y: "y \<in> S \<and> f y = f x"
  then show "y = x"
    using inj xS unfolding inj_on_def by blast
qed

lemma image_inverse_on_right:
  assumes inj: "inj_on f S"
    and yimg: "y \<in> f ` S"
  shows
    "image_inverse_on S f y \<in> S \<and>
     f (image_inverse_on S f y) = y"
proof -
  obtain x where xS: "x \<in> S" and y: "y = f x"
    using yimg by blast
  have inv: "image_inverse_on S f (f x) = x"
    using image_inverse_on_left[OF inj xS] .
  show ?thesis
    using xS y inv by simp
qed

lemma image_inverse_from_order_embedding:
  assumes lin: "strict_linear_on S r"
    and emb: "order_embedding_on S r rho"
  shows
    "(\<forall>x\<in>S. image_inverse_on S rho (rho x) = x) \<and>
     (\<forall>t\<in>rho ` S.
        image_inverse_on S rho t \<in> S \<and>
        rho (image_inverse_on S rho t) = t)"
proof -
  have inj: "inj_on rho S"
    using order_embedding_on_injective[OF lin emb] .
  show ?thesis
    using image_inverse_on_left[OF inj]
      image_inverse_on_right[OF inj] by blast
qed














theorem prop_canonical_observable_time_factorization:
  fixes dyn_trj_fact can_obs_desc :: bool
  assumes dyn: dyn_trj_fact
    and obsdesc: can_obs_desc
    and A_C: "TrjDom_can \<subseteq> CanTimeCarrier"
    and S_def: "OrdTimeCarrier = Prj_ord ` CanTimeCarrier"
    and linear: "strict_linear_on OrdTimeCarrier ord_lt"
    and embedding: "order_embedding_on OrdTimeCarrier ord_lt rho"
    and typed: "TrjMap_can ` TrjDom_can \<subseteq> QuB"
    and fact:
      "eqker_on TrjDom_can Prj_ord
       \<subseteq> eqker_on TrjDom_can TrjMap_can"
  shows
    "\<exists>TrjMap_ord ObsCurve_ord ObsCurve_real.
       TrjMap_ord ` (Prj_ord ` TrjDom_can) \<subseteq> QuB \<and>
       (\<forall>T\<in>TrjDom_can.
          TrjMap_can T = TrjMap_ord (Prj_ord T)) \<and>
       (\<forall>ell\<in>ObsIdx.
          \<forall>T\<in>TrjDom_can.
            Obs_can ell (TrjMap_can T) =
            ObsCurve_ord ell (Prj_ord T)) \<and>
       (\<forall>ell\<in>ObsIdx.
          \<forall>T\<in>TrjDom_can.
            ObsCurve_ord ell (Prj_ord T) =
            ObsCurve_real ell (rho (Prj_ord T))) \<and>
       (\<forall>h.
          (\<forall>T\<in>TrjDom_can.
             TrjMap_can T = h (Prj_ord T)) \<longrightarrow>
          (\<forall>q\<in>Prj_ord ` TrjDom_can.
             h q = TrjMap_ord q)) \<and>
       (\<forall>ell\<in>ObsIdx.
          \<forall>h.
            (\<forall>q\<in>Prj_ord ` TrjDom_can.
               h (rho q) = ObsCurve_ord ell q) \<longrightarrow>
            (\<forall>t\<in>rho ` (Prj_ord ` TrjDom_can).
               h t = ObsCurve_real ell t))"
proof -
  obtain g where
    gfac: "\<forall>T\<in>TrjDom_can. g (Prj_ord T) = TrjMap_can T"
    and guniq:
      "\<forall>h.
         (\<forall>T\<in>TrjDom_can. h (Prj_ord T) = TrjMap_can T) \<longrightarrow>
         (\<forall>q\<in>Prj_ord ` TrjDom_can. h q = g q)"
    using surjective_equality_kernel_factorization_on[OF fact] by blast

  have grange: "g ` (Prj_ord ` TrjDom_can) \<subseteq> QuB"
    using factor_map_range_on[where g=g and pi=Prj_ord and Phi=TrjMap_can and A=TrjDom_can and Q=QuB, OF typed gfac] .

  have image_in_S: "Prj_ord ` TrjDom_can \<subseteq> OrdTimeCarrier"
  proof
    fix q
    assume "q \<in> Prj_ord ` TrjDom_can"
    then obtain T where TA: "T \<in> TrjDom_can" and q: "q = Prj_ord T"
      by blast
    have TC: "T \<in> CanTimeCarrier"
      using A_C TA by blast
    have "Prj_ord T \<in> Prj_ord ` CanTimeCarrier"
      using TC by blast
    then show "q \<in> OrdTimeCarrier"
      using S_def q by simp
  qed

  have rho_inj: "inj_on rho OrdTimeCarrier"
    using order_embedding_on_injective[OF linear embedding] .

  let ?ord = "\<lambda>ell q. Obs_can ell (g q)"
  let ?real =
    "\<lambda>ell t. ?ord ell (image_inverse_on OrdTimeCarrier rho t)"

  have first:
    "\<forall>T\<in>TrjDom_can. TrjMap_can T = g (Prj_ord T)"
    using gfac by auto

  have second:
    "\<forall>ell\<in>ObsIdx.
       \<forall>T\<in>TrjDom_can.
         Obs_can ell (TrjMap_can T) = ?ord ell (Prj_ord T)"
    using gfac by simp

  have third:
    "\<forall>ell\<in>ObsIdx.
       \<forall>T\<in>TrjDom_can.
         ?ord ell (Prj_ord T) = ?real ell (rho (Prj_ord T))"
  proof (intro ballI)
    fix ell T
    assume ellL: "ell \<in> ObsIdx"
      and TA: "T \<in> TrjDom_can"
    have qimg: "Prj_ord T \<in> Prj_ord ` TrjDom_can"
      using TA by blast
    have qS: "Prj_ord T \<in> OrdTimeCarrier"
      using image_in_S qimg by blast
    have inv:
      "image_inverse_on OrdTimeCarrier rho (rho (Prj_ord T)) =
       Prj_ord T"
      using image_inverse_on_left[OF rho_inj qS] .
    show "?ord ell (Prj_ord T) = ?real ell (rho (Prj_ord T))"
      using inv by simp
  qed

  have real_unique:
    "\<forall>ell\<in>ObsIdx.
       \<forall>h.
         (\<forall>q\<in>Prj_ord ` TrjDom_can.
            h (rho q) = ?ord ell q) \<longrightarrow>
         (\<forall>t\<in>rho ` (Prj_ord ` TrjDom_can).
            h t = ?real ell t)"
  proof (intro ballI allI impI ballI)
    fix ell h t
    assume ellL: "ell \<in> ObsIdx"
      and hfac:
        "\<forall>q\<in>Prj_ord ` TrjDom_can.
           h (rho q) = ?ord ell q"
      and timg: "t \<in> rho ` (Prj_ord ` TrjDom_can)"
    obtain q where qB: "q \<in> Prj_ord ` TrjDom_can"
      and t: "t = rho q"
      using timg by blast
    have qS: "q \<in> OrdTimeCarrier"
      using image_in_S qB by blast
    have inv: "image_inverse_on OrdTimeCarrier rho (rho q) = q"
      using image_inverse_on_left[OF rho_inj qS] .
    have "h (rho q) = ?ord ell q"
      using hfac qB by blast
    then show "h t = ?real ell t"
      using t inv by simp
  qed

  have uniq:
    "\<forall>h.
       (\<forall>T\<in>TrjDom_can.
          TrjMap_can T = h (Prj_ord T)) \<longrightarrow>
       (\<forall>q\<in>Prj_ord ` TrjDom_can. h q = g q)"
    using guniq by auto

  show ?thesis
    apply (rule exI[of _ g])
    apply (rule exI[of _ ?ord])
    apply (rule exI[of _ ?real])
    using grange first second third uniq real_unique
    by blast
qed

 

lemma empty_actual_trajectory_carrier:
  fixes pi :: "'a \<Rightarrow> 'b"
    and Phi :: "'a \<Rightarrow> 'c"
  shows
    "\<exists>g.
       (\<forall>x\<in>({}::'a set). g (pi x) = Phi x) \<and>
       (\<forall>h.
          (\<forall>x\<in>({}::'a set). h (pi x) = Phi x) \<longrightarrow>
          (\<forall>y\<in>pi ` ({}::'a set). h y = g y))"
  by simp

lemma empty_actual_order_carrier:
  "strict_linear_on ({}::'a set) r \<and>
   order_embedding_on ({}::'a set) r rho"
  unfolding strict_linear_on_def order_embedding_on_def by simp







definition collapse_bool :: "bool \<Rightarrow> bool" where
  "collapse_bool x = False"

lemma negative_without_equality_kernel_condition:
  "\<not> (\<exists>g::bool \<Rightarrow> bool.
          \<forall>x\<in>UNIV. g (collapse_bool x) = x)"
  unfolding collapse_bool_def by auto

definition bool_strict :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "bool_strict x y \<longleftrightarrow> (\<not> x \<and> y)"

definition rho_constant :: "bool \<Rightarrow> real" where
  "rho_constant x = 0"

lemma bool_strict_linear:
  "strict_linear_on UNIV bool_strict"
  unfolding strict_linear_on_def bool_strict_def by auto

lemma negative_without_order_embedding:
  "\<not> (\<exists>inv::real \<Rightarrow> bool.
          \<forall>x\<in>UNIV. inv (rho_constant x) = x)"
  unfolding rho_constant_def by auto

definition no_order :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "no_order x y \<longleftrightarrow> False"

lemma embedding_equivalence_without_linearity_can_be_noninjective:
  "order_embedding_on UNIV no_order rho_constant"
  unfolding order_embedding_on_def no_order_def rho_constant_def by simp

lemma no_order_is_not_strict_linear:
  "\<not> strict_linear_on UNIV no_order"
  unfolding strict_linear_on_def no_order_def by auto

lemma negative_without_linearity:
  "order_embedding_on UNIV no_order rho_constant \<and>
   \<not> (\<exists>inv::real \<Rightarrow> bool.
          \<forall>x\<in>UNIV. inv (rho_constant x) = x)"
  using embedding_equivalence_without_linearity_can_be_noninjective
  unfolding rho_constant_def by auto

end
