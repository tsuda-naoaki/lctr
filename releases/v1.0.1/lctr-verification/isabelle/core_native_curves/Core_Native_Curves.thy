theory Core_Native_Curves
  imports "LCTR_Core_Observer_Time.Core_Observer_Time"
begin
context observer_seed
begin
definition EB where "EB = least_equiv B (generator_b C D B R Bind)"
definition State where "State = B//EB"
definition trajectory_rel where "trajectory_rel = image_rel EC EB (source_rel C D B R)"
definition trajectory_domain where "trajectory_domain = Domain trajectory_rel"
definition canonical_trajectory where "canonical_trajectory = graph_map trajectory_rel"
definition restricted_projection where "restricted_projection = qproj Time strict"
definition order_domain where "order_domain = restricted_projection`trajectory_domain"
definition fiber_condition where
  "fiber_condition \<longleftrightarrow> eqker_on trajectory_domain restricted_projection
    \<subseteq> eqker_on trajectory_domain canonical_trajectory"
definition scalar_trajectory where
  "scalar_trajectory = factor_choice trajectory_domain restricted_projection canonical_trajectory"
definition order_curve where "order_curve obs = obs \<circ> scalar_trajectory"

lemma trajectory_typed: "trajectory_rel \<subseteq> Time \<times> State"
  unfolding trajectory_rel_def image_rel_def source_rel_def Time_def State_def quotient_def by auto
lemma domain_typed: "trajectory_domain \<subseteq> Time"
  using trajectory_typed unfolding trajectory_domain_def by auto
lemma trajectory_member:
  "t\<in>trajectory_domain \<Longrightarrow> (t,canonical_trajectory t)\<in>trajectory_rel"
  unfolding canonical_trajectory_def trajectory_domain_def by (rule graph_map_member)
lemma trajectory_map_typed: "canonical_trajectory`trajectory_domain \<subseteq> State"
  using trajectory_typed trajectory_member by blast

lemma canonical_graph_contract:
  assumes single: "\<And>t s s'. (t,s)\<in>trajectory_rel \<Longrightarrow> (t,s')\<in>trajectory_rel \<Longrightarrow> s=s'"
  shows "(\<forall>t\<in>trajectory_domain. \<forall>s. ((t,s)\<in>trajectory_rel \<longleftrightarrow> s=canonical_trajectory t)) \<and>
    (\<forall>other. (\<forall>t\<in>trajectory_domain. \<forall>s. ((t,s)\<in>trajectory_rel \<longleftrightarrow> s=other t))
       \<longrightarrow> (\<forall>t\<in>trajectory_domain. other t=canonical_trajectory t))"
proof -
  have exact: "\<And>t s. t\<in>trajectory_domain \<Longrightarrow>
    ((t,s)\<in>trajectory_rel \<longleftrightarrow> s=canonical_trajectory t)"
    using single trajectory_member by blast
  show ?thesis using exact by blast
qed

lemma scalar_factor_contract:
  assumes k: fiber_condition
  shows "(\<forall>x\<in>trajectory_domain. canonical_trajectory x=scalar_trajectory (restricted_projection x)) \<and>
    (\<forall>other. (\<forall>x\<in>trajectory_domain. canonical_trajectory x=other (restricted_projection x))
       \<longrightarrow> (\<forall>q\<in>order_domain. other q=scalar_trajectory q))"
proof -
  have commute: "\<And>x. x\<in>trajectory_domain \<Longrightarrow>
    scalar_trajectory (restricted_projection x)=canonical_trajectory x"
    unfolding scalar_trajectory_def
    by (rule factor_choice_agrees[OF k[unfolded fiber_condition_def]])
  have unique: "\<And>other q. (\<forall>x\<in>trajectory_domain. canonical_trajectory x=other (restricted_projection x))
      \<Longrightarrow> q\<in>order_domain \<Longrightarrow> other q=scalar_trajectory q"
  proof -
    fix other q
    assume h: "\<forall>x\<in>trajectory_domain. canonical_trajectory x=other (restricted_projection x)"
      and q: "q\<in>order_domain"
    obtain x where x: "x\<in>trajectory_domain" and qx: "q=restricted_projection x"
      using q unfolding order_domain_def by blast
    show "other q=scalar_trajectory q" using bspec[OF h x] commute[OF x] qx by simp
  qed
  show ?thesis using commute unique by blast
qed
lemma scalar_factor_exists_unique:
  assumes k: fiber_condition
  shows "\<exists>f. f`order_domain\<subseteq>State \<and>
    (\<forall>x\<in>trajectory_domain. canonical_trajectory x=f (restricted_projection x)) \<and>
    (\<forall>other. (\<forall>x\<in>trajectory_domain. canonical_trajectory x=other (restricted_projection x))
       \<longrightarrow> (\<forall>q\<in>order_domain. other q=f q))"
proof -
  have contract: "(\<forall>x\<in>trajectory_domain. canonical_trajectory x=scalar_trajectory (restricted_projection x)) \<and>
    (\<forall>other. (\<forall>x\<in>trajectory_domain. canonical_trajectory x=other (restricted_projection x))
       \<longrightarrow> (\<forall>q\<in>order_domain. other q=scalar_trajectory q))"
    by (rule scalar_factor_contract[OF k])
  have typed: "scalar_trajectory`order_domain\<subseteq>State"
    using trajectory_map_typed contract unfolding order_domain_def by auto
  show ?thesis using typed contract by blast
qed
lemma scalar_factor_requires_fiber:
  assumes commutes: "\<forall>x\<in>trajectory_domain. canonical_trajectory x=f (restricted_projection x)"
  shows fiber_condition
  using commutes unfolding fiber_condition_def eqker_on_def by auto
lemma empty_source_domain:
  assumes empty: "\<And>c d b. c\<in>C \<Longrightarrow> d\<in>D \<Longrightarrow> b\<in>B \<Longrightarrow> (c,d,b)\<notin>R"
  shows "trajectory_domain={}"
  using empty unfolding trajectory_domain_def trajectory_rel_def image_rel_def source_rel_def by auto
end

context observer_linear
begin
lemma restricted_projection_contract:
  "restricted_projection`trajectory_domain=order_domain \<and>
   (\<forall>x\<in>trajectory_domain. \<forall>y\<in>trajectory_domain.
     (restricted_projection x=restricted_projection y \<longleftrightarrow> inc_on Time strict x y))"
  unfolding order_domain_def restricted_projection_def
  using qproj_class_iff[OF strict_partial inc_trans] domain_typed by blast
lemma order_domain_typed: "order_domain \<subseteq> OrderTime"
  unfolding order_domain_def restricted_projection_def QuSet_def
  by (rule image_mono[OF domain_typed])
end

context observer_real
begin
definition real_domain where "real_domain = rho`order_domain"
definition real_inverse where "real_inverse = inv_into order_domain rho"
definition real_curve where "real_curve obs = order_curve obs \<circ> real_inverse"
lemma restricted_embedding_injective: "inj_on rho order_domain"
  by (rule inj_on_subset[OF embedding_injective order_domain_typed])
lemma real_image_inverse_contract:
  "rho`order_domain=real_domain \<and>
   (\<forall>q\<in>order_domain. real_inverse (rho q)=q) \<and>
   (\<forall>t\<in>real_domain. real_inverse t\<in>order_domain \<and> rho(real_inverse t)=t)"
  unfolding real_domain_def real_inverse_def
  by (intro conjI ballI; (rule refl | rule inv_into_f_f[OF restricted_embedding_injective]
    | rule inv_into_into | rule f_inv_into_f); assumption)
lemma real_domain_composition: "real_domain = time_rep`trajectory_domain"
  unfolding real_domain_def order_domain_def time_rep_def restricted_projection_def
  by (simp add: image_image image_comp)
lemma real_inverse_left:
  "q\<in>order_domain \<Longrightarrow> real_inverse(rho q)=q"
  unfolding real_inverse_def by (rule inv_into_f_f[OF restricted_embedding_injective])
lemma observable_factorization:
  assumes k: fiber_condition
  shows "(\<forall>x\<in>trajectory_domain.
    obs(canonical_trajectory x)=order_curve obs (restricted_projection x) \<and>
    order_curve obs (restricted_projection x)=real_curve obs (rho(restricted_projection x))) \<and>
   (\<forall>other. (\<forall>q\<in>order_domain. other(rho q)=order_curve obs q) \<longrightarrow>
    (\<forall>t\<in>real_domain. other t=real_curve obs t))"
proof -
  have commute: "\<And>x. x\<in>trajectory_domain \<Longrightarrow>
    canonical_trajectory x=scalar_trajectory(restricted_projection x)"
    using scalar_factor_contract[OF k] by blast
  have first: "\<And>x. x\<in>trajectory_domain \<Longrightarrow>
    obs(canonical_trajectory x)=order_curve obs(restricted_projection x)"
    unfolding order_curve_def comp_def using commute by simp
  have second: "\<And>x. x\<in>trajectory_domain \<Longrightarrow>
    order_curve obs(restricted_projection x)=real_curve obs(rho(restricted_projection x))"
  proof -
    fix x assume x: "x\<in>trajectory_domain"
    have p: "restricted_projection x\<in>order_domain" unfolding order_domain_def by (rule imageI[OF x])
    show "order_curve obs(restricted_projection x)=real_curve obs(rho(restricted_projection x))"
      unfolding real_curve_def comp_def by (simp only: real_inverse_left[OF p])
  qed
  have unique: "\<And>other t. (\<forall>q\<in>order_domain. other(rho q)=order_curve obs q) \<Longrightarrow>
     t\<in>real_domain \<Longrightarrow> other t=real_curve obs t"
  proof -
    fix other t
    assume h: "\<forall>q\<in>order_domain. other(rho q)=order_curve obs q" and t: "t\<in>real_domain"
    obtain q where q: "q\<in>order_domain" and tq: "t=rho q" using t unfolding real_domain_def by blast
    show "other t=real_curve obs t" unfolding tq real_curve_def comp_def
      using bspec[OF h q] real_inverse_left[OF q] by simp
  qed
  show ?thesis using first second unique by blast
qed
lemma observable_curve_unique_from_canonical:
  assumes k: fiber_condition
    and commutes: "\<forall>x\<in>trajectory_domain. other(rho(restricted_projection x))=obs(canonical_trajectory x)"
  shows "\<forall>t\<in>real_domain. other t=real_curve obs t"
proof -
  have order_commute: "\<forall>q\<in>order_domain. other(rho q)=order_curve obs q"
  proof (intro ballI)
    fix q assume q: "q\<in>order_domain"
    obtain x where x: "x\<in>trajectory_domain" and qx: "q=restricted_projection x"
      using q unfolding order_domain_def by blast
    have fac: "obs(canonical_trajectory x)=order_curve obs(restricted_projection x)"
      using bspec[OF conjunct1[OF observable_factorization[OF k]] x] by blast
    show "other(rho q)=order_curve obs q" using bspec[OF commutes x] fac qx by simp
  qed
  show ?thesis using conjunct2[OF observable_factorization[OF k]] order_commute by blast
qed
end

ML \<open>
val roots = @{thms observer_seed.canonical_graph_contract observer_linear.restricted_projection_contract
 observer_seed.scalar_factor_exists_unique observer_seed.scalar_factor_contract
 observer_seed.scalar_factor_requires_fiber observer_real.real_image_inverse_contract
 observer_real.real_domain_composition observer_real.observable_factorization
 observer_real.observable_curve_unique_from_canonical observer_seed.empty_source_domain};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
