theory Factorization_Alignment
  imports "LCTR_Factorization_Isabelle.Factorization_Isabelle"
          "LCTR_Order_Embedding_Alignment.Order_Embedding_Alignment"
begin

definition selected_factor where "selected_factor A pi Phi = factor_choice A pi Phi"
definition selected_ord_curve where "selected_ord_curve A pi Phi Obs q = Obs (selected_factor A pi Phi q)"
definition selected_real_curve where
  "selected_real_curve A pi Phi Obs rho t = selected_ord_curve A pi Phi Obs (inv_into (pi ` A) rho t)"

lemma alignment_restrictedProjection_surjective: "y\<in>pi ` A \<Longrightarrow> \<exists>x\<in>A. pi x=y"
  by (rule projection_surjective_onto_its_image)
lemma alignment_selectedOrderTrajectory_factorization:
  "eqker_on A pi\<subseteq>eqker_on A Phi \<Longrightarrow> x\<in>A \<Longrightarrow> Phi x=selected_factor A pi Phi (pi x)"
  unfolding selected_factor_def using factor_choice_agrees by metis
lemma alignment_selectedOrderTrajectory_unique:
  assumes ker: "eqker_on A pi\<subseteq>eqker_on A Phi"
    and h: "\<forall>x\<in>A. Phi x=h (pi x)" and y: "y\<in>pi ` A"
  shows "h y=selected_factor A pi Phi y"
proof -
  obtain x where x: "x\<in>A" and eq: "y=pi x" using y by blast
  show ?thesis using h x alignment_selectedOrderTrajectory_factorization[OF ker x] eq by auto
qed
lemma alignment_scalar_time_trajectory_factorization_adapter:
  assumes ker: "eqker_on A pi\<subseteq>eqker_on A Phi"
  shows "\<exists>g. (\<forall>x\<in>A. Phi x=g (pi x)) \<and>
    (\<forall>h. (\<forall>x\<in>A. Phi x=h (pi x)) \<longrightarrow> (\<forall>y\<in>pi ` A. h y=g y))"
  using surjective_equality_kernel_factorization_on[OF ker] by metis

lemma alignment_rho_injective_from_ordEmbSet:
  assumes tri: "\<forall>x\<in>S. \<forall>y\<in>S. x=y \<or> r x y \<or> r y x"
    and emb: "\<forall>x\<in>S. \<forall>y\<in>S. r x y \<longleftrightarrow> rho x<(rho y::real)"
  shows "inj_on rho S"
  unfolding inj_on_def using tri emb by fastforce
lemma alignment_restrictedEmbedding_surjective:
  "t\<in>rho ` (pi ` A) \<Longrightarrow> \<exists>q\<in>pi ` A. rho q=t"
  by blast
lemma alignment_realImageInverse_left:
  "inj_on rho S \<Longrightarrow> pi ` A\<subseteq>S \<Longrightarrow> q\<in>pi ` A \<Longrightarrow>
    inv_into (pi ` A) rho (rho q)=q"
  by (meson inj_on_subset inv_into_f_f)
lemma alignment_realImageInverse_right:
  "t\<in>rho ` (pi ` A) \<Longrightarrow> inv_into (pi ` A) rho t\<in>pi ` A \<and>
    rho (inv_into (pi ` A) rho t)=t"
  by (simp add: inv_into_into f_inv_into_f)

definition observable_factorization_contract where
  "observable_factorization_contract A pi Phi Obs rho \<longleftrightarrow>
    (\<forall>x\<in>A. Phi x=selected_factor A pi Phi (pi x)) \<and>
    (\<forall>x\<in>A. Obs (Phi x)=selected_ord_curve A pi Phi Obs (pi x)) \<and>
    (\<forall>x\<in>A. selected_ord_curve A pi Phi Obs (pi x)=selected_real_curve A pi Phi Obs rho (rho (pi x))) \<and>
    (\<forall>h. (\<forall>q\<in>pi ` A. h (rho q)=selected_ord_curve A pi Phi Obs q) \<longrightarrow>
      (\<forall>t\<in>rho ` (pi ` A). h t=selected_real_curve A pi Phi Obs rho t))"

lemma observable_factorization_from_injective:
  assumes ker: "eqker_on A pi\<subseteq>eqker_on A Phi" and inj: "inj_on rho S" and sub: "pi ` A\<subseteq>S"
  shows "observable_factorization_contract A pi Phi Obs rho"
proof -
  have fac: "\<forall>x\<in>A. Phi x=selected_factor A pi Phi (pi x)"
    using alignment_selectedOrderTrajectory_factorization[OF ker] by blast
  have inv: "\<And>q. q\<in>pi ` A \<Longrightarrow> inv_into (pi ` A) rho (rho q)=q"
    by (rule alignment_realImageInverse_left[OF inj sub])
  have obs: "\<forall>x\<in>A. Obs (Phi x)=selected_ord_curve A pi Phi Obs (pi x)"
    using fac unfolding selected_ord_curve_def by simp
  have time: "\<forall>x\<in>A. selected_ord_curve A pi Phi Obs (pi x)=selected_real_curve A pi Phi Obs rho (rho (pi x))"
    using inv unfolding selected_real_curve_def by simp
  have unique: "\<forall>h. (\<forall>q\<in>pi ` A. h (rho q)=selected_ord_curve A pi Phi Obs q) \<longrightarrow>
      (\<forall>t\<in>rho ` (pi ` A). h t=selected_real_curve A pi Phi Obs rho t)"
  proof (intro allI impI ballI)
    fix h t assume h: "\<forall>q\<in>pi ` A. h (rho q)=selected_ord_curve A pi Phi Obs q"
      and t: "t\<in>rho ` (pi ` A)"
    obtain q where q: "q\<in>pi ` A" and eq: "t=rho q" using t by blast
    have hq: "h (rho q)=selected_ord_curve A pi Phi Obs q" using h q by blast
    show "h t=selected_real_curve A pi Phi Obs rho t"
      using hq inv[OF q] eq unfolding selected_real_curve_def by simp
  qed
  show ?thesis using fac obs time unique unfolding observable_factorization_contract_def by blast
qed

lemma alignment_canonical_observable_time_factorization_adapter:
  assumes ker: "eqker_on A pi\<subseteq>eqker_on A Phi" and sub: "pi ` A\<subseteq>S"
    and tri: "\<forall>x\<in>S. \<forall>y\<in>S. x=y \<or> r x y \<or> r y x"
    and emb: "\<forall>x\<in>S. \<forall>y\<in>S. r x y \<longleftrightarrow> rho x<(rho y::real)"
  shows "observable_factorization_contract A pi Phi Obs rho"
  by (rule observable_factorization_from_injective[OF ker alignment_rho_injective_from_ordEmbSet[OF tri emb] sub])
lemma alignment_empty_canonical_carrier_supported:
  "\<exists>g. (\<forall>x\<in>{}. Phi x=g (pi x)) \<and>
    (\<forall>h. (\<forall>x\<in>{}. Phi x=h (pi x)) \<longrightarrow> (\<forall>y\<in>pi ` {}. h y=g y))"
  by simp
lemma alignment_quotient_trichotomy_from_order_embedding_bridge:
  "Order_Embedding_Isabelle.strict_on X r \<Longrightarrow> inc_trans_on X r \<Longrightarrow>
    \<forall>x\<in>QuSet X r. \<forall>y\<in>QuSet X r. x=y \<or> qlt X r x y \<or> qlt X r y x"
  using alignment_quotient_strict_linear_components by blast
lemma alignment_canonical_observable_time_factorization_paper_wrapper:
  assumes s: "Order_Embedding_Isabelle.strict_on X r" and tr: "inc_trans_on X r"
    and sub: "A\<subseteq>X" and ker: "eqker_on A (qproj X r)\<subseteq>eqker_on A Phi"
    and emb: "\<forall>x\<in>QuSet X r. \<forall>y\<in>QuSet X r. qlt X r x y \<longleftrightarrow> rho x<(rho y::real)"
  shows "observable_factorization_contract A (qproj X r) Phi Obs rho"
proof -
  have img: "qproj X r ` A\<subseteq>QuSet X r" using sub unfolding QuSet_def by blast
  show ?thesis by (rule alignment_canonical_observable_time_factorization_adapter[OF ker img
      alignment_quotient_trichotomy_from_order_embedding_bridge[OF s tr] emb])
qed
lemma alignment_no_factor_without_equality_kernel:
  "\<not>(\<exists>f::unit\<Rightarrow>bool. \<forall>b. b=f ())"
  by auto
lemma alignment_no_left_inverse_without_embedding_injectivity:
  "\<not>(\<exists>f::unit\<Rightarrow>bool. \<forall>b. f ()=b)"
  by auto

lemma selected_factor_carrier:
  assumes ker: "eqker_on A pi\<subseteq>eqker_on A Phi" and typed: "Phi ` A\<subseteq>Q"
  shows "selected_factor A pi Phi ` (pi ` A)\<subseteq>Q"
  using alignment_selectedOrderTrajectory_factorization[OF ker] typed by force

ML \<open>
val roots = @{thms alignment_restrictedProjection_surjective alignment_scalar_time_trajectory_factorization_adapter
  alignment_selectedOrderTrajectory_factorization alignment_selectedOrderTrajectory_unique
  alignment_rho_injective_from_ordEmbSet alignment_restrictedEmbedding_surjective alignment_realImageInverse_left
  alignment_realImageInverse_right alignment_canonical_observable_time_factorization_adapter
  alignment_empty_canonical_carrier_supported alignment_quotient_trichotomy_from_order_embedding_bridge
  alignment_canonical_observable_time_factorization_paper_wrapper alignment_no_factor_without_equality_kernel
  alignment_no_left_inverse_without_embedding_injectivity};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
