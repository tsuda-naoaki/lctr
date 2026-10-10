theory Order_Embedding_Alignment
  imports "LCTR_Order_Embedding_Isabelle.Negative_Cases"
          "LCTR_Order_Embedding_Isabelle.Empty_Carrier_Cases"
begin

lemma alignment_proj_surjective:
  "qproj X r ` X = QuSet X r"
  by (rule qproj_image)

lemma alignment_proj_eq_iff_inc:
  assumes irr: "\<And>x. x\<in>X \<Longrightarrow> \<not>r x x"
    and trans: "inc_trans_on X r" and x: "x\<in>X" and y: "y\<in>X"
  shows "qproj X r x=qproj X r y \<longleftrightarrow> inc_on X r x y"
proof
  assume h: "qproj X r x=qproj X r y"
  have "x\<in>qclass X r x" using x irr unfolding qclass_def inc_on_def by blast
  then have "inc_on X r y x" using h unfolding qproj_def qclass_def by blast
  then show "inc_on X r x y" by (rule inc_on_sym)
next
  assume h: "inc_on X r x y"
  show "qproj X r x=qproj X r y"
    unfolding qproj_def by (rule qclass_eq_if_inc[OF trans h])
qed

lemma alignment_quotientLt_proj_iff:
  "strict_on X r \<Longrightarrow> inc_trans_on X r \<Longrightarrow> x\<in>X \<Longrightarrow> y\<in>X \<Longrightarrow>
    qlt X r (qproj X r x) (qproj X r y) \<longleftrightarrow> r x y"
  by (rule qproj_order_iff)

lemma alignment_quotient_strict_linear_components:
  assumes "strict_on X r" "inc_trans_on X r"
  shows "(\<forall>q\<in>QuSet X r. \<not>qlt X r q q) \<and>
    (\<forall>q0\<in>QuSet X r. \<forall>q1\<in>QuSet X r. \<forall>q2\<in>QuSet X r.
      qlt X r q0 q1 \<longrightarrow> qlt X r q1 q2 \<longrightarrow> qlt X r q0 q2) \<and>
    (\<forall>q0\<in>QuSet X r. \<forall>q1\<in>QuSet X r. q0\<noteq>q1 \<longrightarrow> qlt X r q0 q1 \<or> qlt X r q1 q0)"
  using transitive_incomparability_quotient[OF assms]
  unfolding strict_linear_on_def strict_on_def by blast

lemma alignment_real_order_iff_map_injective:
  assumes s: "strict_on X r" and tr: "inc_trans_on X r"
    and order: "\<forall>x\<in>QuSet X r. \<forall>y\<in>QuSet X r. qlt X r x y \<longleftrightarrow> rho x<(rho y::real)"
  shows "inj_on rho (QuSet X r)"
proof -
  have linear: "strict_linear_on (QuSet X r) (qlt X r)"
    using transitive_incomparability_quotient[OF s tr] by blast
  show ?thesis by (rule guarded_real_order_embedding_inj_on[OF linear order])
qed

lemma alignment_real_embedding_image_inverse_compositions:
  assumes s: "strict_on X r" and tr: "inc_trans_on X r"
    and order: "\<forall>x\<in>QuSet X r. \<forall>y\<in>QuSet X r. qlt X r x y \<longleftrightarrow> rho x<(rho y::real)"
  shows "(\<forall>q\<in>QuSet X r. inv_into (QuSet X r) rho (rho q)=q) \<and>
    (\<forall>t\<in>rho ` QuSet X r. rho (inv_into (QuSet X r) rho t)=t)"
  using image_inverse_contract[OF alignment_real_order_iff_map_injective[OF s tr order]] by blast

lemma alignment_real_embedding_image_inverse_characterization:
  assumes s: "strict_on X r" and tr: "inc_trans_on X r"
    and order: "\<forall>x\<in>QuSet X r. \<forall>y\<in>QuSet X r. qlt X r x y \<longleftrightarrow> rho x<(rho y::real)"
    and t: "t\<in>rho ` QuSet X r" and q: "q\<in>QuSet X r"
  shows "inv_into (QuSet X r) rho t=q \<longleftrightarrow> rho q=t"
  by (rule inverse_characterization_guarded[OF alignment_real_order_iff_map_injective[OF s tr order] t q])

lemma alignment_brokenStrict_irreflexive: "\<forall>x\<in>P3. \<not>edge02 x x"
  using edge02_is_strict_partial_on_P3 unfolding strict_on_def by blast
lemma alignment_brokenStrict_transitive:
  "\<forall>x\<in>P3. \<forall>y\<in>P3. \<forall>z\<in>P3. edge02 x y \<longrightarrow> edge02 y z \<longrightarrow> edge02 x z"
  using edge02_is_strict_partial_on_P3 unfolding strict_on_def by blast
lemma alignment_brokenStrict_incomparability_not_transitive: "\<not>inc_trans_on P3 edge02"
  by (rule edge02_incomparability_not_transitive)

ML \<open>
val roots = @{thms alignment_proj_surjective alignment_proj_eq_iff_inc alignment_quotientLt_proj_iff
  alignment_quotient_strict_linear_components alignment_real_order_iff_map_injective
  alignment_real_embedding_image_inverse_compositions alignment_real_embedding_image_inverse_characterization
  alignment_brokenStrict_irreflexive alignment_brokenStrict_transitive alignment_brokenStrict_incomparability_not_transitive};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
