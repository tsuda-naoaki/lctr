theory Core_Law_Differential_Bundle
  imports "LCTR_Core_Dynamics_Bundle.Core_Dynamics_Bundle"
    "LCTR_Core_Native_Law_Generation.Core_Native_Law_Generation"
begin
record ('ord,'t,'s,'i,'v,'a) differential_foundation =
  df_embedding :: "'ord\<Rightarrow>real"
  df_representation :: "'t\<Rightarrow>real"
  df_scalar :: "'ord\<Rightarrow>'s"
  df_curves :: "('i\<times>real)\<Rightarrow>'v"
  df_candidate :: "(real,'a,('i\<Rightarrow>'v),('i\<Rightarrow>'v))law_family"
  df_faithful :: "('a\<Rightarrow>((real\<times>('i\<Rightarrow>'v))\<times>('i\<Rightarrow>'v))carrier_reindex)\<Rightarrow>bool"
context native_dynamics_bundle
begin
sublocale law: native_law_context C D B R Bind source_order rho Q obs.canonical_range obs.canonical
  by (unfold_locales; use single fiber canonical_value_typed in blast)
definition candidates where "candidates Jlaw a allowed faithful=law.native_family Jlaw a allowed faithful"
definition core_specification where
  "core_specification Jlaw a allowed faithful x \<longleftrightarrow>
    description_specification(fst x) \<and> snd x=candidates Jlaw a allowed faithful"
lemma law_core_exists_unique: "\<exists>!x. core_specification Jlaw a allowed faithful x"
proof (rule ex1I[where a="(description,candidates Jlaw a allowed faithful)"])
  show "core_specification Jlaw a allowed faithful (description,candidates Jlaw a allowed faithful)"
    using description_spec unfolding core_specification_def by simp
  fix x assume h: "core_specification Jlaw a allowed faithful x"
  have first: "fst x=description" by (rule description_unique) (use h in \<open>simp add: core_specification_def\<close>)
  show "x=(description,candidates Jlaw a allowed faithful)"
    using h first unfolding core_specification_def by (cases x) simp
qed
lemma law_core_validity:
  "all_conditions(candidates Jlaw a allowed faithful) \<Longrightarrow>
    all_conditions(candidates Jlaw a allowed faithful) \<and>
    common_times(candidates Jlaw a allowed faithful)\<noteq>{} \<and>
    allowed(common_times(candidates Jlaw a allowed faithful))"
  by (simp add: all_conditions_def K5_def candidates_def law.native_family_def)
lemma law_core_same_source:
  assumes valid: "t\<in>common_times(candidates Jlaw a allowed faithful)"
  shows "\<exists>x\<in>trajectory_domain. rho(restricted_projection x)=t \<and>
    (\<forall>j\<in>Jlaw. t\<in>evaluation_times(a j) \<and>
      law.evaluation_tuple(a j)t=
        ((t,restrict(\<lambda>i. obs.canonical i(bundle_trajectory(fst description)x))(in_indices(a j))),
         restrict(\<lambda>i. obs.canonical i(bundle_trajectory(fst description)x))(out_indices(a j))) \<and>
      law.evaluation_tuple(a j)t\<in>candidate_relation(a j))"
  using law.common_evaluation_source_values[OF valid[unfolded candidates_def]]
  unfolding description_def law_input_def by simp

definition differential where
  "differential Jlaw a allowed faithful=\<lparr>df_embedding=restrict rho OrderTime,
    df_representation=restrict time_rep Time, df_scalar=restrict scalar_trajectory order_domain,
    df_curves=restrict(\<lambda>p. real_curve(obs.canonical(fst p))(snd p))(Q\<times>real_domain),
    df_candidate=candidates Jlaw a allowed faithful,df_faithful=faithful\<rparr>"
definition differential_specification where
  "differential_specification Jlaw a allowed faithful
      (x::('c set set,'c set,'b set,'i,'v,'j)differential_foundation) \<longleftrightarrow>
    df_embedding x=restrict rho OrderTime \<and>
    df_representation x\<in>extensional Time \<and> df_scalar x\<in>extensional order_domain \<and>
    df_curves x\<in>extensional(Q\<times>real_domain) \<and>
    (\<forall>q\<in>Time. df_representation x q=df_embedding x(restricted_projection q)) \<and>
    (\<forall>t\<in>trajectory_domain. canonical_trajectory t=df_scalar x(restricted_projection t)) \<and>
    (\<forall>i\<in>Q. \<forall>t\<in>trajectory_domain.
      df_curves x(i,rho(restricted_projection t))=obs.canonical i(canonical_trajectory t)) \<and>
    df_candidate x=candidates Jlaw a allowed faithful \<and>
    df_faithful x=faithful_family(df_candidate x)"

lemma differential_spec: "differential_specification Jlaw a allowed faithful(differential Jlaw a allowed faithful)"
proof -
  have fac: "\<And>i t. t\<in>trajectory_domain \<Longrightarrow>
    real_curve(obs.canonical i)(rho(restricted_projection t))=obs.canonical i(canonical_trajectory t)"
  proof -
    fix i t assume t: "t\<in>trajectory_domain"
    show "real_curve(obs.canonical i)(rho(restricted_projection t))=obs.canonical i(canonical_trajectory t)"
      using bspec[OF conjunct1[OF observable_factorization[OF fiber, of "obs.canonical i"]] t] by simp
  qed
  have scalar: "\<And>t. t\<in>trajectory_domain \<Longrightarrow> canonical_trajectory t=scalar_trajectory(restricted_projection t)"
    using conjunct1[OF scalar_factor_contract[OF fiber]] by blast
  have proj: "\<And>t. t\<in>trajectory_domain \<Longrightarrow> restricted_projection t\<in>order_domain"
    unfolding order_domain_def by blast
  have img: "\<And>t. t\<in>trajectory_domain \<Longrightarrow> rho(restricted_projection t)\<in>real_domain"
    using proj unfolding real_domain_def by blast
  show ?thesis using fac scalar proj img projection_typed
    unfolding differential_specification_def differential_def candidates_def law.native_family_def
      time_rep_def restricted_projection_def by auto
qed
lemma differential_unique:
  assumes h: "differential_specification Jlaw a allowed faithful x"
  shows "x=differential Jlaw a allowed faithful"
proof -
  have repr: "\<And>q. q\<in>Time \<Longrightarrow> df_representation x q=time_rep q"
    using h projection_typed unfolding differential_specification_def time_rep_def restricted_projection_def by simp
  have fact: "\<forall>t\<in>trajectory_domain. canonical_trajectory t=df_scalar x(restricted_projection t)"
    using h unfolding differential_specification_def by blast
  have scalar: "\<forall>q\<in>order_domain. df_scalar x q=scalar_trajectory q"
    by (rule mp[OF HOL.spec[OF conjunct2[OF scalar_factor_contract[OF fiber]]] fact])
  have curves: "\<And>i t. i\<in>Q \<Longrightarrow> t\<in>real_domain \<Longrightarrow>
    df_curves x(i,t)=real_curve(obs.canonical i)t"
  proof -
    fix i t assume i: "i\<in>Q" and t: "t\<in>real_domain"
    have agrees: "\<forall>r\<in>trajectory_domain.
      df_curves x(i,rho(restricted_projection r))=obs.canonical i(canonical_trajectory r)"
      using h i unfolding differential_specification_def by blast
    have unique: "\<forall>t\<in>real_domain. df_curves x(i,t)=real_curve(obs.canonical i)t"
      by (rule observable_curve_unique_from_canonical[OF fiber agrees])
    show "df_curves x(i,t)=real_curve(obs.canonical i)t" by (rule bspec[OF unique t])
  qed
  have er: "df_representation x=restrict time_rep Time"
    using h repr unfolding differential_specification_def
    by (intro extensionalityI[where A=Time]) auto
  have es: "df_scalar x=restrict scalar_trajectory order_domain"
    using h scalar unfolding differential_specification_def
    by (intro extensionalityI[where A=order_domain]) auto
  have ec: "df_curves x=restrict(\<lambda>p. real_curve(obs.canonical(fst p))(snd p))(Q\<times>real_domain)"
    using h curves unfolding differential_specification_def
    by (intro extensionalityI[where A="Q\<times>real_domain"]) auto
  have ef: "df_faithful x=faithful"
    using h unfolding differential_specification_def candidates_def law.native_family_def by simp
  show ?thesis using h er es ec ef unfolding differential_specification_def differential_def by (cases x) auto
qed
lemma differential_exists_unique: "\<exists>!x. differential_specification Jlaw a allowed faithful x"
  by (rule ex1I[where a="differential Jlaw a allowed faithful"])
    (rule differential_spec, rule differential_unique, assumption)
lemma differential_with_law_conditions:
  assumes all: "all_conditions(candidates Jlaw a allowed faithful)"
  shows "\<exists>!x. differential_specification Jlaw a allowed faithful x \<and> all_conditions(df_candidate x)"
proof (rule ex1I[where a="differential Jlaw a allowed faithful"])
  show "differential_specification Jlaw a allowed faithful(differential Jlaw a allowed faithful) \<and>
    all_conditions(df_candidate(differential Jlaw a allowed faithful))"
    using differential_spec all unfolding differential_def by simp
  fix x assume h: "differential_specification Jlaw a allowed faithful x \<and> all_conditions(df_candidate x)"
  show "x=differential Jlaw a allowed faithful" by (rule differential_unique) (use h in blast)
qed
lemma differential_same_dynamics:
  "df_embedding(differential Jlaw a allowed faithful)=td_embedding(fst(snd description)) \<and>
    df_representation(differential Jlaw a allowed faithful)=td_representation(fst(snd description)) \<and>
    df_scalar(differential Jlaw a allowed faithful)=tr_scalar(snd(snd description)) \<and>
    df_curves(differential Jlaw a allowed faithful)=tr_real_curve(snd(snd description))"
  by (simp add: differential_def description_def time_data_def trajectory_data_def)
lemma typed_law_curve_agrees:
  "i\<in>Q \<Longrightarrow> t\<in>real_domain \<Longrightarrow>
    law.curve i t=df_curves(differential Jlaw a allowed faithful)(i,t)"
  by (simp add: law.curve_def differential_def)
lemma differential_curve_typed:
  "i\<in>Q \<Longrightarrow> t\<in>real_domain \<Longrightarrow>
    df_curves(differential Jlaw a allowed faithful)(i,t)\<in>obs.canonical_range i"
  using law.curve_typed[of i t] typed_law_curve_agrees[of i t Jlaw a allowed faithful] by simp
end
ML \<open>
val roots = @{thms native_dynamics_bundle.law_core_exists_unique native_dynamics_bundle.law_core_validity
 native_dynamics_bundle.law_core_same_source native_dynamics_bundle.differential_spec
 native_dynamics_bundle.differential_unique native_dynamics_bundle.differential_exists_unique
 native_dynamics_bundle.differential_with_law_conditions native_dynamics_bundle.differential_same_dynamics
 native_dynamics_bundle.typed_law_curve_agrees native_dynamics_bundle.differential_curve_typed};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
