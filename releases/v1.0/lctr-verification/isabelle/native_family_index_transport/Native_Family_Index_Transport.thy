theory Native_Family_Index_Transport
  imports "LCTR_Native_Family_Projection.Native_Family_Projection"
begin

locale nonempty_index_fibres =
  fixes Reps :: "'r set" and Fib :: "'r \<Rightarrow> 'i set"
  assumes nonempty: "\<And>rho. rho\<in>Reps \<Longrightarrow> Fib rho \<noteq> {}"
begin
definition select_index where
  "select_index rho u = (if u\<in>Fib rho then u else (SOME x. x\<in>Fib rho))"

lemma select_fixed:
  "u\<in>Fib rho \<Longrightarrow> select_index rho u = u"
  by (simp add: select_index_def)

lemma select_in:
  assumes rep: "rho\<in>Reps"
  shows "select_index rho u\<in>Fib rho"
proof -
  have ex: "\<exists>x. x\<in>Fib rho" using nonempty[OF rep] by blast
  have chosen: "(SOME x. x\<in>Fib rho)\<in>Fib rho" by (rule someI_ex[OF ex])
  show ?thesis by (simp add: select_index_def chosen)
qed

lemma select_image:
  assumes rep: "rho\<in>Reps"
  shows "image (select_index rho) UNIV = Fib rho"
proof (rule equalityI)
  show "image (select_index rho) UNIV \<subseteq> Fib rho"
    by (rule image_subsetI; rule select_in[OF rep])
  show "Fib rho \<subseteq> image (select_index rho) UNIV"
  proof
    fix x assume hx: "x\<in>Fib rho"
    have eq: "select_index rho x = x" by (rule select_fixed[OF hx])
    show "x\<in>image (select_index rho) UNIV"
      by (rule image_eqI[where x=x]) (simp_all only: eq UNIV_I)
  qed
qed

lemma forall_exact:
  assumes rep: "rho\<in>Reps"
  shows "(\<forall>alpha\<in>Fib rho. P alpha) \<longleftrightarrow> (\<forall>u. P (select_index rho u))"
proof
  assume h: "\<forall>alpha\<in>Fib rho. P alpha"
  show "\<forall>u. P (select_index rho u)"
    by (intro allI; rule bspec[OF h select_in[OF rep]])
next
  assume h: "\<forall>u. P (select_index rho u)"
  show "\<forall>alpha\<in>Fib rho. P alpha"
  proof (intro ballI)
    fix alpha assume ha: "alpha\<in>Fib rho"
    have "P (select_index rho alpha)" by (rule spec[OF h])
    then show "P alpha" by (simp only: select_fixed[OF ha])
  qed
qed

lemma exists_exact:
  assumes rep: "rho\<in>Reps"
  shows "(\<exists>alpha\<in>Fib rho. P alpha) \<longleftrightarrow> (\<exists>u. P (select_index rho u))"
proof
  assume "\<exists>alpha\<in>Fib rho. P alpha"
  then obtain alpha where ha: "alpha\<in>Fib rho" and hp: "P alpha" by blast
  have "P (select_index rho alpha)" using hp by (simp only: select_fixed[OF ha])
  then show "\<exists>u. P (select_index rho u)" by (rule exI)
next
  assume "\<exists>u. P (select_index rho u)"
  then obtain u where hp: "P (select_index rho u)" by blast
  show "\<exists>alpha\<in>Fib rho. P alpha"
    by (rule bexI[where x="select_index rho u"]) (rule hp, rule select_in[OF rep])
qed

lemma two_indices_exact:
  assumes r: "rho\<in>Reps" and s: "other\<in>Reps"
  shows "(\<forall>alpha\<in>Fib rho. \<forall>delta\<in>Fib other. P alpha delta) \<longleftrightarrow>
    (\<forall>u v. P (select_index rho u) (select_index other v))"
proof
  assume h: "\<forall>alpha\<in>Fib rho. \<forall>delta\<in>Fib other. P alpha delta"
  show "\<forall>u v. P (select_index rho u) (select_index other v)"
  proof (intro allI)
    fix u v
    have inner: "\<forall>delta\<in>Fib other. P (select_index rho u) delta"
      by (rule bspec[OF h select_in[OF r]])
    show "P (select_index rho u) (select_index other v)"
      by (rule bspec[OF inner select_in[OF s]])
  qed
next
  assume h: "\<forall>u v. P (select_index rho u) (select_index other v)"
  show "\<forall>alpha\<in>Fib rho. \<forall>delta\<in>Fib other. P alpha delta"
  proof (intro ballI)
    fix alpha delta assume ha: "alpha\<in>Fib rho" and hd: "delta\<in>Fib other"
    have "P (select_index rho alpha) (select_index other delta)" by (rule spec[OF spec[OF h]])
    then show "P alpha delta" by (simp only: select_fixed[OF ha] select_fixed[OF hd])
  qed
qed
end

locale native_family_fibre_atlas =
  generated_law_representations C D B R Bind source_order rho0 d
  for C :: "'c set" and D :: "'d set" and B :: "'b set"
    and R :: "('c \<times> 'd \<times> 'b) set"
    and Bind :: "(('c \<times> 'd \<times> 'b) \<times> ('c \<times> 'd \<times> 'b)) set"
    and source_order :: "('c \<times> 'c) set" and rho0 :: "'c set set \<Rightarrow> real"
    and d :: "(real,'a,'x,'y) law_family" +
  fixes a :: 'a and k :: nat
    and Fib :: "('c set set \<Rightarrow> real) \<Rightarrow> 'ti set"
    and TD TT :: "('c set set \<Rightarrow> real) \<Rightarrow> 'ti \<Rightarrow> real set"
    and tc :: "('c set set \<Rightarrow> real) \<Rightarrow> 'ti \<Rightarrow> real \<Rightarrow> real"
    and ID :: "'bi \<Rightarrow> 'x set" and IT :: "'bi \<Rightarrow> 'e::real_normed_vector set"
    and ic :: "'bi \<Rightarrow> 'x \<Rightarrow> 'e"
    and OD :: "'bo \<Rightarrow> 'y set" and OT :: "'bo \<Rightarrow> 'f::real_normed_vector set"
    and oc :: "'bo \<Rightarrow> 'y \<Rightarrow> 'f"
  assumes fibre_nonempty: "\<And>rho. rho\<in>Reps \<Longrightarrow> Fib rho \<noteq> {}"
    and component_index: "a\<in>law_indices d"
    and positive_order: "0<k"
    and time_charts: "\<And>rho alpha. rho\<in>Reps \<Longrightarrow> alpha\<in>Fib rho \<Longrightarrow>
      bij_betw (tc rho alpha) (TD rho alpha) (TT rho alpha)"
    and time_domains: "\<And>rho alpha. rho\<in>Reps \<Longrightarrow> alpha\<in>Fib rho \<Longrightarrow>
      TD rho alpha\<subseteq>eval_at rho a"
    and input_charts: "\<And>beta. bij_betw (ic beta) (ID beta) (IT beta)"
    and output_charts: "\<And>gamma. bij_betw (oc gamma) (OD gamma) (OT gamma)"
    and time_open: "\<And>rho alpha. rho\<in>Reps \<Longrightarrow> alpha\<in>Fib rho \<Longrightarrow> open (TT rho alpha)"
    and input_open: "\<And>beta. open (IT beta)"
    and output_open: "\<And>gamma. open (OT gamma)"
    and covered: "\<And>rho t. rho\<in>Reps \<Longrightarrow> t\<in>eval_at rho a \<Longrightarrow>
      \<exists>alpha\<in>Fib rho. \<exists>beta gamma.
        t\<in>TD rho alpha \<and> input_at rho a t\<in>ID beta \<and> output_at rho a t\<in>OD gamma"
begin
sublocale indices: nonempty_index_fibres Reps Fib
  by unfold_locales (rule fibre_nonempty)

definition total_domain where "total_domain rho u = TD rho (indices.select_index rho u)"
definition total_target where "total_target rho u = TT rho (indices.select_index rho u)"
definition total_coordinate where "total_coordinate rho u = tc rho (indices.select_index rho u)"

lemma total_coverage:
  assumes rep: "rho\<in>Reps" and t: "t\<in>eval_at rho a"
  shows "\<exists>u beta gamma. t\<in>total_domain rho u \<and>
    input_at rho a t\<in>ID beta \<and> output_at rho a t\<in>OD gamma"
proof -
  obtain alpha beta gamma where
    idx: "alpha\<in>Fib rho" and body:
      "t\<in>TD rho alpha \<and> input_at rho a t\<in>ID beta \<and> output_at rho a t\<in>OD gamma"
    using covered[OF rep t] by blast
  have "t\<in>total_domain rho alpha \<and> input_at rho a t\<in>ID beta \<and> output_at rho a t\<in>OD gamma"
    using body by (simp add: total_domain_def indices.select_fixed[OF idx])
  then show ?thesis by blast
qed

sublocale total: native_family_component_atlas
  C D B R Bind source_order rho0 d a k total_domain total_target total_coordinate ID IT ic OD OT oc
proof unfold_locales
  show "a\<in>law_indices d" by (rule component_index)
  show "0<k" by (rule positive_order)
  show "\<And>rho alpha. rho\<in>Reps \<Longrightarrow>
    bij_betw (total_coordinate rho alpha) (total_domain rho alpha) (total_target rho alpha)"
    unfolding total_coordinate_def total_domain_def total_target_def
    by (rule time_charts; assumption?; rule indices.select_in; assumption)
  show "\<And>rho alpha. rho\<in>Reps \<Longrightarrow> total_domain rho alpha\<subseteq>eval_at rho a"
    unfolding total_domain_def
    by (rule time_domains; assumption?; rule indices.select_in; assumption)
  show "\<And>beta. bij_betw (ic beta) (ID beta) (IT beta)" by (rule input_charts)
  show "\<And>gamma. bij_betw (oc gamma) (OD gamma) (OT gamma)" by (rule output_charts)
  show "\<And>rho alpha. rho\<in>Reps \<Longrightarrow> open (total_target rho alpha)"
    unfolding total_target_def by (rule time_open; assumption?; rule indices.select_in; assumption)
  show "\<And>beta. open (IT beta)" by (rule input_open)
  show "\<And>gamma. open (OT gamma)" by (rule output_open)
  show "\<And>rho t. rho\<in>Reps \<Longrightarrow> t\<in>eval_at rho a \<Longrightarrow>
    \<exists>alpha beta gamma. t\<in>total_domain rho alpha \<and>
      input_at rho a t\<in>ID beta \<and> output_at rho a t\<in>OD gamma"
    by (rule total_coverage)
qed

lemma original_chart_unchanged:
  "alpha\<in>Fib rho \<Longrightarrow>
    total_domain rho alpha = TD rho alpha \<and> total_target rho alpha = TT rho alpha \<and>
    total_coordinate rho alpha = tc rho alpha"
  by (simp add: total_domain_def total_target_def total_coordinate_def indices.select_fixed)

lemma total_joint_exact:
  "total.Joint rho u beta gamma =
    {t\<in>TD rho (indices.select_index rho u).
      input_at rho a t\<in>ID beta \<and> output_at rho a t\<in>OD gamma}"
  by (simp add: total.Joint_def total_domain_def)

lemma total_curve_exact:
  "total.Curve rho u beta gamma theta =
    (ic beta (input_at rho a (inv_into
      {t\<in>TD rho (indices.select_index rho u).
        input_at rho a t\<in>ID beta \<and> output_at rho a t\<in>OD gamma}
      (tc rho (indices.select_index rho u)) theta)),
     oc gamma (output_at rho a (inv_into
      {t\<in>TD rho (indices.select_index rho u).
        input_at rho a t\<in>ID beta \<and> output_at rho a t\<in>OD gamma}
      (tc rho (indices.select_index rho u)) theta)))"
  by (simp add: total.Curve_def total_joint_exact total_coordinate_def)

lemma actual_totalized_atlas:
  "rho\<in>Reps \<Longrightarrow> native_product_atlas
    (total_target rho) (total_domain rho) (total_coordinate rho) IT ID ic OT OD oc"
  by (rule total.actual_product_atlas)

lemma actual_totalized_values:
  "rho\<in>Reps \<Longrightarrow> t\<in>total.Joint rho u beta gamma \<Longrightarrow>
    total.Curve rho u beta gamma (total_coordinate rho u t) =
      (ic beta (input_value (component_at rho a) t),
       oc gamma (output_value (component_at rho a) t))"
  by (rule total.actual_coordinate_values)
end

ML \<open>
val roots = @{thms nonempty_index_fibres.select_fixed nonempty_index_fibres.select_in
  nonempty_index_fibres.select_image nonempty_index_fibres.forall_exact
  nonempty_index_fibres.exists_exact nonempty_index_fibres.two_indices_exact
  native_family_fibre_atlas.total_coverage native_family_fibre_atlas.original_chart_unchanged
  native_family_fibre_atlas.total_joint_exact native_family_fibre_atlas.total_curve_exact
  native_family_fibre_atlas.actual_totalized_atlas native_family_fibre_atlas.actual_totalized_values};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
