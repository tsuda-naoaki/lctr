theory Core_Observer_Time
  imports "LCTR_Core_Dynamics_Factors_Alignment.Core_Dynamics_Factors_Alignment"
    "LCTR_Order_Embedding_Isabelle.Order_Embedding_Isabelle"
begin

locale observer_seed =
  fixes C :: "'c set" and D :: "'d set" and B :: "'b set"
    and R :: "('c \<times> 'd \<times> 'b) set"
    and Bind :: "(('c \<times> 'd \<times> 'b) \<times> ('c \<times> 'd \<times> 'b)) set"
    and source_order :: "('c \<times> 'c) set"
begin
definition EC where "EC = least_equiv C (generator_c C D B R Bind)"
definition Time where "Time = C // EC"
definition time_projection where "time_projection x = EC``{x}"
definition time_edges where "time_edges = source_quotient_edges C EC source_order"
definition generated_order where "generated_order = reach_on Time time_edges"
definition strict where "strict x y \<longleftrightarrow> (x,y)\<in>generated_order \<and> x\<noteq>y"
lemma EC_equiv: "equiv C EC"
  unfolding EC_def by (rule least_equiv_equivalence[OF source_generator_carriers(2)])
lemma projection_typed: "x\<in>C \<Longrightarrow> time_projection x\<in>Time"
  unfolding time_projection_def Time_def by (rule quotientI)
lemma projection_kernel:
  "x\<in>C \<Longrightarrow> y\<in>C \<Longrightarrow> (time_projection x=time_projection y \<longleftrightarrow> (x,y)\<in>EC)"
  unfolding time_projection_def using eq_equiv_class_iff[OF EC_equiv] by blast
end

locale observer_time = observer_seed C D B R Bind source_order
  for C :: "'c set" and D :: "'d set" and B :: "'b set"
    and R :: "('c \<times> 'd \<times> 'b) set"
    and Bind :: "(('c \<times> 'd \<times> 'b) \<times> ('c \<times> 'd \<times> 'b)) set"
    and source_order :: "('c \<times> 'c) set" +
  assumes anti: "antisym generated_order"
begin
lemma generated_partial:
  "refl_on Time generated_order \<and> trans generated_order \<and> antisym generated_order"
  using reach_refl[of Time time_edges] reach_trans[of Time time_edges] anti
  unfolding generated_order_def by blast
lemma strict_partial: "strict_on Time strict"
  using generated_partial unfolding strict_on_def strict_def trans_def antisym_def by blast
lemma inc_reflexive_symmetric:
  "(\<forall>x\<in>Time. inc_on Time strict x x) \<and>
   (\<forall>x y. inc_on Time strict x y \<longrightarrow> inc_on Time strict y x)"
  using strict_partial unfolding strict_on_def inc_on_def by blast
end

locale observer_linear = observer_time C D B R Bind source_order
  for C :: "'c set" and D :: "'d set" and B :: "'b set"
    and R :: "('c \<times> 'd \<times> 'b) set"
    and Bind :: "(('c \<times> 'd \<times> 'b) \<times> ('c \<times> 'd \<times> 'b)) set"
    and source_order :: "('c \<times> 'c) set" +
  assumes inc_trans: "inc_trans_on Time strict"
begin
abbreviation OrderTime where "OrderTime \<equiv> QuSet Time strict"
abbreviation order_projection where "order_projection \<equiv> qproj Time strict"
abbreviation order_lt where "order_lt \<equiv> qlt Time strict"
lemma inc_equivalence: "equiv Time {(x,y). inc_on Time strict x y}"
  using inc_reflexive_symmetric inc_trans
  unfolding equiv_def refl_on_def sym_def trans_def inc_trans_on_def inc_on_def by blast
lemma strict_invariance:
  "inc_on Time strict x x' \<Longrightarrow> inc_on Time strict y y' \<Longrightarrow>
   (strict x y \<longleftrightarrow> strict x' y')"
  by (rule lt_invariant_under_inc[OF strict_partial inc_trans])
lemma order_quotient_strict_linear: "strict_linear_on OrderTime order_lt"
  using transitive_incomparability_quotient[OF strict_partial inc_trans] by blast
lemma projection_contract:
  "order_projection`Time = OrderTime \<and>
   (\<forall>x\<in>Time. \<forall>y\<in>Time. (order_projection x=order_projection y \<longleftrightarrow> inc_on Time strict x y)) \<and>
   (\<forall>x\<in>Time. \<forall>y\<in>Time. (order_lt (order_projection x) (order_projection y) \<longleftrightarrow> strict x y))"
  using transitive_incomparability_quotient[OF strict_partial inc_trans] by blast
end

locale observer_real = observer_linear C D B R Bind source_order
  for C :: "'c set" and D :: "'d set" and B :: "'b set"
    and R :: "('c \<times> 'd \<times> 'b) set"
    and Bind :: "(('c \<times> 'd \<times> 'b) \<times> ('c \<times> 'd \<times> 'b)) set"
    and source_order :: "('c \<times> 'c) set" +
  fixes rho :: "'c set set \<Rightarrow> real"
  assumes order_iff: "\<forall>x\<in>OrderTime. \<forall>y\<in>OrderTime. (order_lt x y \<longleftrightarrow> rho x < rho y)"
begin
definition time_rep where "time_rep = rho \<circ> order_projection"
lemma embedding_injective: "inj_on rho OrderTime"
  by (rule guarded_real_order_embedding_inj_on[OF order_quotient_strict_linear order_iff])
lemma image_inverse_contract:
  "(\<forall>q\<in>OrderTime. inv_into OrderTime rho (rho q)=q) \<and>
   (\<forall>t\<in>rho`OrderTime. rho (inv_into OrderTime rho t)=t)"
  by (intro conjI ballI;
    (rule inv_into_f_f[OF embedding_injective] | rule f_inv_into_f); assumption)
lemma real_representation_contract:
  "(\<forall>x\<in>Time. \<forall>y\<in>Time. (time_rep x=time_rep y \<longleftrightarrow> inc_on Time strict x y)) \<and>
   (\<forall>x\<in>Time. \<forall>y\<in>Time. (time_rep x<time_rep y \<longleftrightarrow> strict x y))"
proof -
  have pt: "\<And>x. x\<in>Time \<Longrightarrow> order_projection x\<in>OrderTime"
    unfolding QuSet_def by blast
  have eq: "\<And>x y. x\<in>Time \<Longrightarrow> y\<in>Time \<Longrightarrow>
    (rho (order_projection x)=rho (order_projection y) \<longleftrightarrow> order_projection x=order_projection y)"
    by (rule inj_on_eq_iff[OF embedding_injective pt pt]; assumption)
  show ?thesis
  proof (intro conjI ballI)
    fix x y assume x: "x\<in>Time" and y: "y\<in>Time"
    have ker: "order_projection x=order_projection y \<longleftrightarrow> inc_on Time strict x y"
      by (rule qproj_class_iff[OF strict_partial inc_trans x y])
    show "time_rep x=time_rep y \<longleftrightarrow> inc_on Time strict x y"
      unfolding time_rep_def comp_def using eq[OF x y] ker by blast
  next
    fix x y assume x: "x\<in>Time" and y: "y\<in>Time"
    have emb: "order_lt (order_projection x) (order_projection y) \<longleftrightarrow>
      rho(order_projection x)<rho(order_projection y)"
      by (rule bspec[OF bspec[OF order_iff pt[OF x]] pt[OF y]])
    have ord: "order_lt (order_projection x) (order_projection y) \<longleftrightarrow> strict x y"
      by (rule qproj_order_iff[OF strict_partial inc_trans x y])
    show "time_rep x<time_rep y \<longleftrightarrow> strict x y"
      unfolding time_rep_def comp_def using emb ord by blast
  qed
qed
lemma source_time_representation_contract:
  "(\<forall>x\<in>C. \<forall>y\<in>C. (time_projection x=time_projection y \<longleftrightarrow> (x,y)\<in>EC)) \<and>
   (\<forall>x\<in>C. \<forall>y\<in>C. (time_rep(time_projection x)=time_rep(time_projection y) \<longleftrightarrow>
      inc_on Time strict (time_projection x) (time_projection y))) \<and>
   (\<forall>x\<in>C. \<forall>y\<in>C. (time_rep(time_projection x)<time_rep(time_projection y) \<longleftrightarrow>
      strict (time_projection x) (time_projection y)))"
  using projection_kernel projection_typed real_representation_contract by blast
end

ML \<open>
val roots = @{thms observer_time.generated_partial observer_time.strict_partial
  observer_time.inc_reflexive_symmetric observer_linear.inc_equivalence
  observer_linear.strict_invariance observer_linear.order_quotient_strict_linear
  observer_linear.projection_contract observer_real.embedding_injective
  observer_real.image_inverse_contract observer_real.real_representation_contract
  observer_real.source_time_representation_contract};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
