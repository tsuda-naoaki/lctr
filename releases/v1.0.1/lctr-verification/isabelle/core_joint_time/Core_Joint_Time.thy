theory Core_Joint_Time
 imports "LCTR_Core_Native_Curves.Core_Native_Curves" "HOL-Library.FuncSet"
begin
locale common_native_time =
 old: observer_linear C D B R0 Bind0 order0 +
 newer: observer_linear C D B R1 Bind1 order1
 for C :: "'c set" and D :: "'d set" and B :: "'b set"
 and R0 :: "('c\<times>'d\<times>'b)set" and R1 :: "('c\<times>'d\<times>'b)set"
 and Bind0 :: "(('c\<times>'d\<times>'b)\<times>('c\<times>'d\<times>'b))set"
 and Bind1 :: "(('c\<times>'d\<times>'b)\<times>('c\<times>'d\<times>'b))set"
 and order0 :: "('c\<times>'c)set" and order1 :: "('c\<times>'c)set" +
 assumes generated_equiv: "old.EC=newer.EC" and same_source: "order0=order1"
begin
definition time_map where "time_map(q::'c set)=q"
definition order_map where "order_map(q::'c set set)=q"
lemma time_setoids_equal: "old.EC=newer.EC" by (rule generated_equiv)
lemma time_quotient_types_equal: "old.Time=newer.Time"
 by (simp add: old.Time_def newer.Time_def generated_equiv)
lemma time_projection_agrees: "time_map(old.time_projection x)=newer.time_projection x"
 by (simp add: time_map_def old.time_projection_def newer.time_projection_def generated_equiv)
lemma time_maps_inverse: "time_map(time_map q)=q"
 by (simp add: time_map_def)
lemma generated_order_equal: "old.generated_order=newer.generated_order"
 using generated_equiv same_source time_quotient_types_equal
 unfolding old.generated_order_def newer.generated_order_def old.time_edges_def newer.time_edges_def by simp
lemma time_order_agrees:
 "(time_map x,time_map y)\<in>newer.generated_order \<longleftrightarrow> (x,y)\<in>old.generated_order"
 by (simp add: time_map_def generated_order_equal)
lemma time_strict_agrees: "newer.strict(time_map x)(time_map y) \<longleftrightarrow> old.strict x y"
 by (simp add: old.strict_def newer.strict_def time_map_def generated_order_equal)
lemma strict_equal: "old.strict=newer.strict"
 using time_strict_agrees unfolding time_map_def by (intro ext) blast
lemma time_incomparability_agrees:
 "inc_on newer.Time newer.strict(time_map x)(time_map y) \<longleftrightarrow> inc_on old.Time old.strict x y"
 by (simp add: time_map_def time_quotient_types_equal strict_equal)
lemma order_carriers_equal: "old.OrderTime=newer.OrderTime"
 by (simp add: time_quotient_types_equal strict_equal)
lemma order_projection_agrees:
 "order_map(old.order_projection x)=newer.order_projection(time_map x)"
 by (simp add: order_map_def time_map_def time_quotient_types_equal strict_equal)
lemma order_maps_inverse: "order_map(order_map q)=q"
 by (simp add: order_map_def)
lemma order_strict_agrees:
 "newer.order_lt(order_map p)(order_map q) \<longleftrightarrow> old.order_lt p q"
 by (simp add: order_map_def time_quotient_types_equal strict_equal)
lemma order_map_unique:
 assumes ext: "f\<in>extensional old.OrderTime"
 and commutes: "\<forall>x\<in>old.Time. f(old.order_projection x)=newer.order_projection(time_map x)"
 shows "f=restrict order_map old.OrderTime"
proof (rule extensionalityI[OF ext restrict_extensional])
 fix q assume q: "q\<in>old.OrderTime"
 obtain x where x: "x\<in>old.Time" and qx: "q=old.order_projection x"
  using conjunct1[OF old.projection_contract] q by blast
 show "f q=restrict order_map old.OrderTime q"
  using bspec[OF commutes x] order_projection_agrees[of x] q qx by simp
qed
lemma embedding_transfers:
 assumes rho: "\<forall>x\<in>newer.OrderTime. \<forall>y\<in>newer.OrderTime.
  (newer.order_lt x y \<longleftrightarrow> (rho::'c set set\<Rightarrow>real)x<rho y)"
 shows "\<exists>sigma. (\<forall>x\<in>old.OrderTime. \<forall>y\<in>old.OrderTime.
  (old.order_lt x y \<longleftrightarrow> sigma x<sigma y)) \<and>
  (\<forall>q\<in>old.OrderTime. sigma q=rho(order_map q))"
 using rho order_strict_agrees order_carriers_equal unfolding order_map_def by auto
end

locale native_joint_curves =
 fixes C :: "'c set" and D :: "'d set" and B :: "'b set" and J :: "'i set" and base :: "'i"
 and R :: "'i\<Rightarrow>('c\<times>'d\<times>'b)set"
 and Bind :: "'i\<Rightarrow>(('c\<times>'d\<times>'b)\<times>('c\<times>'d\<times>'b))set"
 and source_order :: "'i\<Rightarrow>('c\<times>'c)set"
 assumes base_member: "base\<in>J"
 and linear: "\<And>i. i\<in>J \<Longrightarrow> observer_linear C D B (R i)(Bind i)(source_order i)"
 and single: "\<And>i t s s'. i\<in>J \<Longrightarrow>
  (t,s)\<in>observer_seed.trajectory_rel C D B (R i)(Bind i) \<Longrightarrow>
  (t,s')\<in>observer_seed.trajectory_rel C D B (R i)(Bind i) \<Longrightarrow> s=s'"
 and fiber: "\<And>i. i\<in>J \<Longrightarrow> observer_seed.fiber_condition C D B (R i)(Bind i)(source_order i)"
 and common: "\<And>i j. i\<in>J \<Longrightarrow> j\<in>J \<Longrightarrow>
  observer_seed.EC C D B (R i)(Bind i)=observer_seed.EC C D B (R j)(Bind j)"
 and source: "\<And>i j. i\<in>J \<Longrightarrow> j\<in>J \<Longrightarrow> source_order i=source_order j"
begin
definition individual_domain where
 "individual_domain i=observer_seed.order_domain C D B (R i)(Bind i)(source_order i)"
definition individual_curve where
 "individual_curve i=observer_seed.scalar_trajectory C D B (R i)(Bind i)(source_order i)"
definition common_domain where "common_domain={q. \<forall>i\<in>J. q\<in>individual_domain i}"
definition joint_curve where
 "joint_curve=restrict(\<lambda>q. restrict(\<lambda>i. individual_curve i q)J)common_domain"
definition relation_pullback where
 "relation_pullback V r={(q,v). q\<in>common_domain \<and> v\<in>V \<and> (joint_curve q,v)\<in>r}"
lemma individual_curve_typed:
 assumes i: "i\<in>J" and q: "q\<in>individual_domain i"
 shows "individual_curve i q\<in>observer_seed.State C D B (R i)(Bind i)"
proof -
 interpret obj: observer_seed C D B "R i" "Bind i" "source_order i" .
 obtain t where t: "t\<in>obj.trajectory_domain" and qt: "q=obj.restricted_projection t"
  using q unfolding individual_domain_def obj.order_domain_def by blast
 have factor: "obj.canonical_trajectory t=obj.scalar_trajectory(obj.restricted_projection t)"
  using bspec[OF conjunct1[OF obj.scalar_factor_contract[OF fiber[OF i]]] t] .
 have typed: "obj.canonical_trajectory t\<in>obj.State"
  using obj.trajectory_map_typed t by blast
 show ?thesis using factor typed qt unfolding individual_curve_def by simp
qed
lemma joint_curve_typed:
 "q\<in>common_domain \<Longrightarrow> joint_curve q\<in>PiE J (\<lambda>i. observer_seed.State C D B (R i)(Bind i))"
 unfolding joint_curve_def
 using individual_curve_typed by (auto simp: PiE_iff common_domain_def)
lemma native_joint_components:
 "q\<in>common_domain \<Longrightarrow> i\<in>J \<Longrightarrow> joint_curve q i=individual_curve i q"
 by (simp add: joint_curve_def)
lemma native_joint_unique:
 assumes outer: "g\<in>extensional common_domain"
 and inner: "\<And>q. q\<in>common_domain \<Longrightarrow> g q\<in>extensional J"
 and components: "\<And>q i. q\<in>common_domain \<Longrightarrow> i\<in>J \<Longrightarrow> g q i=individual_curve i q"
 shows "g=joint_curve"
proof (rule extensionalityI[OF outer])
 show "joint_curve\<in>extensional common_domain" by (simp add: joint_curve_def)
 fix q assume q: "q\<in>common_domain"
 show "g q=joint_curve q"
  using inner[OF q] components[OF q] q
  unfolding joint_curve_def by (intro extensionalityI[where A=J]) auto
qed
lemma joint_relation_on_actual_states:
 "q\<in>common_domain \<Longrightarrow> v\<in>V \<Longrightarrow>
  ((q,v)\<in>relation_pullback V r \<longleftrightarrow> (joint_curve q,v)\<in>r)"
 by (simp add: relation_pullback_def)
end
ML \<open>
val roots = @{thms common_native_time.time_setoids_equal common_native_time.time_quotient_types_equal
 common_native_time.time_projection_agrees common_native_time.time_maps_inverse
 common_native_time.time_order_agrees common_native_time.time_strict_agrees
 common_native_time.time_incomparability_agrees common_native_time.order_projection_agrees
 common_native_time.order_maps_inverse common_native_time.order_strict_agrees
 common_native_time.order_map_unique common_native_time.embedding_transfers
 native_joint_curves.native_joint_components native_joint_curves.native_joint_unique
 native_joint_curves.joint_relation_on_actual_states};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
