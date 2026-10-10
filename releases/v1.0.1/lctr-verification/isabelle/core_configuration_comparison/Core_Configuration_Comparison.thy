theory Core_Configuration_Comparison
 imports "LCTR_Core_Comparison_Stage.Core_Comparison_Stage"
 "LCTR_Core_Operational_Configuration.Core_Operational_Configuration"
 "LCTR_Core_Pair_Transport_Factorization.Core_Pair_Transport_Factorization"
begin
locale configuration_comparison_seed =
 fixes raw :: "('z,'s,'t,'l,'c,'d,'o,'m,'v,'rc,'rd,'rb)raw_input"
 and src :: "('cs,'dt,'bt,'cl,'dl,'z,'v,'rc,'rd,'rb)source_data"
 and adm :: "'v\<Rightarrow>'v\<Rightarrow>bool"
 and joint :: "'v\<Rightarrow>'v\<Rightarrow>(bool\<Rightarrow>('rc+'rd))\<Rightarrow>(bool\<Rightarrow>('rc+'rd))\<Rightarrow>bool"
 assumes valid: "valid_configuration(raw,src)"
 and admissible_nodes: "adm u v \<Longrightarrow> u\<in>reception_nodes raw \<and> v\<in>reception_nodes raw"
begin
definition DC where "DC u=(if u\<in>reception_nodes raw then arrival_domain(clock_arrival src u) else {})"
definition DD where "DD u=(if u\<in>reception_nodes raw then arrival_domain(detector_arrival src u) else {})"
definition fC where "fC u=arrival_value(clock_arrival src u)"
definition fD where "fD u=arrival_value(detector_arrival src u)"
definition images where "images u r=(if r then Inr ` (fD u ` DD u) else Inl ` (fC u ` DC u))"
definition L1 where "L1\<longleftrightarrow>(\<forall>u. inj_on(fC u)(DC u) \<and> inj_on(fD u)(DD u))"
definition L2 where "L2\<longleftrightarrow>(L1\<longrightarrow>(\<forall>u v. adm u v\<longrightarrow>
 (\<exists>!p. factorization_valid UNIV (images u)(images v)(joint u v)p)))"
lemma l2_exact:
 "L2\<longleftrightarrow>(L1\<longrightarrow>(\<forall>u v. adm u v\<longrightarrow>
 (\<exists>p. factorization_valid UNIV (images u)(images v)(joint u v)p)))"
 by (simp only: L2_def existence_unique_iff)
definition localRel where "localRel=comparison_relation src"
definition sourceRel where "sourceRel=source_relation src"
lemma relations_preserved:
 "(\<forall>u a. a\<in>localRel u\<longleftrightarrow>a\<in>comparison_relation src u) \<and>
 (\<forall>a. a\<in>sourceRel\<longleftrightarrow>a\<in>source_relation src)"
 by (simp add: localRel_def sourceRel_def)
lemma arrival_preserved:
 "u\<in>reception_nodes raw\<Longrightarrow>
 (DC u=arrival_domain(clock_arrival src u) \<and> fC u=arrival_value(clock_arrival src u)) \<and>
 (DD u=arrival_domain(detector_arrival src u) \<and> fD u=arrival_value(detector_arrival src u))"
 by (simp add: DC_def DD_def fC_def fD_def)
end

locale configuration_comparison = configuration_comparison_seed raw src adm joint
 for raw :: "('z,'s,'t,'l,'c,'d,'o,'m,'v,'rc,'rd,'rb)raw_input"
 and src :: "('cs,'dt,'bt,'cl,'dl,'z,'v,'rc,'rd,'rb)source_data"
 and adm :: "'v\<Rightarrow>'v\<Rightarrow>bool"
 and joint :: "'v\<Rightarrow>'v\<Rightarrow>(bool\<Rightarrow>('rc+'rd))\<Rightarrow>(bool\<Rightarrow>('rc+'rd))\<Rightarrow>bool" +
 assumes l1: L1 and l2: L2
begin
definition factor where "factor u v=(THE p. factorization_valid UNIV (images u)(images v)(joint u v)p)"
lemma factor_valid:
 "adm u v\<Longrightarrow>factorization_valid UNIV (images u)(images v)(joint u v)(factor u v)"
 unfolding factor_def by (rule theI') (use l1 l2 in \<open>auto simp: L2_def\<close>)
lemma joint_graph_exact:
 "adm u v\<Longrightarrow>(joint u v a b\<longleftrightarrow>
 a\<in>fst(factor u v) \<and> b=joint_value UNIV (snd(factor u v)) a)"
 using factor_valid by (auto simp: factorization_valid_def)
lemma transport_partial_injection:
 assumes uv: "adm u v"
 shows "(\<forall>a b c. component(joint u v) r a b\<longrightarrow>component(joint u v) r a c\<longrightarrow>b=c) \<and>
 (\<forall>a b c. component(joint u v) r a c\<longrightarrow>component(joint u v) r b c\<longrightarrow>a=b)"
proof -
 interpret f: pair_factorization UNIV "images u" "images v" "joint u v"
  "fst(factor u v)" "snd(factor u v)"
  by unfold_locales (use factor_valid[OF uv] in simp)
 show ?thesis using f.component_functional[OF UNIV_I] f.component_injective[OF UNIV_I] by blast
qed
definition trC where "trC u v a b=component(joint u v) False (Inl a)(Inl b)"
definition trD where "trD u v a b=component(joint u v) True (Inr a)(Inr b)"
lemma transport_preserved:
 "trC u v a b=component(joint u v) False (Inl a)(Inl b) \<and>
 trD u v d e=component(joint u v) True (Inr d)(Inr e)"
 by (simp add: trC_def trD_def)
sublocale pair: paired_comparison DC fC trC adm DD fD trD adm
proof
 show "inj_on(fC u)(DC u)" for u using l1 by (simp add: L1_def)
next
 fix u v a b c assume uv: "adm u v"
  and a: "a\<in>fC u ` DC u" and b: "b\<in>fC v ` DC v" and c: "c\<in>fC v ` DC v"
  and ab: "trC u v a b" and ac: "trC u v a c"
 show "b=c" using transport_partial_injection[OF uv, where r=False] ab ac unfolding trC_def by blast
next
 fix u v a b c assume uv: "adm u v"
  and a: "a\<in>fC u ` DC u" and b: "b\<in>fC u ` DC u" and c: "c\<in>fC v ` DC v"
  and ac: "trC u v a c" and bc: "trC u v b c"
 show "a=b" using transport_partial_injection[OF uv, where r=False] ac bc unfolding trC_def by blast
next
 show "inj_on(fD u)(DD u)" for u using l1 by (simp add: L1_def)
next
 fix u v a b c assume uv: "adm u v"
  and a: "a\<in>fD u ` DD u" and b: "b\<in>fD v ` DD v" and c: "c\<in>fD v ` DD v"
  and ab: "trD u v a b" and ac: "trD u v a c"
 show "b=c" using transport_partial_injection[OF uv, where r=True] ab ac unfolding trD_def by blast
next
 fix u v a b c assume uv: "adm u v"
  and a: "a\<in>fD u ` DD u" and b: "b\<in>fD u ` DD u" and c: "c\<in>fD v ` DD v"
  and ac: "trD u v a c" and bc: "trD u v b c"
 show "a=b" using transport_partial_injection[OF uv, where r=True] ac bc unfolding trD_def by blast
qed
lemma local_source_compatible:
 assumes a: "a\<in>fC u ` DC u" and b: "b\<in>fD u ` DD u"
 shows "((a,b)\<in>localRel u)\<longleftrightarrow>(recovery DC fC u a,recovery DD fD u b)\<in>sourceRel"
proof -
 obtain c where c: "c\<in>DC u" "fC u c=a" using a by blast
 obtain d where d: "d\<in>DD u" "fD u d=b" using b by blast
 have u: "u\<in>reception_nodes raw" using c(1) by (auto simp: DC_def split: if_splits)
 have ca: "c\<in>arrival_domain(clock_arrival src u)" using c u by (simp add: DC_def)
 have da: "d\<in>arrival_domain(detector_arrival src u)" using d u by (simp add: DD_def)
 have rel: "((c,d)\<in>source_relation src)\<longleftrightarrow>(a,b)\<in>comparison_relation src u"
  using source_comparison_relation_preserved[OF valid, of u c d] u ca da c(2) d(2)
  by (simp add: fC_def fD_def)
 have cr: "recovery DC fC u a=c"
  using recover_arrival[where D=DC and f=fC and u=u and s=c, OF pair.C.local_inj c(1)] c(2) by simp
 have dr: "recovery DD fD u b=d"
  using recover_arrival[where D=DD and f=fD and u=u and s=d, OF pair.D.local_inj d(1)] d(2) by simp
 show ?thesis by (simp add: cr dr localRel_def sourceRel_def rel)
qed
lemma l5_from_configuration: "pair.stage_L5 localRel sourceRel"
proof (unfold pair.stage_L5_def, intro ballI)
 fix p assume p: "p\<in>pair.synchronized"
 have a: "fst(snd p)\<in>fC(fst p) ` DC(fst p)"
 and b: "snd(snd p)\<in>fD(fst p) ` DD(fst p)"
  using p by (auto simp: pair.synchronized_def)
 show "snd p\<in>localRel(fst p)\<longleftrightarrow>
 (recovery DC fC (fst p)(fst(snd p)),recovery DD fD (fst p)(snd(snd p)))\<in>sourceRel"
  using local_source_compatible[OF a b] by simp
qed
definition remaining where "remaining cs ds\<longleftrightarrow>
 pair.stage_L3 cs ds \<and> pair.stage_L4 cs ds \<and> pair.saturated localRel \<and>
 pair.C.irreducible_mixed_identity \<and> pair.D.irreducible_mixed_identity \<and>
 pair.C.pure_loop_identity \<and> pair.D.pure_loop_identity"
lemma remaining_iff_operative:
 "remaining cs ds\<longleftrightarrow>pair.residual_operative cs ds localRel sourceRel"
 by (simp add: remaining_def pair.residual_operative_def l5_from_configuration)
lemma native_output_unique:
 "remaining cs ds\<Longrightarrow>\<exists>!out. pair.valid_output cs ds localRel out"
 by (rule pair.unique_generated_output[where sourceRel=sourceRel])
  (simp add: remaining_iff_operative[symmetric])
lemma native_source_relation_pullback:
 "remaining cs ds\<Longrightarrow>p\<in>pair.synchronized\<Longrightarrow>
 (pair.projection p\<in>quotient_relation(pair.generate cs ds localRel)\<longleftrightarrow>
 (recovery DC fC (fst p)(fst(snd p)),recovery DD fD (fst p)(snd(snd p)))\<in>source_relation src)"
 using pair.generated_source_pullback by (simp add: remaining_iff_operative sourceRel_def)
lemma native_local_injective:
 "remaining cs ds\<Longrightarrow>
 inj_on(\<lambda>p. pair.ceq``{p})(regions DC fC u) \<and>
 inj_on(\<lambda>p. pair.deq``{p})(regions DD fD u)"
 by (rule pair.generated_local_injective[where cs=cs and ds=ds and localRel=localRel and sourceRel=sourceRel])
  (simp add: remaining_iff_operative[symmetric])
end
ML \<open>
val roots = @{thms configuration_comparison_seed.l2_exact configuration_comparison.joint_graph_exact
 configuration_comparison.transport_partial_injection configuration_comparison_seed.arrival_preserved
 configuration_comparison.transport_preserved configuration_comparison_seed.relations_preserved
 configuration_comparison.l5_from_configuration configuration_comparison.remaining_iff_operative
 configuration_comparison.native_output_unique configuration_comparison.native_source_relation_pullback
 configuration_comparison.native_local_injective};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
