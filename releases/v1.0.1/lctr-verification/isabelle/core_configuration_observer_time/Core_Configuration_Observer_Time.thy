theory Core_Configuration_Observer_Time
 imports "LCTR_Core_Configuration_Dynamics.Core_Configuration_Dynamics"
 "LCTR_Core_Observer_Time.Core_Observer_Time"
begin
fun pack_source where
 "pack_source c d b SClock=Inl c"
| "pack_source c d b SDetector=Inr(Inl d)"
| "pack_source c d b SBody=Inr(Inr b)"
definition source_tuples where
 "source_tuples src = (\<lambda>(c,d,b). pack_source c d b) `
 ((clock_sources src\<times>UNIV)\<times>detector_tokens src\<times>body_tokens src)"
definition unpack_source where
 "unpack_source p=(case p SClock of Inl c \<Rightarrow> c | _ \<Rightarrow> undefined,
 case p SDetector of Inr(Inl d) \<Rightarrow> d | _ \<Rightarrow> undefined,
 case p SBody of Inr(Inr b) \<Rightarrow> b | _ \<Rightarrow> undefined)"
lemma unpack_pack[simp]: "unpack_source(pack_source c d b)=(c,d,b)"
 by (simp add: unpack_source_def)
lemma pack_roundtrip:
 "p\<in>source_tuples src \<Longrightarrow>
 pack_source (fst(unpack_source p)) (fst(snd(unpack_source p))) (snd(snd(unpack_source p)))=p"
 by (auto simp: source_tuples_def)

locale configuration_observer = configuration_dynamics raw src node
 for raw :: "('z,'s,'t,'l,'c,'d,'o,'m,'v,'rc,'rd,'rb)raw_input"
 and src :: "('cs,'dt,'bt,'cl,'dl,'z,'v,'rc,'rd,'rb)source_data" and node :: 'v +
 fixes R :: "(source_role\<Rightarrow>('cs clock_token+('dt+'bt)))set"
 and L :: "(source_role\<Rightarrow>('rc+('rd+'rb)))set"
 and bind :: "(source_role\<Rightarrow>('rc+('rd+'rb)))\<Rightarrow>(source_role\<Rightarrow>('rc+('rd+'rb)))\<Rightarrow>bool"
 assumes relation_typed: "R\<subseteq>source_tuples src"
 and local_typed: "L\<subseteq>received_tuples"
begin
abbreviation C where "C\<equiv>clock_sources src\<times>UNIV"
abbreviation D where "D\<equiv>detector_tokens src"
abbreviation B where "B\<equiv>body_tokens src"
definition Relation where "Relation=unpack_source ` R"
definition Binding where
 "Binding={(p,q). source_binding L bind (pack_source (fst p)(fst(snd p))(snd(snd p)))
  (pack_source (fst q)(fst(snd q))(snd(snd q)))}"
definition source_clock_order where "source_clock_order={(c,c'). clock_order src c c'}"
lemma relation_carrier: "Relation\<subseteq>C\<times>D\<times>B"
 using relation_typed by (auto simp: Relation_def source_tuples_def)
lemma relation_membership:
 "(c,d,b)\<in>Relation \<longleftrightarrow> c\<in>C \<and> d\<in>D \<and> b\<in>B \<and> pack_source c d b\<in>R"
proof
 assume "(c,d,b)\<in>Relation"
 then obtain p where p: "p\<in>R" "unpack_source p=(c,d,b)" by (auto simp: Relation_def)
 have pc: "p\<in>source_tuples src" using relation_typed p by blast
 then obtain c' d' b' where q: "c'\<in>C" "d'\<in>D" "b'\<in>B" "p=pack_source c' d' b'"
  unfolding source_tuples_def by auto
 show "c\<in>C \<and> d\<in>D \<and> b\<in>B \<and> pack_source c d b\<in>R" using p q by auto
next
 assume h: "c\<in>C \<and> d\<in>D \<and> b\<in>B \<and> pack_source c d b\<in>R"
 have "unpack_source(pack_source c d b)\<in>unpack_source ` R" using h by blast
 then show "(c,d,b)\<in>Relation" by (simp add: Relation_def)
qed
lemma tuple_cases:
 "p\<in>R \<Longrightarrow> \<exists>c\<in>C. \<exists>d\<in>D. \<exists>b\<in>B. p=pack_source c d b"
proof -
 assume p: "p\<in>R"
 have "p\<in>source_tuples src" using relation_typed p by blast
 then obtain c d b where "c\<in>C" "d\<in>D" "b\<in>B" "p=pack_source c d b"
  unfolding source_tuples_def by auto
 then show ?thesis by blast
qed
lemma generated_packed:
 "generated R L bind r s t \<longleftrightarrow>
 (\<exists>c\<in>C. \<exists>d\<in>D. \<exists>b\<in>B. \<exists>c'\<in>C. \<exists>d'\<in>D. \<exists>b'\<in>B.
 pack_source c d b\<in>R \<and> pack_source c' d' b'\<in>R \<and>
 source_binding L bind (pack_source c d b)(pack_source c' d' b') \<and>
 pack_source c d b r=s \<and> pack_source c' d' b' r=t)"
proof
 assume "generated R L bind r s t"
 then obtain p q where h: "p\<in>R" "q\<in>R" "source_binding L bind p q" "p r=s" "q r=t"
  by (auto simp: generated_def)
 obtain c d b where p: "c\<in>C" "d\<in>D" "b\<in>B" "p=pack_source c d b"
  using tuple_cases[OF h(1)] by blast
 obtain c' d' b' where q: "c'\<in>C" "d'\<in>D" "b'\<in>B" "q=pack_source c' d' b'"
  using tuple_cases[OF h(2)] by blast
 show "\<exists>c\<in>C. \<exists>d\<in>D. \<exists>b\<in>B. \<exists>c'\<in>C. \<exists>d'\<in>D. \<exists>b'\<in>B.
 pack_source c d b\<in>R \<and> pack_source c' d' b'\<in>R \<and>
 source_binding L bind (pack_source c d b)(pack_source c' d' b') \<and>
 pack_source c d b r=s \<and> pack_source c' d' b' r=t" using h p q by blast
next
 assume "\<exists>c\<in>C. \<exists>d\<in>D. \<exists>b\<in>B. \<exists>c'\<in>C. \<exists>d'\<in>D. \<exists>b'\<in>B.
 pack_source c d b\<in>R \<and> pack_source c' d' b'\<in>R \<and>
 source_binding L bind (pack_source c d b)(pack_source c' d' b') \<and>
 pack_source c d b r=s \<and> pack_source c' d' b' r=t"
 then show "generated R L bind r s t" unfolding generated_def by blast
qed
lemma clock_generator_exact:
 "generator_c C D B Relation Binding =
 {(s,t). generated R L bind SClock (Inl s)(Inl t)}"
 by (auto simp: generator_c_def Binding_def generated_packed relation_membership; blast)
lemma body_generator_exact:
 "generator_b C D B Relation Binding =
 {(s,t). generated R L bind SBody (Inr(Inr s))(Inr(Inr t))}"
 by (auto simp: generator_b_def Binding_def generated_packed relation_membership; blast)
sublocale seed: observer_seed C D B Relation Binding source_clock_order .
lemma clock_quotient_kernel:
 "s\<in>C \<Longrightarrow> t\<in>C \<Longrightarrow> (seed.time_projection s=seed.time_projection t \<longleftrightarrow>
 (s,t)\<in>least_equiv C {(s,t). generated R L bind SClock (Inl s)(Inl t)})"
 using seed.projection_kernel by (simp only: seed.EC_def clock_generator_exact)
lemma body_quotient_kernel:
 assumes s: "s\<in>B" and t: "t\<in>B"
 shows "(least_equiv B (generator_b C D B Relation Binding)``{s}=
 least_equiv B (generator_b C D B Relation Binding)``{t}) \<longleftrightarrow>
 (s,t)\<in>least_equiv B {(s,t). generated R L bind SBody (Inr(Inr s))(Inr(Inr t))}"
proof -
 have e: "equiv B (least_equiv B (generator_b C D B Relation Binding))"
  by (rule least_equiv_equivalence[OF source_generator_carriers(3)])
 show ?thesis using eq_equiv_class_iff[OF e s t] by (simp only: body_generator_exact)
qed
lemma source_trajectory_exact:
 "(c,b)\<in>source_rel C D B Relation \<longleftrightarrow>
 (\<exists>p\<in>R. p SClock=Inl c \<and> p SBody=Inr(Inr b))"
proof
 assume "(c,b)\<in>source_rel C D B Relation"
 then obtain d where h: "c\<in>C" "d\<in>D" "b\<in>B" "pack_source c d b\<in>R"
  by (auto simp: source_rel_def relation_membership)
 have "pack_source c d b SClock=Inl c \<and> pack_source c d b SBody=Inr(Inr b)" by simp
 then show "\<exists>p\<in>R. p SClock=Inl c \<and> p SBody=Inr(Inr b)" using h(4) by blast
next
 assume "\<exists>p\<in>R. p SClock=Inl c \<and> p SBody=Inr(Inr b)"
 then obtain p where h: "p\<in>R" "p SClock=Inl c" "p SBody=Inr(Inr b)" by blast
 obtain c' d b' where q: "c'\<in>C" "d\<in>D" "b'\<in>B" "p=pack_source c' d b'"
  using tuple_cases[OF h(1)] by blast
 have eq: "c'=c" "b'=b" using h q(4) by auto
 have "(c,d,b)\<in>Relation" using h(1) q eq by (simp add: relation_membership)
 then show "(c,b)\<in>source_rel C D B Relation" using q eq by (auto simp: source_rel_def)
qed
lemma observer_source_order_step:
 assumes s: "s\<in>C" and t: "t\<in>C" and ord: "clock_order src s t"
 shows "(seed.time_projection s,seed.time_projection t)\<in>seed.generated_order"
 unfolding seed.time_projection_def seed.generated_order_def seed.time_edges_def seed.Time_def
 by (rule canonical_source_order_preserved[OF s t])
  (use ord in \<open>simp add: source_clock_order_def\<close>)
lemma observer_partial_order:
 "antisym seed.generated_order \<Longrightarrow>
 refl_on seed.Time seed.generated_order \<and> trans seed.generated_order \<and> antisym seed.generated_order"
proof -
 assume anti: "antisym seed.generated_order"
 interpret time: observer_time C D B Relation Binding source_clock_order
  by unfold_locales (rule anti)
 show ?thesis by (rule time.generated_partial)
qed
lemma real_time_source_contract:
 fixes rho :: "'cs clock_token set set\<Rightarrow>real"
 assumes anti: "antisym seed.generated_order"
 and inc: "inc_trans_on seed.Time seed.strict"
 and emb: "\<forall>x\<in>QuSet seed.Time seed.strict. \<forall>y\<in>QuSet seed.Time seed.strict.
 qlt seed.Time seed.strict x y \<longleftrightarrow> rho x<rho y"
 shows "(\<forall>s\<in>C. \<forall>t\<in>C. seed.time_projection s=seed.time_projection t \<longleftrightarrow>
 (s,t)\<in>least_equiv C {(s,t). generated R L bind SClock (Inl s)(Inl t)}) \<and>
 (\<forall>s\<in>C. \<forall>t\<in>C.
 (rho(qproj seed.Time seed.strict (seed.time_projection s))=
 rho(qproj seed.Time seed.strict (seed.time_projection t)) \<longleftrightarrow>
 inc_on seed.Time seed.strict (seed.time_projection s)(seed.time_projection t))) \<and>
 (\<forall>s\<in>C. \<forall>t\<in>C.
 (rho(qproj seed.Time seed.strict (seed.time_projection s))<
 rho(qproj seed.Time seed.strict (seed.time_projection t)) \<longleftrightarrow>
 seed.strict (seed.time_projection s)(seed.time_projection t)))"
proof -
 interpret time: observer_real C D B Relation Binding source_clock_order rho
  by unfold_locales (rule anti, rule inc, rule emb)
 show ?thesis using time.source_time_representation_contract
  by (simp only: time.time_rep_def comp_def seed.EC_def clock_generator_exact)
qed
end
ML \<open>
val roots = @{thms pack_roundtrip configuration_observer.clock_generator_exact
 configuration_observer.body_generator_exact configuration_observer.clock_quotient_kernel
 configuration_observer.body_quotient_kernel configuration_observer.source_trajectory_exact
 configuration_observer.observer_source_order_step configuration_observer.observer_partial_order
 configuration_observer.real_time_source_contract};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
