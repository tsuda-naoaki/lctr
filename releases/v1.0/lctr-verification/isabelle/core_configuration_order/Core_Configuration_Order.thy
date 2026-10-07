theory Core_Configuration_Order
 imports "LCTR_Core_Exact_Input_Assembly.Core_Exact_Input_Assembly"
 "LCTR_Core_Configuration_Comparison.Core_Configuration_Comparison"
begin
lemma clock_order_exact:
 "clock_order src a b\<longleftrightarrow>fst a=fst b \<and> snd a\<le>snd b"
 by (simp add: clock_order_def family_le_def)
lemma record_order_exact:
 "detector_order src a b\<longleftrightarrow>a=b \<or> record_sequence src a<record_sequence src b"
 by (rule detector_order_exact)
lemma distinct_clock_sources_incomparable:
 "fst a\<noteq>fst b\<Longrightarrow>\<not>clock_order src a b \<and> \<not>clock_order src b a"
 by (auto simp: clock_order_exact)
lemma clock_pre: "pre_on UNIV (clock_order src)"
 unfolding pre_on_def clock_order_exact by auto
lemma clock_anti: "clock_order src a b\<Longrightarrow>clock_order src b a\<Longrightarrow>a=b"
 by (auto simp: clock_order_exact intro: antisym prod_eqI)
lemma record_pre: "pre_on UNIV (detector_order src)"
 unfolding pre_on_def record_order_exact by auto
lemma record_anti: "detector_order src a b\<Longrightarrow>detector_order src b a\<Longrightarrow>a=b"
 by (auto simp: record_order_exact)

context exact_structure
begin
definition chosen_native_rep where
 "chosen_native_rep a=(SOME p. p\<in>native_carrier D f \<and> canonical_projection p=a)"
lemma chosen_native_rep_spec:
 assumes a: "a\<in>canonical_carrier"
 shows "chosen_native_rep a\<in>native_carrier D f \<and> canonical_projection(chosen_native_rep a)=a"
proof -
 have "a\<in>canonical_projection ` native_carrier D f" using a by (simp only: canonical_projection_onto)
 then have "\<exists>p. p\<in>native_carrier D f \<and> canonical_projection p=a" by blast
 then show ?thesis unfolding chosen_native_rep_def by (rule someI_ex)
qed
lemma chosen_source_order:
 assumes a: "a\<in>canonical_carrier" and b: "b\<in>canonical_carrier"
 shows "canonical_le a b\<longleftrightarrow>r(recover_tag(chosen_native_rep a))(recover_tag(chosen_native_rep b))"
 using canonical_order_representatives[OF chosen_native_rep_spec[OF a, THEN conjunct1]
 chosen_native_rep_spec[OF b, THEN conjunct1]] chosen_native_rep_spec[OF a] chosen_native_rep_spec[OF b] by simp
lemma represented_source_order:
 assumes inc: "inc_trans_on canonical_carrier canonical_lt"
 and emb: "\<And>a b. a\<in>QuSet canonical_carrier canonical_lt\<Longrightarrow>b\<in>QuSet canonical_carrier canonical_lt\<Longrightarrow>
 lt(embfn a)(embfn b)\<longleftrightarrow>qlt canonical_carrier canonical_lt a b"
 and a: "a\<in>canonical_carrier" and b: "b\<in>canonical_carrier"
 shows "lt(represented embfn a)(represented embfn b)\<longleftrightarrow>
 r(recover_tag(chosen_native_rep a))(recover_tag(chosen_native_rep b)) \<and> a\<noteq>b"
 using represented_order_pullback[where emb=embfn and lt=lt and x=a and y=b, OF inc emb a b]
 chosen_source_order[OF a b]
 by (simp only: canonical_lt_def)
end

locale configuration_order = configuration_comparison raw src adm joint
 for raw :: "('z,'s,'t,'l,'c,'d,'o,'m,'v,'rc,'rd,'rb)raw_input"
 and src :: "('cs,'dt,'bt,'cl,'dl,'z,'v,'rc,'rd,'rb)source_data"
 and adm :: "'v\<Rightarrow>'v\<Rightarrow>bool"
 and joint :: "'v\<Rightarrow>'v\<Rightarrow>(bool\<Rightarrow>('rc+'rd))\<Rightarrow>(bool\<Rightarrow>('rc+'rd))\<Rightarrow>bool" +
 assumes clock_descent: "ord_desc (native_carrier DC fC)(native_equiv DC fC trC adm)
 (pullback pair.C.recover_tag (clock_order src))"
 and record_descent: "ord_desc (native_carrier DD fD)(native_equiv DD fD trD adm)
 (pullback pair.D.recover_tag (detector_order src))"
begin
sublocale co: exact_structure DC fC trC adm "clock_order src"
 by unfold_locales (rule clock_pre, rule clock_anti, assumption+, rule clock_descent)
sublocale ro: exact_structure DD fD trD adm "detector_order src"
 by unfold_locales (rule record_pre, rule record_anti, assumption+, rule record_descent)
lemma quotient_preserved:
 "co.canonical_carrier=native_carrier DC fC//pair.ceq \<and>
 ro.canonical_carrier=native_carrier DD fD//pair.deq"
 by (simp add: co.canonical_carrier_def ro.canonical_carrier_def)
lemma projection_preserved:
 "co.canonical_projection a=pair.ceq``{a} \<and> ro.canonical_projection b=pair.deq``{b}"
 by (simp add: co.canonical_projection_def ro.canonical_projection_def)
lemma original_source_order:
 "(\<forall>a\<in>native_carrier DC fC. \<forall>b\<in>native_carrier DC fC.
 co.canonical_le(co.canonical_projection a)(co.canonical_projection b)\<longleftrightarrow>
 clock_order src (pair.C.recover_tag a)(pair.C.recover_tag b)) \<and>
 (\<forall>a\<in>native_carrier DD fD. \<forall>b\<in>native_carrier DD fD.
 ro.canonical_le(ro.canonical_projection a)(ro.canonical_projection b)\<longleftrightarrow>
 detector_order src (pair.D.recover_tag a)(pair.D.recover_tag b))"
 by (intro conjI ballI; rule co.canonical_order_representatives ro.canonical_order_representatives; assumption)
lemma native_partial_order:
 "part_on co.canonical_carrier co.canonical_le \<and> part_on ro.canonical_carrier ro.canonical_le"
 using co.canonical_partial_order ro.canonical_partial_order by blast
end

locale configuration_ordered = configuration_order raw src adm joint
 for raw :: "('z,'s,'t,'l,'c,'d,'o,'m,'v,'rc,'rd,'rb)raw_input"
 and src :: "('cs,'dt,'bt,'cl,'dl,'z,'v,'rc,'rd,'rb)source_data"
 and adm :: "'v\<Rightarrow>'v\<Rightarrow>bool"
 and joint :: "'v\<Rightarrow>'v\<Rightarrow>(bool\<Rightarrow>('rc+'rd))\<Rightarrow>(bool\<Rightarrow>('rc+'rd))\<Rightarrow>bool" +
 assumes clock_inc: "inc_trans_on co.canonical_carrier co.canonical_lt"
 and record_inc: "inc_trans_on ro.canonical_carrier ro.canonical_lt"
begin
sublocale assembled: paired_ordered_assembly DC fC trC adm DD fD trD adm "clock_order src" "detector_order src"
 by unfold_locales (rule clock_inc, rule record_inc)
lemma native_ordered_output_unique:
 "remaining cs ds\<Longrightarrow>\<exists>!p.
 pair.valid_output cs ds localRel(fst p) \<and> assembled.family_valid(snd p)"
 by (rule assembled.comparison_and_order_same_input[where src=sourceRel])
  (simp add: remaining_iff_operative[symmetric])
lemma native_local_global_compatible:
 "(\<forall>a\<in>regions DC fC i. co.local_global i(co.local_chart i a)=
 qproj co.canonical_carrier co.canonical_lt(co.canonical_projection a)) \<and>
 (\<forall>b\<in>regions DD fD i. ro.local_global i(ro.local_chart i b)=
 qproj ro.canonical_carrier ro.canonical_lt(ro.canonical_projection b))"
 by (intro conjI ballI; rule co.local_global_chart_commutes ro.local_global_chart_commutes)
  (use clock_inc record_inc co.global_implies_local_inc ro.global_implies_local_inc in auto)
lemma native_representation_order:
 assumes c: "\<And>a b. a\<in>QuSet co.canonical_carrier co.canonical_lt\<Longrightarrow>b\<in>QuSet co.canonical_carrier co.canonical_lt\<Longrightarrow>
 lc(fc a)(fc b)\<longleftrightarrow>qlt co.canonical_carrier co.canonical_lt a b"
 and d: "\<And>a b. a\<in>QuSet ro.canonical_carrier ro.canonical_lt\<Longrightarrow>b\<in>QuSet ro.canonical_carrier ro.canonical_lt\<Longrightarrow>
 ld(fd a)(fd b)\<longleftrightarrow>qlt ro.canonical_carrier ro.canonical_lt a b"
 shows "(\<forall>a\<in>co.canonical_carrier. \<forall>b\<in>co.canonical_carrier.
 lc(co.represented fc a)(co.represented fc b)\<longleftrightarrow>
 clock_order src (pair.C.recover_tag(co.chosen_native_rep a))(pair.C.recover_tag(co.chosen_native_rep b)) \<and> a\<noteq>b) \<and>
 (\<forall>a\<in>ro.canonical_carrier. \<forall>b\<in>ro.canonical_carrier.
 ld(ro.represented fd a)(ro.represented fd b)\<longleftrightarrow>
 detector_order src (pair.D.recover_tag(ro.chosen_native_rep a))(pair.D.recover_tag(ro.chosen_native_rep b)) \<and> a\<noteq>b)"
 by (intro conjI ballI;
  rule co.represented_source_order[where embfn=fc and lt=lc, OF clock_inc c]
   ro.represented_source_order[where embfn=fd and lt=ld, OF record_inc d]; assumption)
lemma native_representation_kernel:
 assumes c: "inj_on fc (QuSet co.canonical_carrier co.canonical_lt)"
 and d: "inj_on fd (QuSet ro.canonical_carrier ro.canonical_lt)"
 shows "(\<forall>a\<in>co.canonical_carrier. \<forall>b\<in>co.canonical_carrier.
 co.represented fc a=co.represented fc b\<longleftrightarrow>inc_on co.canonical_carrier co.canonical_lt a b) \<and>
 (\<forall>a\<in>ro.canonical_carrier. \<forall>b\<in>ro.canonical_carrier.
 ro.represented fd a=ro.represented fd b\<longleftrightarrow>inc_on ro.canonical_carrier ro.canonical_lt a b)"
 using co.represented_kernel[OF clock_inc c] ro.represented_kernel[OF record_inc d]
 by (auto simp: inc_on_def)
end
ML \<open>
val roots = @{thms clock_order_exact record_order_exact distinct_clock_sources_incomparable
 configuration_order.quotient_preserved configuration_order.projection_preserved
 configuration_order.original_source_order configuration_order.native_partial_order
 configuration_ordered.native_ordered_output_unique configuration_ordered.native_local_global_compatible
 configuration_ordered.native_representation_order configuration_ordered.native_representation_kernel};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
