theory Core_Exact_Input_Assembly
 imports "LCTR_Core_Exact_Completion.Core_Exact_Completion"
begin
record ('u,'s,'v) assembled_input =
 arrival_domains :: "'u\<Rightarrow>'s set"
 arrival_map :: "'u\<Rightarrow>'s\<Rightarrow>'v"
 transport_map :: "'u\<Rightarrow>'u\<Rightarrow>'v\<Rightarrow>'v\<Rightarrow>bool"
 transport_allowed :: "'u\<Rightarrow>'u\<Rightarrow>bool"
 input_source_order :: "'s\<Rightarrow>'s\<Rightarrow>bool"
definition assemble where
 "assemble D f tr adm r=\<lparr>arrival_domains=D,arrival_map=f,transport_map=tr,
 transport_allowed=adm,input_source_order=r\<rparr>"
lemma same_arrivals:
 "arrival_domains(assemble D f tr adm r)=D \<and> arrival_map(assemble D f tr adm r)=f"
 by (simp add: assemble_def)
lemma same_transport:
 "transport_map(assemble D f tr adm r)=tr \<and> transport_allowed(assemble D f tr adm r)=adm"
 by (simp add: assemble_def)
lemma same_quotient:
 assumes es: "exact_structure D f tr adm r"
 shows "exact_structure.canonical_carrier (arrival_domains(assemble D f tr adm r))
 (arrival_map(assemble D f tr adm r))(transport_map(assemble D f tr adm r))
 (transport_allowed(assemble D f tr adm r))=
 native_carrier D f//native_equiv D f tr adm"
proof -
 interpret es: exact_structure D f tr adm r by (rule es)
 show ?thesis by (simp add: assemble_def es.canonical_carrier_def)
qed
lemma same_projection:
 assumes es: "exact_structure D f tr adm r"
 shows "exact_structure.canonical_projection (arrival_domains(assemble D f tr adm r))
 (arrival_map(assemble D f tr adm r))(transport_map(assemble D f tr adm r))
 (transport_allowed(assemble D f tr adm r))x=Image(native_equiv D f tr adm){x}"
proof -
 interpret es: exact_structure D f tr adm r by (rule es)
 show ?thesis by (simp add: assemble_def es.canonical_projection_def)
qed

context exact_structure
begin
lemma source_order_recovered:
 "x\<in>native_carrier D f \<Longrightarrow> y\<in>native_carrier D f \<Longrightarrow>
 (canonical_le(canonical_projection x)(canonical_projection y) \<longleftrightarrow>
 r(recover_tag x)(recover_tag y))"
 by (rule canonical_order_representatives)
end
context ordered_completion
begin
lemma local_global_same_source:
 assumes a: "a\<in>regions D f i"
 shows "oo_localglobal generated_ordered i (oo_chart generated_ordered i a)=
 oo_global generated_ordered (Image(native_equiv D f tr adm){a})"
proof -
 have local: "cp a\<in>L i" using a by (auto simp: local_carrier_def)
 have global: "cp a\<in>C" using a projection_maps by blast
 have commute: "local_global i(qp i(cp a))=gp(cp a)"
  by (rule local_global_commutes[OF local_inc global_inc local])
 show ?thesis using a local global commute
  by (simp add: generated_ordered_def on_domain_def local_chart_def canonical_projection_def QuSet_def)
qed
end

locale paired_ordered_assembly =
 paired_comparison DC fC trC admC DD fD trD admD +
 CO: ordered_completion DC fC trC admC rC +
 DO: ordered_completion DD fD trD admD rD
 for DC :: "'u\<Rightarrow>'sc set" and fC :: "'u\<Rightarrow>'sc\<Rightarrow>'vc"
 and trC :: "'u\<Rightarrow>'u\<Rightarrow>'vc\<Rightarrow>'vc\<Rightarrow>bool"
 and admC :: "'u\<Rightarrow>'u\<Rightarrow>bool"
 and DD :: "'u\<Rightarrow>'sd set" and fD :: "'u\<Rightarrow>'sd\<Rightarrow>'vd"
 and trD :: "'u\<Rightarrow>'u\<Rightarrow>'vd\<Rightarrow>'vd\<Rightarrow>bool"
 and admD :: "'u\<Rightarrow>'u\<Rightarrow>bool"
 and rC :: "'sc\<Rightarrow>'sc\<Rightarrow>bool" and rD :: "'sd\<Rightarrow>'sd\<Rightarrow>bool"
begin
definition family_valid where "family_valid q \<longleftrightarrow> CO.ordered_valid(fst q) \<and> DO.ordered_valid(snd q)"
definition generated_family where "generated_family=(CO.generated_ordered,DO.generated_ordered)"
lemma generated_family_valid: "family_valid generated_family"
 by (simp add: family_valid_def generated_family_def CO.generated_ordered_valid DO.generated_ordered_valid)
lemma family_unique: "family_valid q \<Longrightarrow> q=generated_family"
 using CO.ordered_output_unique DO.ordered_output_unique
 unfolding family_valid_def generated_family_def by (metis surjective_pairing)
lemma ordered_family_unique: "\<exists>!q. family_valid q"
 by (rule ex1I[where a=generated_family]) (rule generated_family_valid, rule family_unique, assumption)
lemma comparison_and_order_same_input:
 assumes op: "residual_operative cs ds loc src"
 shows "\<exists>!p. valid_output cs ds loc (fst p) \<and> family_valid(snd p)"
proof -
 have l3: "stage_L3 cs ds" using op by (simp add: residual_operative_def)
 have valid: "valid_output cs ds loc (generate cs ds loc)" by (rule generated_valid[OF l3])
 show ?thesis
 proof (rule ex1I[where a="(generate cs ds loc,generated_family)"])
  show "valid_output cs ds loc (fst(generate cs ds loc,generated_family)) \<and>
   family_valid(snd(generate cs ds loc,generated_family))"
   using valid generated_family_valid by simp
 next
  fix p assume h: "valid_output cs ds loc (fst p) \<and> family_valid(snd p)"
  have one: "fst p=generate cs ds loc" by (rule output_unique[OF l3]) (use h in blast)
  have two: "snd p=generated_family" by (rule family_unique) (use h in blast)
  show "p=(generate cs ds loc,generated_family)" using one two by (cases p) auto
 qed
qed
lemma comparison_injection_retained:
 "residual_operative cs ds loc src \<Longrightarrow>
 inj_on CO.canonical_projection (regions DC fC i) \<and>
 inj_on DO.canonical_projection (regions DD fD i)"
 unfolding CO.canonical_projection_def DO.canonical_projection_def
 by (rule generated_local_injective)
lemma generated_order_no_extra_coordinate_input:
 "(\<And>p. family_valid(candidate p)) \<Longrightarrow> candidate p=candidate q"
 using family_unique by metis
end

ML \<open>
val roots = @{thms same_arrivals same_transport same_quotient same_projection
 exact_structure.source_order_recovered paired_ordered_assembly.ordered_family_unique
 paired_ordered_assembly.comparison_and_order_same_input ordered_completion.local_global_same_source
 paired_ordered_assembly.comparison_injection_retained
 paired_ordered_assembly.generated_order_no_extra_coordinate_input};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
