theory Core_Exact_Completion
 imports LCTR_Core_Exact_Structure.Core_Exact_Structure
 LCTR_Core_Comparison_Stage.Core_Comparison_Stage
begin

context paired_comparison
begin
definition residual_stage_seven where
 "residual_stage_seven cs ds loc src \<longleftrightarrow> stage_L3 cs ds \<and> stage_L4 cs ds \<and>
  stage_L5 loc src \<and> saturated loc \<and> C.irreducible_mixed_identity \<and> D.irreducible_mixed_identity"
theorem native_master_condition:
 "residual_operative cs ds loc src \<longleftrightarrow>
  residual_stage_seven cs ds loc src \<and> C.pure_loop_identity \<and> D.pure_loop_identity"
 by (simp add: residual_operative_def residual_stage_seven_def)
theorem native_conditions_give_comparison_output:
 assumes h: "residual_stage_seven cs ds loc src" and c: C.pure_loop_identity and d: D.pure_loop_identity
 shows "residual_operative cs ds loc src \<and> (\<exists>!out. valid_output cs ds loc out)"
proof -
 have op: "residual_operative cs ds loc src" using h c d native_master_condition[of cs ds loc src] by blast
 show ?thesis using op unique_generated_output[OF op] by blast
qed
end

definition on_domain where "on_domain A f x=(if x\<in>A then f x else undefined)"
definition normalized where "normalized A f \<longleftrightarrow> (\<forall>x. x\<notin>A \<longrightarrow> f x=undefined)"
lemma on_domain_normalized: "normalized A (on_domain A f)"
 by (simp add: normalized_def on_domain_def)
lemma on_domain_agrees: "x\<in>A \<Longrightarrow> on_domain A f x=f x"
 by (simp add: on_domain_def)
lemma normalized_unique:
 assumes nf: "normalized A f" and ng: "normalized A g"
 and eq: "\<And>x. x\<in>A \<Longrightarrow> f x=g x"
 shows "f=g"
proof (rule ext)
 fix x
 show "f x=g x"
 proof (cases "x\<in>A")
  case True show ?thesis by (rule eq[OF True])
 next
  case False
  have "f x=undefined" using nf False by (simp add: normalized_def)
  moreover have "g x=undefined" using ng False by (simp add: normalized_def)
  ultimately show ?thesis by simp
 qed
qed
lemma normalized_projection_unique:
 assumes onto: "image p S=A" and nf: "normalized A f" and ng: "normalized A g"
 and eq: "\<And>x. x\<in>S \<Longrightarrow> f(p x)=g(p x)"
 shows "f=g"
 by (rule normalized_unique[OF nf ng]) (use onto eq in blast)

record ('u,'a,'q) ordered_output =
 oo_order :: "'q\<Rightarrow>'q\<Rightarrow>bool"
 oo_chart :: "'u\<Rightarrow>'a\<Rightarrow>'q set"
 oo_change :: "'u\<Rightarrow>'u\<Rightarrow>'q set\<Rightarrow>'q set"
 oo_global :: "'q\<Rightarrow>'q set"
 oo_localglobal :: "'u\<Rightarrow>'q set\<Rightarrow>'q set"

context exact_structure
begin
lemma canonical_projection_onto:
 "image canonical_projection (native_carrier D f)=canonical_carrier"
 by (auto simp: canonical_projection_def canonical_carrier_def quotient_def)
theorem canonical_order_unique:
 assumes reps: "\<And>x y. x\<in>native_carrier D f \<Longrightarrow> y\<in>native_carrier D f \<Longrightarrow>
  (q(canonical_projection x)(canonical_projection y) \<longleftrightarrow> r(recover_tag x)(recover_tag y))"
 shows "\<forall>a\<in>canonical_carrier. \<forall>b\<in>canonical_carrier. q a b=canonical_le a b"
proof (intro ballI)
 fix a b assume a: "a\<in>canonical_carrier" and b: "b\<in>canonical_carrier"
 have ai: "a\<in>image canonical_projection (native_carrier D f)"
  using a by (simp only: canonical_projection_onto)
 have bi: "b\<in>image canonical_projection (native_carrier D f)"
  using b by (simp only: canonical_projection_onto)
 obtain x where x: "x\<in>native_carrier D f" and ax: "a=canonical_projection x"
  using ai by (rule imageE)
 obtain y where y: "y\<in>native_carrier D f" and byy: "b=canonical_projection y"
  using bi by (rule imageE)
 show "q a b=canonical_le a b"
  using reps[OF x y] canonical_order_representatives[OF x y] ax byy by blast
qed
end

locale ordered_completion = exact_structure D f tr adm r
 for D :: "'u\<Rightarrow>'s set" and f :: "'u\<Rightarrow>'s\<Rightarrow>'v"
 and tr :: "'u\<Rightarrow>'u\<Rightarrow>'v\<Rightarrow>'v\<Rightarrow>bool"
 and adm :: "'u\<Rightarrow>'u\<Rightarrow>bool" and r +
 assumes global_inc: "inc_trans_on canonical_carrier canonical_lt"
begin
abbreviation C where "C\<equiv>canonical_carrier"
abbreviation L where "L\<equiv>local_carrier"
abbreviation cp where "cp\<equiv>canonical_projection"
abbreviation qp where "qp i\<equiv>qproj(L i)canonical_lt"
abbreviation gp where "gp\<equiv>qproj C canonical_lt"
abbreviation overlap where "overlap i j\<equiv>L i\<inter>L j"
abbreviation change_dom where "change_dom i j\<equiv>image(qp i)(overlap i j)"
abbreviation change where "change i j\<equiv>overlap_change(L i)(L j)canonical_lt"

lemma local_inc: "inc_trans_on(L i)canonical_lt"
 by (rule global_implies_local_inc[OF global_inc])
lemma changes_commute:
 "x\<in>overlap i j \<Longrightarrow> change i j (qp i x)=qp j x"
proof -
 interpret P: order_pair "L i" "L j" canonical_lt
  by unfold_locales (rule local_strict,rule local_inc,rule local_strict,rule local_inc)
 show "x\<in>overlap i j \<Longrightarrow> change i j (qp i x)=qp j x" by (rule P.overlap_change_commutes)
qed

definition generated_ordered :: "('u,'u\<times>'v,('u\<times>'v)set) ordered_output" where
 "generated_ordered=\<lparr>
  oo_order=(\<lambda>x y. x\<in>C \<and> y\<in>C \<and> canonical_le x y),
  oo_chart=(\<lambda>i. on_domain(regions D f i)(local_chart i)),
  oo_change=(\<lambda>i j. on_domain(change_dom i j)(change i j)),
  oo_global=on_domain C gp,
  oo_localglobal=(\<lambda>i. on_domain(QuSet(L i)canonical_lt)(local_global i))\<rparr>"
definition ordered_valid where
 "ordered_valid (out::('u,'u\<times>'v,('u\<times>'v)set) ordered_output) \<longleftrightarrow>
  (\<forall>x y. oo_order out x y \<longrightarrow> x\<in>C \<and> y\<in>C) \<and>
  (\<forall>x\<in>native_carrier D f. \<forall>y\<in>native_carrier D f.
   oo_order out (cp x)(cp y) \<longleftrightarrow> r(recover_tag x)(recover_tag y)) \<and>
  (\<forall>i. normalized(regions D f i)(oo_chart out i)) \<and>
  (\<forall>i. \<forall>a\<in>regions D f i. oo_chart out i a=qp i(cp a)) \<and>
  (\<forall>i j. normalized(change_dom i j)(oo_change out i j)) \<and>
  (\<forall>i j. \<forall>x\<in>overlap i j. oo_change out i j(qp i x)=qp j x) \<and>
  normalized C (oo_global out) \<and>
  (\<forall>x\<in>native_carrier D f. oo_global out(cp x)=gp(cp x)) \<and>
  (\<forall>i. normalized(QuSet(L i)canonical_lt)(oo_localglobal out i)) \<and>
  (\<forall>i. \<forall>x\<in>L i. oo_localglobal out i(qp i x)=gp x)"

theorem generated_ordered_valid: "ordered_valid generated_ordered"
proof -
 have rep: "\<And>x y. x\<in>native_carrier D f \<Longrightarrow> y\<in>native_carrier D f \<Longrightarrow>
  (oo_order generated_ordered(cp x)(cp y) \<longleftrightarrow> r(recover_tag x)(recover_tag y))"
  using projection_maps canonical_order_representatives by (simp add: generated_ordered_def)
 have loc: "\<And>i a. a\<in>regions D f i \<Longrightarrow> oo_chart generated_ordered i a=qp i(cp a)"
  by (simp add: generated_ordered_def on_domain_def local_chart_def)
 have ch: "\<And>i j x. x\<in>overlap i j \<Longrightarrow> oo_change generated_ordered i j(qp i x)=qp j x"
  using changes_commute by (auto simp: generated_ordered_def on_domain_def)
 have gl: "\<And>x. x\<in>native_carrier D f \<Longrightarrow> oo_global generated_ordered(cp x)=gp(cp x)"
  using projection_maps by (simp add: generated_ordered_def on_domain_def)
 have lg: "\<And>i x. x\<in>L i \<Longrightarrow> oo_localglobal generated_ordered i(qp i x)=gp x"
  using local_global_commutes[OF local_inc global_inc]
  by (auto simp: generated_ordered_def on_domain_def QuSet_def)
 show ?thesis unfolding ordered_valid_def
  using rep loc ch gl lg by (auto simp: generated_ordered_def on_domain_normalized)
qed

theorem ordered_output_unique:
 assumes v: "ordered_valid out"
 shows "out=generated_ordered"
proof -
 have gen: "ordered_valid generated_ordered" by (rule generated_ordered_valid)
 have oq: "\<forall>a\<in>C. \<forall>b\<in>C. oo_order out a b=canonical_le a b"
  by (rule canonical_order_unique) (use v in \<open>auto simp: ordered_valid_def\<close>)
 have oeq: "oo_order out=oo_order generated_ordered"
 proof (rule ext, rule ext)
  fix x y
  have typed: "oo_order out x y \<Longrightarrow> x\<in>C \<and> y\<in>C"
  proof -
   assume xy: "oo_order out x y"
   have all: "\<forall>x y. oo_order out x y \<longrightarrow> x\<in>C \<and> y\<in>C"
    using v unfolding ordered_valid_def by (rule conjunct1)
   show "x\<in>C \<and> y\<in>C" by (rule all[rule_format, of x y, OF xy])
  qed
  have ineq: "x\<in>C \<Longrightarrow> y\<in>C \<Longrightarrow> oo_order out x y=canonical_le x y"
   using oq by blast
  show "oo_order out x y=oo_order generated_ordered x y"
   using typed ineq by (auto simp: generated_ordered_def)
 qed
 have ceq: "oo_chart out=oo_chart generated_ordered"
 proof (rule ext)
  fix i
  show "oo_chart out i=oo_chart generated_ordered i"
   by (rule normalized_unique[where A="regions D f i"]) (use v gen in \<open>auto simp: ordered_valid_def\<close>)
 qed
 have cheq: "oo_change out=oo_change generated_ordered"
 proof (rule ext, rule ext)
  fix i j
  show "oo_change out i j=oo_change generated_ordered i j"
   by (rule normalized_projection_unique[where S="overlap i j" and p="qp i" and A="change_dom i j"])
    (use v gen in \<open>auto simp: ordered_valid_def\<close>)
 qed
 have geq: "oo_global out=oo_global generated_ordered"
  by (rule normalized_projection_unique[OF canonical_projection_onto])
   (use v gen in \<open>auto simp: ordered_valid_def\<close>)
 have lgeq: "oo_localglobal out=oo_localglobal generated_ordered"
 proof (rule ext)
  fix i
  show "oo_localglobal out i=oo_localglobal generated_ordered i"
   by (rule normalized_projection_unique[where S="L i" and p="qp i" and A="QuSet(L i)canonical_lt"])
    (use v gen in \<open>auto simp: ordered_valid_def QuSet_def\<close>)
 qed
 show ?thesis using oeq ceq cheq geq lgeq by (cases out) (simp add: generated_ordered_def)
qed

theorem canonical_ordered_bundle_exists_unique: "\<exists>!out. ordered_valid out"
 by (rule ex1I[where a=generated_ordered]) (rule generated_ordered_valid, rule ordered_output_unique)

theorem conventional_time_factor:
 fixes time :: "('u\<times>'v)set\<Rightarrow>'t::linorder"
 assumes kernel: "\<And>x y. x\<in>C \<Longrightarrow> y\<in>C \<Longrightarrow>
  (time x=time y \<longleftrightarrow> inc_on C canonical_lt x y)"
 and ord: "\<And>x y. x\<in>C \<Longrightarrow> y\<in>C \<Longrightarrow> (time x<time y \<longleftrightarrow> canonical_lt x y)"
 shows "\<exists>F. bij_betw F (QuSet C canonical_lt)(image time C) \<and>
  (\<forall>x\<in>C. F(gp x)=time x) \<and>
  (\<forall>a\<in>QuSet C canonical_lt. \<forall>b\<in>QuSet C canonical_lt. F a<F b \<longleftrightarrow> qlt C canonical_lt a b) \<and>
  (\<forall>G. (\<forall>x\<in>C. G(gp x)=time x) \<longrightarrow> (\<forall>q\<in>QuSet C canonical_lt. G q=F q))"
proof -
 interpret F: order_quotient_factor C canonical_lt time
  by standard (rule strict_part_contract,rule global_inc,rule kernel)
 show ?thesis by (rule F.quotient_factor_exists_unique[OF ord])
qed
end

context exact_structure
begin
theorem conventional_time_coordinate_freedom:
 fixes time :: "('u\<times>'v)set\<Rightarrow>'t::linorder"
 and other :: "('u\<times>'v)set\<Rightarrow>'z::linorder"
 assumes k1: "\<And>x y. x\<in>canonical_carrier \<Longrightarrow> y\<in>canonical_carrier \<Longrightarrow>
  (time x=time y \<longleftrightarrow> inc_on canonical_carrier canonical_lt x y)"
 and k2: "\<And>x y. x\<in>canonical_carrier \<Longrightarrow> y\<in>canonical_carrier \<Longrightarrow>
  (other x=other y \<longleftrightarrow> inc_on canonical_carrier canonical_lt x y)"
 and s1: "\<And>x y. x\<in>canonical_carrier \<Longrightarrow> y\<in>canonical_carrier \<Longrightarrow>
  (time x<time y \<longleftrightarrow> canonical_lt x y)"
 and s2: "\<And>x y. x\<in>canonical_carrier \<Longrightarrow> y\<in>canonical_carrier \<Longrightarrow>
  (other x<other y \<longleftrightarrow> canonical_lt x y)"
 shows "\<exists>F. bij_betw F (image time canonical_carrier)(image other canonical_carrier) \<and>
  (\<forall>a\<in>image time canonical_carrier. \<forall>b\<in>image time canonical_carrier. F a<F b \<longleftrightarrow> a<b) \<and>
  (\<forall>x\<in>canonical_carrier. F(time x)=other x) \<and>
  (\<forall>G. (\<forall>x\<in>canonical_carrier. G(time x)=other x) \<longrightarrow> (\<forall>a\<in>image time canonical_carrier. G a=F a))"
 by (rule reparametrization_unique[OF k1 k2 s1 s2])
end

ML \<open>
val roots = @{thms paired_comparison.native_master_condition
 paired_comparison.native_conditions_give_comparison_output exact_structure.canonical_order_unique
 ordered_completion.generated_ordered_valid ordered_completion.ordered_output_unique
 ordered_completion.canonical_ordered_bundle_exists_unique ordered_completion.conventional_time_factor
 exact_structure.conventional_time_coordinate_freedom};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
