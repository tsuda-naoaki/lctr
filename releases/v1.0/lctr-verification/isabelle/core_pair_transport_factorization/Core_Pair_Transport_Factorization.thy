theory Core_Pair_Transport_Factorization
 imports "HOL-Library.FuncSet"
begin
definition projection where "projection D i = (\<lambda>x. x i) ` D"
definition joint_value where
 "joint_value I f x = restrict (\<lambda>i. f i (x i)) I"
definition component where
 "component R i a b \<longleftrightarrow> (\<exists>x y. R x y \<and> x i=a \<and> y i=b)"
definition factorization_valid where
 "factorization_valid I X Y R p \<longleftrightarrow>
 fst p \<subseteq> PiE I X \<and>
 (\<forall>i\<in>I. snd p i \<in> extensional(projection (fst p) i) \<and>
   snd p i ` projection (fst p) i \<subseteq> Y i \<and> inj_on (snd p i) (projection (fst p) i)) \<and>
 (\<forall>i. i\<notin>I \<longrightarrow> snd p i=(\<lambda>_. undefined)) \<and>
 (\<forall>x y. R x y \<longleftrightarrow> x\<in>fst p \<and> y=joint_value I (snd p) x)"

locale pair_factorization =
 fixes I :: "'i set" and X :: "'i\<Rightarrow>'a set" and Y :: "'i\<Rightarrow>'b set"
 and R :: "('i\<Rightarrow>'a)\<Rightarrow>('i\<Rightarrow>'b)\<Rightarrow>bool"
 and D :: "('i\<Rightarrow>'a)set" and f :: "'i\<Rightarrow>'a\<Rightarrow>'b"
 assumes valid: "factorization_valid I X Y R (D,f)"
begin
lemma graph: "R x y \<longleftrightarrow> x\<in>D \<and> y=joint_value I f x"
 using valid by (simp add: factorization_valid_def)
lemma normalized: "i\<in>I \<Longrightarrow> a\<notin>projection D i \<Longrightarrow> f i a=undefined"
 using valid by (auto simp: factorization_valid_def extensional_def)
lemma inactive: "i\<notin>I \<Longrightarrow> f i=(\<lambda>_. undefined)"
 using valid by (simp add: factorization_valid_def)
lemma domain_forced: "D={x. \<exists>y. R x y}"
 by (auto simp: graph)
lemma component_graph_exact:
 assumes i: "i\<in>I"
 shows "component R i a b \<longleftrightarrow> a\<in>projection D i \<and> f i a=b"
 using i by (auto simp: component_def graph projection_def joint_value_def)
lemma component_functional:
 "i\<in>I \<Longrightarrow> component R i a b \<Longrightarrow> component R i a c \<Longrightarrow> b=c"
 by (simp add: component_graph_exact)
lemma component_injective:
 assumes i: "i\<in>I" and a: "component R i a c" and b: "component R i b c"
 shows "a=b"
proof -
 have inj: "inj_on (f i) (projection D i)" using valid i
  by (auto simp: factorization_valid_def)
 show ?thesis using a b inj by (auto simp: component_graph_exact[OF i] inj_on_def)
qed
end

lemma factorization_unique:
 assumes f: "factorization_valid I X Y R p" and g: "factorization_valid I X Y R q"
 shows "p=q"
proof -
 obtain D fm where p: "p=(D,fm)" by (cases p) auto
 obtain E gm where q: "q=(E,gm)" by (cases q) auto
 interpret f: pair_factorization I X Y R D fm by unfold_locales (use f p in simp)
 interpret g: pair_factorization I X Y R E gm by unfold_locales (use g q in simp)
 have de: "D=E" using f.domain_forced g.domain_forced by simp
 have maps: "fm=gm"
 proof (rule ext)+
  fix i a
  show "fm i a=gm i a"
  proof (cases "i\<in>I")
   case False then show ?thesis by (simp add: f.inactive g.inactive)
  next
   case True
   show ?thesis
   proof (cases "a\<in>projection D i")
    case False then show ?thesis using True de f.normalized g.normalized by metis
   next
    case True
    have mem: "component R i a (fm i a)" using True \<open>i\<in>I\<close>
     by (simp add: f.component_graph_exact)
    show ?thesis using mem \<open>i\<in>I\<close> by (simp add: g.component_graph_exact)
   qed
  qed
 qed
 show ?thesis using p q de maps by simp
qed
lemma existence_unique_iff:
 "(\<exists>p. factorization_valid I X Y R p) \<longleftrightarrow> (\<exists>!p. factorization_valid I X Y R p)"
 using factorization_unique by blast

definition coupled :: "(bool\<Rightarrow>bool)\<Rightarrow>(bool\<Rightarrow>bool)\<Rightarrow>bool" where
 "coupled x y \<longleftrightarrow>
 (x=(\<lambda>_. False) \<and> y=(\<lambda>_. False)) \<or>
 (x=id \<and> y=(\<lambda>_. True))"
lemma joint_function_does_not_ensure_component_factorization:
 "(\<forall>x y z. coupled x y \<longrightarrow> coupled x z \<longrightarrow> y=z) \<and>
 \<not>(\<exists>p. factorization_valid UNIV (\<lambda>_. UNIV) (\<lambda>_. UNIV) coupled p)"
proof
 show "\<forall>x y z. coupled x y \<longrightarrow> coupled x z \<longrightarrow> y=z"
  by (auto simp: coupled_def fun_eq_iff)
 show "\<not>(\<exists>p. factorization_valid UNIV (\<lambda>_. UNIV) (\<lambda>_. UNIV) coupled p)"
 proof
  assume "\<exists>p. factorization_valid UNIV (\<lambda>_. UNIV) (\<lambda>_. UNIV) coupled p"
  then obtain D fm where h: "factorization_valid UNIV (\<lambda>_. UNIV) (\<lambda>_. UNIV) coupled (D,fm)"
   by (metis surj_pair)
  interpret f: pair_factorization UNIV "\<lambda>_. UNIV" "\<lambda>_. UNIV" coupled D fm
   by unfold_locales (rule h)
  have a: "component coupled False False False"
   unfolding component_def by (intro exI[where x="\<lambda>_. False"] conjI) (simp_all add: coupled_def)
  have b: "component coupled False False True"
   unfolding component_def by (intro exI[where x=id] exI[where x="\<lambda>_. True"] conjI) (simp_all add: coupled_def)
  have "False=True" by (rule f.component_functional[OF UNIV_I a b])
  then show False by simp
 qed
qed

ML \<open>
val roots = @{thms pair_factorization.domain_forced pair_factorization.component_graph_exact
 pair_factorization.component_functional pair_factorization.component_injective factorization_unique
 existence_unique_iff joint_function_does_not_ensure_component_factorization};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
