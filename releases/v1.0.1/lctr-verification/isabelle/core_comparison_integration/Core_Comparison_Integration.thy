theory Core_Comparison_Integration
  imports "LCTR_Core_Typed_Words.Core_Typed_Words"
    "LCTR_Core_Source_Match.Core_Source_Match"
    "LCTR_Core_Preorder_Quotient.Core_Preorder_Quotient"
begin

datatype 'u comparison_atom = Source 'u 'u | Forward 'u 'u | Backward 'u 'u
fun initial where "initial (Source u v)=u" | "initial (Forward u v)=u" | "initial (Backward u v)=u"
fun terminal where "terminal (Source u v)=v" | "terminal (Forward u v)=v" | "terminal (Backward u v)=v"
fun inverted where
  "inverted (Source u v)=Source v u" |
  "inverted (Forward u v)=Backward v u" |
  "inverted (Backward u v)=Forward v u"
fun admitted where
  "admitted adm (Source u v)=True" |
  "admitted adm (Forward u v)=adm u v" |
  "admitted adm (Backward u v)=adm v u"

definition regions where "regions D f u = {u}\<times>(f u ` D u)"
fun cmp_act where
  "cmp_act D f tr (Source u v) p q =
    (fst p=u \<and> fst q=v \<and> src_graph D f u v (snd p) (snd q))" |
  "cmp_act D f tr (Forward u v) p q =
    (p\<in>regions D f u \<and> q\<in>regions D f v \<and> tr u v (snd p) (snd q))" |
  "cmp_act D f tr (Backward u v) p q =
    (p\<in>regions D f u \<and> q\<in>regions D f v \<and> tr v u (snd q) (snd p))"

lemma src_graph_images:
  "src_graph D f u v a b \<Longrightarrow> a\<in>f u ` D u \<and> b\<in>f v ` D v"
  unfolding src_graph_def src_match_def by blast

locale native_comparison =
  fixes D :: "'u\<Rightarrow>'s set" and f :: "'u\<Rightarrow>'s\<Rightarrow>'v"
    and tr :: "'u\<Rightarrow>'u\<Rightarrow>'v\<Rightarrow>'v\<Rightarrow>bool"
    and adm :: "'u\<Rightarrow>'u\<Rightarrow>bool"
  assumes local_inj: "inj_on (f u) (D u)"
    and tr_fun: "adm u v \<Longrightarrow> a\<in>f u ` D u \<Longrightarrow> b\<in>f v ` D v \<Longrightarrow> c\<in>f v ` D v \<Longrightarrow> tr u v a b \<Longrightarrow> tr u v a c \<Longrightarrow> b=c"
    and tr_inj: "adm u v \<Longrightarrow> a\<in>f u ` D u \<Longrightarrow> b\<in>f u ` D u \<Longrightarrow> c\<in>f v ` D v \<Longrightarrow> tr u v a c \<Longrightarrow> tr u v b c \<Longrightarrow> a=b"
begin

lemma atom_type:
  "cmp_act D f tr e p q \<Longrightarrow> p\<in>regions D f (initial e) \<and> q\<in>regions D f (terminal e)"
  by (cases e; cases p; cases q) (auto simp: regions_def dest: src_graph_images)

lemma atom_functional:
  assumes ad: "admitted adm e" and pq: "cmp_act D f tr e p q" and pr: "cmp_act D f tr e p r"
  shows "q=r"
  using assms
  by (cases e; cases p; cases q; cases r)
    (auto simp: regions_def dest: source_match_functional intro: tr_fun tr_inj)

lemma atom_inverse:
  "cmp_act D f tr (inverted e) q p = cmp_act D f tr e p q"
proof (cases e)
  case (Source u v)
  have sg: "\<And>a b. src_graph D f v u b a = src_graph D f u v a b"
  proof -
    fix a b
    show "src_graph D f v u b a = src_graph D f u v a b"
    proof
      assume h: "src_graph D f v u b a"
      have bi: "b\<in>f v ` D v" and ai: "a\<in>f u ` D u"
        using src_graph_images[where D=D and f=f and u=v and v=u and a=b and b=a, OF h] by auto
      show "src_graph D f u v a b"
        using source_match_inverse_graph[where D=D and f=f and u=u and v=v and a=a and b=b,
          OF local_inj local_inj ai bi] h by blast
    next
      assume h: "src_graph D f u v a b"
      have ai: "a\<in>f u ` D u" and bi: "b\<in>f v ` D v"
        using src_graph_images[where D=D and f=f and u=u and v=v and a=a and b=b, OF h] by auto
      show "src_graph D f v u b a"
        using source_match_inverse_graph[where D=D and f=f and u=u and v=v and a=a and b=b,
          OF local_inj local_inj ai bi] h by blast
    qed
  qed
  show ?thesis using Source sg by auto
next
  case (Forward u v)
  then show ?thesis by auto
next
  case (Backward u v)
  then show ?thesis by auto
qed

interpretation W: typed_actions "regions D f" "{e. admitted adm e}" initial terminal inverted "cmp_act D f tr"
proof
  fix e
  assume "e\<in>{e. admitted adm e}"
  then show "inverted e\<in>{e. admitted adm e}" by (cases e) auto
next
  fix e
  assume "e\<in>{e. admitted adm e}"
  show "initial (inverted e)=terminal e" by (cases e) auto
next
  fix e
  assume "e\<in>{e. admitted adm e}"
  show "terminal (inverted e)=initial e" by (cases e) auto
next
  fix e
  assume "e\<in>{e. admitted adm e}"
  show "inverted (inverted e)=e" by (cases e) auto
next
  fix e p q
  assume "e\<in>{e. admitted adm e}" and pq: "cmp_act D f tr e p q"
  show "p\<in>regions D f (initial e) \<and> q\<in>regions D f (terminal e)" by (rule atom_type[OF pq])
next
  fix e p q r
  assume "e\<in>{e. admitted adm e}" and "cmp_act D f tr e p q" and "cmp_act D f tr e p r"
  then show "q=r" using atom_functional by auto
next
  fix e p q
  assume "e\<in>{e. admitted adm e}"
  show "cmp_act D f tr (inverted e) q p = cmp_act D f tr e p q" by (rule atom_inverse)
qed

lemma regions_disjoint:
  "p\<in>regions D f u \<Longrightarrow> p\<in>regions D f v \<Longrightarrow> u=v"
  unfolding regions_def by auto

theorem comparison_equivalence: "equiv W.carrier {(p,q). W.orbit p q}"
  by (rule W.orbit_equivalence[OF regions_disjoint])

theorem equal_recovery_comparison:
  assumes a: "a\<in>f u ` D u" and b: "b\<in>f v ` D v"
    and eq: "recovery D f u a = recovery D f v b"
  shows "W.orbit (u,a) (v,b)"
proof -
  have sg: "src_graph D f u v a b"
    using same_source_native_match[where D=D and f=f and u=u and v=v and a=a and b=b, OF a b eq] a
    unfolding src_graph_def by blast
  have run: "W.action u [Source u v] v (u,a) (v,b)"
    using a sg by (auto simp: W.action_def W.typed.simps regions_def)
  show ?thesis using run unfolding W.orbit_def by blast
qed

definition recover_tag where "recover_tag p = recovery D f (fst p) (snd p)"

theorem comparison_order_separation:
  assumes anti: "\<And>a b. r a b \<Longrightarrow> r b a \<Longrightarrow> a=b"
  shows "ord_sep W.carrier {(p,q). W.orbit p q} (pullback recover_tag r)"
proof (unfold ord_sep_def, intro ballI impI)
  fix p q
  assume p: "p\<in>W.carrier" and q: "q\<in>W.carrier"
    and pq: "pullback recover_tag r p q" and qp: "pullback recover_tag r q p"
  have pi: "snd p\<in>f (fst p) ` D (fst p)" and qi: "snd q\<in>f (fst q) ` D (fst q)"
    using p q unfolding W.carrier_def regions_def by auto
  have eq: "recovery D f (fst p) (snd p) = recovery D f (fst q) (snd q)"
    using anti pq qp unfolding pullback_def recover_tag_def by blast
  have "W.orbit (fst p,snd p) (fst q,snd q)" by (rule equal_recovery_comparison[OF pi qi eq])
  then show "(p,q)\<in>{(p,q). W.orbit p q}" by simp
qed

theorem canonical_comparison_partial_order:
  assumes pre: "pre_on UNIV r"
    and anti: "\<And>a b. r a b \<Longrightarrow> r b a \<Longrightarrow> a=b"
    and desc: "ord_desc W.carrier {(p,q). W.orbit p q} (pullback recover_tag r)"
  shows "part_on (W.carrier//{(p,q). W.orbit p q})
    (qrel W.carrier {(p,q). W.orbit p q} (pullback recover_tag r))"
proof -
  have arrival: "pre_on W.carrier (pullback recover_tag r)"
    by (rule preorder_pullback[where T=UNIV, OF _ pre]) auto
  show ?thesis by (rule quotient_partial_order[OF comparison_equivalence desc comparison_order_separation[OF anti] arrival])
qed

theorem comparison_loop_projection_criterion:
  "W.loop_identity = (\<forall>u. inj_on (\<lambda>p. {(x,y). W.orbit x y}``{p}) (regions D f u))"
  by (rule W.loop_identity_iff_local_projection_injective[OF regions_disjoint])

end

ML \<open>
val roots = @{thms native_comparison.comparison_equivalence native_comparison.equal_recovery_comparison
  native_comparison.comparison_order_separation native_comparison.canonical_comparison_partial_order
  native_comparison.comparison_loop_projection_criterion};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
