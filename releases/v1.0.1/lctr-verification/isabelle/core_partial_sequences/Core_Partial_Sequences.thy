theory Core_Partial_Sequences
 imports LCTR_Core_Typed_Words.Core_Typed_Words LCTR_Core_Source_Match.Core_Source_Match
begin

definition pi_graph where "pi_graph A f a b \<longleftrightarrow> a\<in>A \<and> f a=b"
definition pi_domain where "pi_domain R={a. \<exists>b. R a b}"
definition pi_image where "pi_image R={b. \<exists>a. R a b}"
definition pi_reverse where "pi_reverse R b a \<longleftrightarrow> R a b"
definition pi_comp where "pi_comp R S a c \<longleftrightarrow> (\<exists>b. R a b \<and> S b c)"
definition pi_injection where
 "pi_injection R \<longleftrightarrow> (\<forall>a b c. R a b \<longrightarrow> R a c \<longrightarrow> b=c) \<and>
  (\<forall>a b c. R a c \<longrightarrow> R b c \<longrightarrow> a=b)"

theorem partial_graph_domain: "pi_domain(pi_graph A f)=A"
 by (auto simp: pi_domain_def pi_graph_def)
theorem partial_graph_value: "a\<in>A \<Longrightarrow> (pi_graph A f a b \<longleftrightarrow> f a=b)"
 by (simp add: pi_graph_def)
theorem reverse_domain_is_image: "pi_domain(pi_reverse R)=pi_image R"
 by (simp add: pi_domain_def pi_reverse_def pi_image_def)

theorem inverse_composition_on_domain:
 assumes h: "pi_injection R"
 shows "pi_comp R (pi_reverse R) a c \<longleftrightarrow> a=c \<and> a\<in>pi_domain R"
 using h unfolding pi_comp_def pi_reverse_def pi_domain_def pi_injection_def by blast

theorem composition_domain:
 "a\<in>pi_domain(pi_comp R S) \<longleftrightarrow> (\<exists>b. R a b \<and> b\<in>pi_domain S)"
 by (auto simp: pi_domain_def pi_comp_def)

lemma pi_reverse_injection: "pi_injection R \<Longrightarrow> pi_injection(pi_reverse R)"
 unfolding pi_injection_def pi_reverse_def by blast
lemma pi_reverse_reverse: "pi_reverse(pi_reverse R)=R"
 by (intro ext) (simp add: pi_reverse_def)

datatype ('u,'x) partial_atom = PAtom 'u 'u "'x\<Rightarrow>'x\<Rightarrow>bool"
fun pi_src where "pi_src(PAtom u v R)=u"
fun pi_dst where "pi_dst(PAtom u v R)=v"
fun pi_act where "pi_act(PAtom u v R)=R"
fun pi_flip where "pi_flip(PAtom u v R)=PAtom v u (pi_reverse R)"
definition pi_admissible where
 "pi_admissible Y e \<longleftrightarrow> pi_injection(pi_act e) \<and>
  (\<forall>a b. pi_act e a b \<longrightarrow> a\<in>Y(pi_src e) \<and> b\<in>Y(pi_dst e))"

locale all_partial_graphs =
 fixes Y :: "'u\<Rightarrow>'x set"
begin
interpretation W: typed_actions Y "{e. pi_admissible Y e}" pi_src pi_dst pi_flip pi_act
proof
 fix e assume "e\<in>{e. pi_admissible Y e}"
 then show "pi_flip e\<in>{e. pi_admissible Y e}"
  by (cases e) (auto simp: pi_admissible_def pi_reverse_def pi_injection_def)
next
 fix e assume "e\<in>{e. pi_admissible Y e}"
 show "pi_src(pi_flip e)=pi_dst e" by (cases e) simp
next
 fix e assume "e\<in>{e. pi_admissible Y e}"
 show "pi_dst(pi_flip e)=pi_src e" by (cases e) simp
next
 fix e assume "e\<in>{e. pi_admissible Y e}"
 show "pi_flip(pi_flip e)=e" by (cases e) (simp add: pi_reverse_reverse)
next
 fix e a b assume "e\<in>{e. pi_admissible Y e}" "pi_act e a b"
 then show "a\<in>Y(pi_src e) \<and> b\<in>Y(pi_dst e)" by (auto simp: pi_admissible_def)
next
 fix e a b c assume "e\<in>{e. pi_admissible Y e}" "pi_act e a b" "pi_act e a c"
 then show "b=c" by (auto simp: pi_admissible_def pi_injection_def)
next
 fix e a b assume "e\<in>{e. pi_admissible Y e}"
 show "pi_act(pi_flip e)b a=pi_act e a b" by (cases e) (simp add: pi_reverse_def)
qed

theorem empty_sequence:
 "W.action u [] u a b \<longleftrightarrow> a\<in>Y u \<and> a=b"
 by (rule W.empty_action)

theorem sequence_append:
 assumes p: "W.typed u es v" and q: "W.typed v fs w"
 shows "W.action u (es@fs) w=pi_comp(W.action u es v)(W.action v fs w)"
 by (intro ext) (simp add: W.action_append[OF p q] pi_comp_def)

theorem sequence_append_domain:
 assumes p: "W.typed u es v" and q: "W.typed v fs w"
 shows "a\<in>pi_domain(W.action u (es@fs) w) \<longleftrightarrow>
  (\<exists>b. W.action u es v a b \<and> b\<in>pi_domain(W.action v fs w))"
 by (simp only: sequence_append[OF p q] composition_domain)

theorem sequence_reverse:
 assumes p: "W.typed u es v"
 shows "W.action v (map pi_flip(rev es))u=pi_reverse(W.action u es v)"
 by (intro ext) (simp add: W.action_reverse[OF p] pi_reverse_def)

theorem sequence_partial_injectivity:
 "pi_injection(W.action u es v)"
 unfolding pi_injection_def using W.action_functional W.action_injective by blast

theorem sequence_inverse_identity:
 assumes p: "W.typed u es v"
 shows "W.action u (es@map pi_flip(rev es)) u a c \<longleftrightarrow>
  a=c \<and> a\<in>pi_domain(W.action u es v)"
proof -
 have rev: "W.typed v (map pi_flip(rev es))u" by (rule W.typed_reverse[OF p])
 show ?thesis
  by (simp only: sequence_append[OF p rev] sequence_reverse[OF p]
   inverse_composition_on_domain[OF sequence_partial_injectivity])
qed
end

definition pi_tag where
 "pi_tag i j R p q \<longleftrightarrow> fst p=i \<and> fst q=j \<and> R(snd p)(snd q)"
theorem tagged_graph_reverse:
 "pi_reverse(pi_tag i j R)=pi_tag j i (pi_reverse R)"
 by (intro ext) (auto simp: pi_reverse_def pi_tag_def)

definition source_partial_domain where
 "source_partial_domain D f i j={a\<in>image(f i)(D i). recovery D f i a\<in>D j}"
definition source_partial_graph where
 "source_partial_graph D f i j=pi_graph(source_partial_domain D f i j)(src_match D f i j)"
definition source_term where
 "source_term D f i j=pi_tag i j (source_partial_graph D f i j)"

locale source_family =
 fixes D :: "'u\<Rightarrow>'s set" and f :: "'u\<Rightarrow>'s\<Rightarrow>'v"
 assumes injective: "\<And>i. inj_on(f i)(D i)"
begin

theorem source_partial_graph:
 "Core_Partial_Sequences.source_partial_graph D f i j a b \<longleftrightarrow> src_graph D f i j a b"
 by (auto simp: Core_Partial_Sequences.source_partial_graph_def source_partial_domain_def pi_graph_def src_graph_def)

lemma source_graph_typed:
 "src_graph D f i j a b \<Longrightarrow> a\<in>image(f i)(D i) \<and> b\<in>image(f j)(D j)"
 by (auto simp: src_graph_def src_match_def)

theorem source_reverse:
 "Core_Partial_Sequences.source_partial_graph D f j i=pi_reverse(Core_Partial_Sequences.source_partial_graph D f i j)"
proof (intro ext)
 fix b a
 have eq: "src_graph D f j i b a \<longleftrightarrow> src_graph D f i j a b"
 proof
  assume h: "src_graph D f j i b a"
  have b: "b\<in>image(f j)(D j)" and a: "a\<in>image(f i)(D i)" using source_graph_typed[OF h] by auto
  show "src_graph D f i j a b" using source_match_inverse_graph[OF injective injective b a] h by blast
 next
  assume h: "src_graph D f i j a b"
  have a: "a\<in>image(f i)(D i)" and b: "b\<in>image(f j)(D j)" using source_graph_typed[OF h] by auto
  show "src_graph D f j i b a" using source_match_inverse_graph[OF injective injective a b] h by blast
 qed
 show "Core_Partial_Sequences.source_partial_graph D f j i b a=
  pi_reverse(Core_Partial_Sequences.source_partial_graph D f i j) b a"
  using eq by (simp add: source_partial_graph pi_reverse_def)
qed

theorem source_term_inverse:
 "source_term D f j i=pi_reverse(source_term D f i j)"
 unfolding source_term_def using source_reverse[where i=i and j=j]
 by (simp only: tagged_graph_reverse)

theorem source_term_domain:
 assumes p: "p\<in>{i}\<times>image(f i)(D i)"
 shows "p\<in>pi_domain(source_term D f i j) \<longleftrightarrow> recovery D f i (snd p)\<in>D j"
 using p by (auto simp: pi_domain_def source_term_def pi_tag_def
  Core_Partial_Sequences.source_partial_graph_def pi_graph_def source_partial_domain_def)

lemma source_term_injection: "pi_injection(source_term D f i j)"
proof -
 have functional: "\<And>a b c. src_graph D f i j a b \<Longrightarrow> src_graph D f i j a c \<Longrightarrow> b=c"
  by (rule source_match_functional)
 have inj: "\<And>a b c. src_graph D f i j a c \<Longrightarrow> src_graph D f i j b c \<Longrightarrow> a=b"
  by (rule source_match_injective[where D=D and f=f and u=i and v=j, OF injective])
 show ?thesis using functional inj unfolding pi_injection_def source_term_def pi_tag_def
  by (auto simp: source_partial_graph intro!: prod_eqI)
qed

theorem source_term_composition_identity:
 "pi_comp(source_term D f i j)(source_term D f j i) a c \<longleftrightarrow>
  a=c \<and> a\<in>pi_domain(source_term D f i j)"
 by (simp only: source_term_inverse[where i=i and j=j]
  inverse_composition_on_domain[OF source_term_injection])
end

theorem empty_carrier_supported: "pi_domain(pi_graph {} f)={}"
 by (rule partial_graph_domain)

ML \<open>
val roots = @{thms partial_graph_domain partial_graph_value reverse_domain_is_image
 inverse_composition_on_domain composition_domain all_partial_graphs.empty_sequence
 all_partial_graphs.sequence_append all_partial_graphs.sequence_append_domain all_partial_graphs.sequence_reverse
 all_partial_graphs.sequence_inverse_identity all_partial_graphs.sequence_partial_injectivity
 tagged_graph_reverse source_family.source_partial_graph source_family.source_reverse
 source_family.source_term_inverse source_family.source_term_domain
 source_family.source_term_composition_identity empty_carrier_supported};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
