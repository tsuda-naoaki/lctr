theory Core_Native_Word_Families
 imports "LCTR_Core_Source_Loops.Core_Source_Loops"
begin
definition source_count where "source_count es=length(filter source_atom es)"
definition transport_count where "transport_count es=length(filter (\<lambda>e. \<not>source_atom e) es)"

theorem length_partition: "length es=source_count es+transport_count es"
 by (induction es) (auto simp: source_count_def transport_count_def)
theorem source_only_iff: "source_only es \<longleftrightarrow> transport_count es=0"
 by (auto simp: source_only_def transport_count_def filter_empty_conv)
theorem transport_only_iff: "transport_only es \<longleftrightarrow> source_count es=0"
 by (auto simp: transport_only_def source_count_def filter_empty_conv)
theorem append_counts:
 "source_count(p@q)=source_count p+source_count q \<and>
  transport_count(p@q)=transport_count p+transport_count q"
 by (simp add: source_count_def transport_count_def)
lemma inverted_source [simp]: "source_atom(inverted e)=source_atom e"
 by (cases e) simp_all
theorem reverse_counts:
 "source_count(map inverted(rev es))=source_count es \<and>
  transport_count(map inverted(rev es))=transport_count es"
 by (induction es) (auto simp: source_count_def transport_count_def)
theorem pure_families_closed:
 "(source_only(p@q) \<longleftrightarrow> source_only p \<and> source_only q) \<and>
  (transport_only(p@q) \<longleftrightarrow> transport_only p \<and> transport_only q) \<and>
  (source_only(map inverted(rev p)) \<longleftrightarrow> source_only p) \<and>
  (transport_only(map inverted(rev p)) \<longleftrightarrow> transport_only p)"
 by (simp add: source_only_iff transport_only_iff append_counts reverse_counts)

definition mixed_word where "mixed_word es=(0<source_count es \<and> 0<transport_count es)"
definition word_case where
 "word_case es c = ((c=0 \<and> length es=0) \<or>
   (c=1 \<and> 0<length es \<and> transport_only es) \<or>
   (c=2 \<and> 0<length es \<and> source_only es) \<or>
   (c=3 \<and> mixed_word es))"
theorem four_cases_exist_unique:
 "\<exists>!c::nat. c<4 \<and> word_case es c"
proof -
 have n: "length es=source_count es+transport_count es" by (rule length_partition)
 show ?thesis
  using n
  by (cases "source_count es=0"; cases "transport_count es=0")
   (auto simp: word_case_def mixed_word_def source_only_iff transport_only_iff)
qed
theorem common_pure_family_iff_empty:
 "source_only es \<and> transport_only es \<longleftrightarrow> length es=0"
 using length_partition[of es] by (auto simp: source_only_iff transport_only_iff)

context native_comparison
begin
interpretation W: typed_actions "regions D f" "{e. admitted adm e}" initial terminal inverted "cmp_act D f tr"
proof
  fix e assume "e\<in>{e. admitted adm e}"
  then show "inverted e\<in>{e. admitted adm e}" by (cases e) auto
next
  fix e assume "e\<in>{e. admitted adm e}"
  show "initial (inverted e)=terminal e" by (cases e) auto
next
  fix e assume "e\<in>{e. admitted adm e}"
  show "terminal (inverted e)=initial e" by (cases e) auto
next
  fix e assume "e\<in>{e. admitted adm e}"
  show "inverted (inverted e)=e" by (cases e) auto
next
  fix e p q assume "e\<in>{e. admitted adm e}" and pq: "cmp_act D f tr e p q"
  show "p\<in>regions D f (initial e) \<and> q\<in>regions D f (terminal e)" by (rule atom_type[OF pq])
next
  fix e p q r assume "e\<in>{e. admitted adm e}" and "cmp_act D f tr e p q" and "cmp_act D f tr e p r"
  then show "q=r" using atom_functional by auto
next
  fix e p q assume "e\<in>{e. admitted adm e}"
  show "cmp_act D f tr (inverted e) q p = cmp_act D f tr e p q" by (rule atom_inverse)
qed

definition source_words where "source_words u v={es. W.typed u es v \<and> source_only es}"
definition transport_words where "transport_words u v={es. W.typed u es v \<and> transport_only es}"

theorem standard_embeddings_injective:
 "inj_on id (source_words u v) \<and> inj_on id (transport_words u v)"
 by simp

theorem standard_embeddings_operations:
 assumes p: "p\<in>source_words u v" and q: "q\<in>source_words v w"
 and r: "r\<in>transport_words u v" and s: "s\<in>transport_words v w"
 shows "p@q\<in>source_words u w \<and> r@s\<in>transport_words u w \<and>
   map inverted(rev p)\<in>source_words v u \<and>
   map inverted(rev r)\<in>transport_words v u \<and>
   []\<in>source_words u u \<and> []\<in>transport_words u u \<and>
   id(p@q)=id p@id q \<and> id(r@s)=id r@id s \<and>
   id(map inverted(rev p))=map inverted(rev(id p)) \<and>
   id(map inverted(rev r))=map inverted(rev(id r))"
 using assms W.typed_reverse
 by (auto simp: source_words_def transport_words_def W.typed_append
  source_only_def transport_only_def)

theorem extended_action_laws:
 assumes p: "W.typed u es v" and q: "W.typed v fs w" and a: "a\<in>regions D f u"
 shows "(W.action v (map inverted(rev es)) u b a \<longleftrightarrow> W.action u es v a b) \<and>
  ((\<exists>z. W.action u (es@fs) w a z) \<longleftrightarrow>
    (\<exists>z. W.action u es v a z \<and> (\<exists>c. W.action v fs w z c))) \<and>
  (W.action u (es@fs) w a c \<longleftrightarrow> (\<exists>z. W.action u es v a z \<and> W.action v fs w z c)) \<and>
  (\<forall>b. W.action u [] u a b \<longleftrightarrow> a=b)"
 using W.action_reverse[OF p] W.action_append_domain[OF p q] W.action_append[OF p q] a
 by (simp add: W.empty_action)

theorem source_action_laws:
 assumes p: "es\<in>source_words u v" and q: "fs\<in>source_words v w" and a: "a\<in>regions D f u"
 shows "(W.action v (map inverted(rev es)) u b a \<longleftrightarrow> W.action u es v a b) \<and>
  ((\<exists>z. W.action u (es@fs) w a z) \<longleftrightarrow>
    (\<exists>z. W.action u es v a z \<and> (\<exists>c. W.action v fs w z c))) \<and>
  (W.action u (es@fs) w a c \<longleftrightarrow> (\<exists>z. W.action u es v a z \<and> W.action v fs w z c)) \<and>
  (\<forall>b. W.action u [] u a b \<longleftrightarrow> a=b)"
 by (rule extended_action_laws) (use p q a in \<open>auto simp: source_words_def\<close>)

theorem transport_action_laws:
 assumes p: "es\<in>transport_words u v" and q: "fs\<in>transport_words v w" and a: "a\<in>regions D f u"
 shows "(W.action v (map inverted(rev es)) u b a \<longleftrightarrow> W.action u es v a b) \<and>
  ((\<exists>z. W.action u (es@fs) w a z) \<longleftrightarrow>
    (\<exists>z. W.action u es v a z \<and> (\<exists>c. W.action v fs w z c))) \<and>
  (W.action u (es@fs) w a c \<longleftrightarrow> (\<exists>z. W.action u es v a z \<and> W.action v fs w z c)) \<and>
  (\<forall>b. W.action u [] u a b \<longleftrightarrow> a=b)"
 by (rule extended_action_laws) (use p q a in \<open>auto simp: transport_words_def\<close>)

theorem native_partial_injectivity:
 "(\<forall>a b c. W.action u es v a b \<longrightarrow> W.action u es v a c \<longrightarrow> b=c) \<and>
  (\<forall>a b c. W.action u es v a c \<longrightarrow> W.action u es v b c \<longrightarrow> a=b)"
 using W.action_functional W.action_injective by blast

theorem unique_pure_preimages:
 assumes typed: "W.typed u es v"
 shows "(transport_only es \<longrightarrow> (\<exists>!q. q\<in>transport_words u v \<and> id q=es)) \<and>
   (source_only es \<longrightarrow> (\<exists>!q. q\<in>source_words u v \<and> id q=es))"
 using typed by (auto simp: source_words_def transport_words_def)
end

ML \<open>
val roots = @{thms length_partition source_only_iff transport_only_iff append_counts reverse_counts
 pure_families_closed native_comparison.standard_embeddings_injective
 native_comparison.standard_embeddings_operations native_comparison.source_action_laws
 native_comparison.transport_action_laws native_comparison.extended_action_laws
 native_comparison.native_partial_injectivity four_cases_exist_unique
 native_comparison.unique_pure_preimages common_pure_family_iff_empty};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
