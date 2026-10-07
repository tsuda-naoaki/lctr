theory Core_Finite_Mixed_Reduction
 imports "LCTR_Core_Indexed_Native_Deletion.Core_Indexed_Native_Deletion"
  "LCTR_Core_Pure_Word_Displays.Core_Pure_Word_Displays"
begin
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

lemma deletion_preserves_transport_count:
 "delete_loop u v p q \<Longrightarrow> transport_count q=transport_count p"
 by (erule delete_loop.cases)
  (auto simp: Core_Native_Word_Families.append_counts Core_Native_Word_Families.source_only_iff)

lemma reduction_preserves_transport_count:
 "source_reduction u v p q \<Longrightarrow> transport_count q=transport_count p"
 by (induction rule: source_reduction.induct) (auto dest: deletion_preserves_transport_count)

lemma reduction_preserves_typing:
 "source_reduction u v p q \<Longrightarrow> W.typed u p v \<Longrightarrow> W.typed u q v"
 by (induction rule: source_reduction.induct) (auto dest: deleted_word_typed)

lemma terminal_classification:
 assumes tp: "W.typed u p v" and mix: "mixed_word p"
  and red: "source_reduction u v p q" and irr: "irreducible u v q"
 shows "(mixed_word q \<and> irreducible u v q) \<or> (\<exists>t. t\<in>transport_words u v \<and> t=q)"
proof -
 have tq: "W.typed u q v" by (rule reduction_preserves_typing[OF red tp])
 have positive: "0<transport_count q"
  using mix reduction_preserves_transport_count[OF red] by (simp add: mixed_word_def)
 show ?thesis using positive tq irr
  by (cases "source_count q=0") (auto simp: mixed_word_def transport_words_def transport_only_iff)
qed

definition trace where
 "trace u v p q N ws =
  (ws 0=p \<and> ws N=q \<and>
   (\<forall>n<N. delete_loop u v (ws n) (ws (Suc n))) \<and>
   (\<forall>n\<le>N. source_reduction u v p (ws n)))"

lemma reduction_trace:
 "source_reduction u v p q \<Longrightarrow> \<exists>N ws. trace u v p q N ws"
proof (induction rule: source_reduction.induct)
 case (refl u v p)
 have "trace u v p p 0 (\<lambda>_. p)"
  by (simp add: trace_def source_reduction.refl)
 then show ?case by blast
next
 case (step u v p q r)
 obtain N ws where tr: "trace u v q r N ws" using step.IH by blast
 have first: "ws 0=q" and last: "ws N=r"
  and steps: "\<forall>n<N. delete_loop u v (ws n) (ws (Suc n))"
  and reach: "\<forall>n\<le>N. source_reduction u v q (ws n)"
  using tr unfolding trace_def by auto
 let ?gs = "case_nat p ws"
 have edges: "\<forall>n<Suc N. delete_loop u v (?gs n) (?gs (Suc n))"
 proof (intro allI impI)
  fix n assume bound: "n<Suc N"
  show "delete_loop u v (?gs n) (?gs (Suc n))"
  proof (cases n)
   case 0
   then show ?thesis using step.hyps(1) first by simp
  next
   case (Suc k)
   have "k<N" using bound Suc by simp
   then have "delete_loop u v (ws k) (ws (Suc k))" using steps by blast
   then show ?thesis by (simp add: Suc)
  qed
 qed
 have accessible: "\<forall>n\<le>Suc N. source_reduction u v p (?gs n)"
 proof (intro allI impI)
  fix n assume bound: "n\<le>Suc N"
  show "source_reduction u v p (?gs n)"
  proof (cases n)
   case 0
   then show ?thesis by (simp add: source_reduction.refl)
  next
   case (Suc k)
   have "k\<le>N" using bound Suc by simp
   then have tail: "source_reduction u v q (ws k)" using reach by blast
   have "source_reduction u v p (ws k)" by (rule source_reduction.step[OF step.hyps(1) tail])
   then show ?thesis by (simp add: Suc)
  qed
 qed
 have "trace u v p r (Suc N) ?gs"
  using first last edges accessible by (simp add: trace_def)
 then show ?case by blast
qed

lemma trace_domain_extension:
 assumes tr: "trace u v p q N ws" and bound: "n\<le>N"
  and dom: "\<exists>b. W.action u p v a b"
 shows "\<exists>b. W.action u (ws n) v a b"
proof -
 have red: "source_reduction u v p (ws n)" using tr bound unfolding trace_def by blast
 obtain b where run: "W.action u p v a b" using dom by blast
 have "W.action u (ws n) v a b" by (rule reduction_extends_action[OF red run])
 then show ?thesis by blast
qed

lemma trace_exact_on_old_domain:
 assumes tr: "trace u v p q N ws" and bound: "n\<le>N"
  and dom: "\<exists>c. W.action u p v a c"
 shows "W.action u (ws n) v a b = W.action u p v a b"
proof -
 have red: "source_reduction u v p (ws n)" using tr bound unfolding trace_def by blast
 show ?thesis by (rule reduction_exact_on_old_domain[OF red dom])
qed

lemma trace_typed:
 assumes tp: "W.typed u p v" and tr: "trace u v p q N ws" and bound: "n\<le>N"
 shows "W.typed u (ws n) v"
proof -
 have red: "source_reduction u v p (ws n)" using tr bound unfolding trace_def by blast
 show ?thesis by (rule reduction_preserves_typing[OF red tp])
qed

lemma mixed_reduction_trace:
 assumes tp: "W.typed u p u" and mix: "mixed_word p"
 shows "\<exists>N ws. trace u u p (ws N) N ws \<and>
  ((mixed_word (ws N) \<and> irreducible u u (ws N)) \<or>
   (\<exists>t. t\<in>transport_words u u \<and> t=ws N))"
proof -
 obtain q where red: "source_reduction u u p q" and irr: "irreducible u u q"
  using finite_source_reduction[where u=u and v=u and p=p] by blast
 obtain N ws where tr: "trace u u p q N ws" using reduction_trace[OF red] by blast
 have last: "ws N=q" using tr unfolding trace_def by simp
 have terminal: "(mixed_word q \<and> irreducible u u q) \<or> (\<exists>t. t\<in>transport_words u u \<and> t=q)"
  by (rule terminal_classification[OF tp mix red irr])
 have combined: "trace u u p (ws N) N ws \<and>
  ((mixed_word (ws N) \<and> irreducible u u (ws N)) \<or> (\<exists>t. t\<in>transport_words u u \<and> t=ws N))"
  using tr terminal by (simp only: last)
 show ?thesis by (rule exI[of _ N], rule exI[of _ ws], rule combined)
qed

lemma terminal_transport_display:
 assumes t: "t\<in>transport_words u u"
 shows "map transport_kind (directions t)=native_kinds t \<and>
  length(fst(snd(transport_display u t)))=length t+1 \<and>
  length(snd(snd(transport_display u t)))=length t"
 using t by (simp add: transport_words_def transport_kinds_recovered
  transport_display_def native_position_length direction_length)

lemma mixed_indexed_trace:
 assumes tp: "W.typed u p u" and mix: "mixed_word p"
 shows "\<exists>N ws. ws 0=p \<and> (\<forall>n\<le>N. W.typed u (ws n) u) \<and>
  (\<forall>n<N. indexed_delete Src u (decode(ws n)) (decode(ws (Suc n)))) \<and>
  ((mixed_word (ws N) \<and> \<not>(\<exists>es. indexed_delete Src u (decode(ws N)) es)) \<or>
   (\<exists>t. t\<in>transport_words u u \<and> t=ws N)) \<and>
  (\<forall>n\<le>N. \<forall>a. (\<exists>b. W.action u p u a b) \<longrightarrow>
   (\<exists>b. W.action u (ws n) u a b) \<and>
   (\<forall>b. W.action u (ws n) u a b = W.action u p u a b))"
proof -
 obtain N ws where tr: "trace u u p (ws N) N ws"
  and terminal: "(mixed_word (ws N) \<and> irreducible u u (ws N)) \<or>
   (\<exists>t. t\<in>transport_words u u \<and> t=ws N)"
  using mixed_reduction_trace[OF tp mix] by blast
 have first: "ws 0=p" using tr unfolding trace_def by simp
 have typed: "\<forall>n\<le>N. W.typed u (ws n) u"
  by (intro allI impI, rule trace_typed[OF tp tr])
 have edges: "\<forall>n<N. indexed_delete Src u (decode(ws n)) (decode(ws(Suc n)))"
 proof (intro allI impI)
  fix n assume bound: "n<N"
  have del: "delete_loop u u (ws n) (ws(Suc n))" using tr bound unfolding trace_def by blast
  show "indexed_delete Src u (decode(ws n)) (decode(ws(Suc n)))" by (rule native_to_indexed[OF del])
 qed
 have final_type: "W.typed u (ws N) u" by (rule trace_typed[OF tp tr le_refl])
 have final: "(mixed_word (ws N) \<and> \<not>(\<exists>es. indexed_delete Src u (decode(ws N)) es)) \<or>
   (\<exists>t. t\<in>transport_words u u \<and> t=ws N)"
  using terminal by (simp only: irreducible_iff_no_indexed[OF final_type])
 have action: "\<forall>n\<le>N. \<forall>a. (\<exists>b. W.action u p u a b) \<longrightarrow>
   (\<exists>b. W.action u (ws n) u a b) \<and>
   (\<forall>b. W.action u (ws n) u a b = W.action u p u a b)"
 proof (intro allI impI)
  fix n a assume bound: "n\<le>N" and dom: "\<exists>b. W.action u p u a b"
  show "(\<exists>b. W.action u (ws n) u a b) \<and>
   (\<forall>b. W.action u (ws n) u a b = W.action u p u a b)"
  proof
   show "\<exists>b. W.action u (ws n) u a b" by (rule trace_domain_extension[OF tr bound dom])
   show "\<forall>b. W.action u (ws n) u a b = W.action u p u a b"
    by (intro allI, rule trace_exact_on_old_domain[OF tr bound dom])
  qed
 qed
 show ?thesis
  by (rule exI[of _ N], rule exI[of _ ws])
   (use first typed edges final action in \<open>simp\<close>)
qed

end
ML \<open>
val roots = @{thms native_comparison.deletion_preserves_transport_count
 native_comparison.reduction_preserves_transport_count native_comparison.terminal_classification
 native_comparison.reduction_trace native_comparison.trace_domain_extension
 native_comparison.trace_exact_on_old_domain native_comparison.mixed_reduction_trace
 native_comparison.terminal_transport_display native_comparison.mixed_indexed_trace};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
