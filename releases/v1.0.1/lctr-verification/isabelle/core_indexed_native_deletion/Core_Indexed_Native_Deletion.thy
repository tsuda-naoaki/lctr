theory Core_Indexed_Native_Deletion
 imports "LCTR_Core_Word_Encoding.Core_Word_Encoding"
  "LCTR_Core_Indexed_Deletion.Core_Indexed_Deletion"
begin

lemma view_append: "decode(p@q)=decode p@decode q" by (simp add: decode_def)
lemma view_length: "length(decode p)=length p" by (simp add: decode_def)
lemma source_atom_kind: "source_atom e = (kind_of e=Src)" by (cases e) simp_all
lemma view_source:
 "Core_Source_Loops.source_only p = Core_Indexed_Deletion.source_only Src (decode p)"
 by (simp add: Core_Source_Loops.source_only_def Core_Indexed_Deletion.source_only_def decode_def source_atom_kind)

lemma raw_valid:
 "raw_typed adm u es v = valid_edges (admissible adm) u es v"
 by (induction es arbitrary: u) (auto split: prod.splits)

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

lemma view_valid: "W.typed u p v \<Longrightarrow> valid_edges (admissible adm) u (decode p) v"
 using decode_typed by (simp only: raw_valid)

lemma view_reconstruction:
 "valid_edges (admissible adm) u es v \<Longrightarrow> \<exists>p. W.typed u p v \<and> decode p=es"
 by (intro exI[of _ "encode u es"]) (simp add: encode_typed raw_valid decode_encode)

lemma view_injective:
 assumes p: "W.typed u p v" and q: "W.typed u q v" and eq: "decode p=decode q"
 shows "p=q"
proof -
 have "encode u (decode p)=encode u (decode q)" by (simp only: eq)
 then show ?thesis by (simp only: encode_decode[OF p] encode_decode[OF q])
qed

lemma view_terminal: "W.typed u p v \<Longrightarrow> final_node u (decode p)=v"
 by (induction p arbitrary: u) (auto simp: decode_def)

lemma native_to_indexed:
 assumes del: "delete_loop u v p q"
 shows "indexed_delete Src u (decode p) (decode q)"
proof -
 obtain a mid c n where ta: "W.typed u a n" and tm: "W.typed n mid n" and tc: "W.typed n c v"
  and src: "Core_Source_Loops.source_only mid" and pos: "0<length mid"
  and pe: "p=(a@mid)@c" and qe: "q=a@c"
  using del by (cases rule: delete_loop.cases) auto
 have nz: "decode mid\<noteq>[]" using pos view_length[of mid] by auto
 have only_src: "Core_Indexed_Deletion.source_only Src (decode mid)" using src by (simp only: view_source)
 have close: "final_node u (decode a)=final_node u (decode a@decode mid)"
  by (simp only: terminal_append view_terminal[OF ta] view_terminal[OF tm])
 have seg: "segment_delete Src u (decode p) (decode q)"
  unfolding segment_delete_def
  by (rule exI[of _ "decode a"], rule exI[of _ "decode mid"], rule exI[of _ "decode c"])
   (use pe qe nz only_src close in \<open>simp add: view_append\<close>)
 show ?thesis by (rule iffD2[OF indexed_iff_segment seg])
qed

lemma indexed_to_native:
 assumes tp: "W.typed u p v" and tq: "W.typed u q v"
  and idx: "indexed_delete Src u (decode p) (decode q)"
 shows "delete_loop u v p q"
proof -
 obtain a mid c where pe: "decode p=(a@mid)@c" and qe: "decode q=a@c" and nz: "mid\<noteq>[]"
  and src: "Core_Indexed_Deletion.source_only Src mid"
  and close: "final_node u a=final_node u (a@mid)"
  using indexed_to_segment[OF idx] unfolding segment_delete_def by blast
 have vp: "valid_edges (admissible adm) u ((a@mid)@c) v" using view_valid[OF tp] by (simp only: pe)
 have outer: "valid_edges (admissible adm) u (a@mid) (final_node u (a@mid)) \<and>
  valid_edges (admissible adm) (final_node u (a@mid)) c v" using vp by (simp only: valid_append)
 have inner: "valid_edges (admissible adm) u a (final_node u a) \<and>
  valid_edges (admissible adm) (final_node u a) mid (final_node u (a@mid))"
  using conjunct1[OF outer] by (simp only: valid_append)
 have vm: "valid_edges (admissible adm) (final_node u a) mid (final_node u a)"
  using conjunct2[OF inner] by (simp only: close)
 have vc: "valid_edges (admissible adm) (final_node u a) c v"
  using conjunct2[OF outer] by (simp only: close)
 obtain pa where ta: "W.typed u pa (final_node u a)" and ea: "decode pa=a"
  using view_reconstruction[OF conjunct1[OF inner]] by blast
 obtain pm where tm: "W.typed (final_node u a) pm (final_node u a)" and em: "decode pm=mid"
  using view_reconstruction[OF vm] by blast
 obtain pc where tc: "W.typed (final_node u a) pc v" and ec: "decode pc=c"
  using view_reconstruction[OF vc] by blast
 have tab: "W.typed u (pa@pm) (final_node u a)" using ta tm by (auto simp: W.typed_append)
 have tall: "W.typed u ((pa@pm)@pc) v" using tab tc by (auto simp: W.typed_append)
 have tout: "W.typed u (pa@pc) v" using ta tc by (auto simp: W.typed_append)
 have dp: "decode((pa@pm)@pc)=decode p" by (simp only: view_append ea em ec pe)
 have dq: "decode(pa@pc)=decode q" by (simp only: view_append ea ec qe)
 have ep: "(pa@pm)@pc=p" by (rule view_injective[OF tall tp dp])
 have eq: "pa@pc=q" by (rule view_injective[OF tout tq dq])
 have so: "Core_Source_Loops.source_only pm" using src by (simp only: view_source em)
 have pos: "0<length pm" using nz view_length[of pm] em by auto
 have del: "delete_loop u v ((pa@pm)@pc) (pa@pc)" by (rule delete_loop.segment[OF ta tm tc so pos])
 show ?thesis using del by (simp only: ep eq)
qed

lemma native_delete_iff:
 "W.typed u p v \<Longrightarrow> W.typed u q v \<Longrightarrow>
  (delete_loop u v p q = indexed_delete Src u (decode p) (decode q))"
 by (rule iffI, erule native_to_indexed, erule (2) indexed_to_native)

lemma deleted_word_typed: "delete_loop u v p q \<Longrightarrow> W.typed u q v"
 by (cases rule: delete_loop.cases) (auto simp: W.typed_append)

lemma irreducible_iff_no_indexed:
 assumes tp: "W.typed u p v"
 shows "irreducible u v p = (\<not>(\<exists>fs. indexed_delete Src u (decode p) fs))"
proof
 assume irr: "irreducible u v p"
 show "\<not>(\<exists>fs. indexed_delete Src u (decode p) fs)"
 proof
  assume "\<exists>fs. indexed_delete Src u (decode p) fs"
  then obtain fs where ix: "indexed_delete Src u (decode p) fs" by blast
  have vf: "valid_edges (admissible adm) u fs v" by (rule deletion_preserves_typing[OF view_valid[OF tp] ix])
  obtain q where tq: "W.typed u q v" and eq: "decode q=fs" using view_reconstruction[OF vf] by blast
  have idx: "indexed_delete Src u (decode p) (decode q)" using ix by (simp only: eq)
  have del: "delete_loop u v p q" by (rule indexed_to_native[OF tp tq idx])
  show False using irr del unfolding irreducible_def by blast
 qed
next
 assume no: "\<not>(\<exists>fs. indexed_delete Src u (decode p) fs)"
 show "irreducible u v p" unfolding irreducible_def
  using no native_to_indexed by blast
qed

lemma indexed_action_extension:
 assumes tp: "W.typed u p v" and tq: "W.typed u q v"
  and ix: "indexed_delete Src u (decode p) (decode q)" and run: "W.action u p v a b"
 shows "W.action u q v a b"
 by (rule deletion_extends_action[OF indexed_to_native[OF tp tq ix] run])

lemma indexed_exact_on_old_domain:
 assumes tp: "W.typed u p v" and tq: "W.typed u q v"
  and ix: "indexed_delete Src u (decode p) (decode q)" and dom: "\<exists>c. W.action u p v a c"
 shows "W.action u q v a b = W.action u p v a b"
 by (rule deletion_exact_on_old_domain[OF indexed_to_native[OF tp tq ix] dom])

end
ML \<open>
val roots = @{thms native_comparison.view_valid native_comparison.view_reconstruction native_comparison.view_injective
 view_append view_length view_source native_comparison.native_delete_iff native_comparison.irreducible_iff_no_indexed
 native_comparison.indexed_action_extension native_comparison.indexed_exact_on_old_domain};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
