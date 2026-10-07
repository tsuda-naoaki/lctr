theory Core_Word_Encoding
 imports "LCTR_Core_Native_Word_Families.Core_Native_Word_Families"
begin
fun make_atom where
 "make_atom u v Src=Source u v" |
 "make_atom u v TrPlus=Forward u v" |
 "make_atom u v TrMinus=Backward u v"
fun kind_of where
 "kind_of(Source u v)=Src" |
 "kind_of(Forward u v)=TrPlus" |
 "kind_of(Backward u v)=TrMinus"
fun encode where
 "encode u []=[]" |
 "encode u ((v,k)#es)=make_atom u v k # encode v es"
definition decode where "decode es=map (\<lambda>e. (terminal e,kind_of e)) es"
fun raw_typed where
 "raw_typed adm u [] v=(u=v)" |
 "raw_typed adm u ((w,k)#es) v=(admissible adm k u w \<and> raw_typed adm w es v)"
definition raw_positions where "raw_positions u es=u#map fst es"
definition raw_kinds where "raw_kinds es=map snd es"
definition display_tuple where "display_tuple u es=(length(raw_kinds es),raw_positions u es,raw_kinds es)"

lemma make_atom_properties [simp]:
 "initial(make_atom u v k)=u"
 "terminal(make_atom u v k)=v"
 "kind_of(make_atom u v k)=k"
 "admitted adm (make_atom u v k)=admissible adm k u v"
 by (cases k; simp)+
lemma make_atom_roundtrip [simp]: "make_atom (initial e) (terminal e) (kind_of e)=e"
 by (cases e) simp_all
theorem decode_encode: "decode(encode u es)=es"
 by (induction es arbitrary: u) (auto simp: decode_def split: prod.splits)
theorem positions_from_edges: "raw_positions u es=u#map fst es"
 by (rule raw_positions_def)
theorem kinds_from_edges: "raw_kinds es=map snd es"
 by (rule raw_kinds_def)
theorem edges_injective: "id es=id fs \<Longrightarrow> es=fs"
 by simp
theorem displayed_tuple_injective: "inj(display_tuple u)"
proof (rule injI)
 fix es fs assume h: "display_tuple u es=display_tuple u fs"
 have left: "map fst es=map fst fs" and right: "map snd es=map snd fs"
  using h by (auto simp: display_tuple_def raw_positions_def raw_kinds_def)
 have "zip (map fst es) (map snd es)=zip (map fst fs) (map snd fs)"
  by (simp only: left right)
 then show "es=fs" by (simp add: zip_map_fst_snd)
qed
theorem tuple_lengths: "length(raw_positions u es)=length(raw_kinds es)+1"
 by (simp add: raw_positions_def raw_kinds_def)
theorem native_length_preserved: "length(encode u es)=length(raw_kinds es)"
 by (induction es arbitrary: u) (auto simp: raw_kinds_def split: prod.splits)

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

lemma encode_typed: "W.typed u (encode u es) v \<longleftrightarrow> raw_typed adm u es v"
 by (induction es arbitrary: u) (auto split: prod.splits)

theorem encode_decode:
 "W.typed u es v \<Longrightarrow> encode u (decode es)=es"
 by (induction es arbitrary: u) (auto simp: decode_def split: comparison_atom.splits)

lemma decode_typed:
 "W.typed u es v \<Longrightarrow> raw_typed adm u (decode es) v"
 using encode_typed encode_decode by metis

theorem encoding_bijective:
 "bij_betw (encode u) {es. raw_typed adm u es v} {es. W.typed u es v}"
proof (unfold bij_betw_def, intro conjI)
 show "inj_on (encode u) {es. raw_typed adm u es v}"
 proof (rule inj_onI)
  fix es fs assume "encode u es=encode u fs"
  then have "decode(encode u es)=decode(encode u fs)" by simp
  then show "es=fs" by (simp only: decode_encode)
 qed
 show "image (encode u) {es. raw_typed adm u es v}={es. W.typed u es v}"
 proof (rule set_eqI)
  fix es
  show "es\<in>image (encode u) {es. raw_typed adm u es v} \<longleftrightarrow> es\<in>{es. W.typed u es v}"
  proof
   assume "es\<in>image (encode u) {es. raw_typed adm u es v}"
   then show "es\<in>{es. W.typed u es v}" by (auto simp: encode_typed)
  next
   assume h: "es\<in>{es. W.typed u es v}"
   have ty: "W.typed u es v" using h by simp
   have raw: "decode es\<in>{es. raw_typed adm u es v}" using decode_typed[OF ty] by simp
   have eq: "es=encode u (decode es)" using encode_decode[OF ty] by simp
   show "es\<in>image (encode u) {es. raw_typed adm u es v}"
    by (rule image_eqI[where x="decode es"]) (rule eq, rule raw)
  qed
 qed
qed

fun raw_action where
 "raw_action u [] a v b=(u=v \<and> a=b)" |
 "raw_action u ((w,k)#es) a v b=(\<exists>c. cmp_act D f tr (make_atom u w k) a c \<and> raw_action w es c v b)"
lemma raw_sequence:
 "raw_typed adm u es v \<Longrightarrow>
  raw_action u es a v b=sequence (cmp_act D f tr) (encode u es) a b"
 by (induction es arbitrary: u a) (auto split: prod.splits)

theorem action_preservation:
 "raw_typed adm u es v \<Longrightarrow> a\<in>regions D f u \<Longrightarrow>
  W.action u (encode u es) v a b \<longleftrightarrow> raw_action u es a v b"
 using raw_sequence by (simp add: W.action_def encode_typed)
theorem domain_preservation:
 "raw_typed adm u es v \<Longrightarrow> a\<in>regions D f u \<Longrightarrow>
  ((\<exists>b. W.action u (encode u es) v a b) \<longleftrightarrow> (\<exists>b. raw_action u es a v b))"
 using action_preservation by blast

theorem native_display_injective:
 "inj_on (\<lambda>es. display_tuple u (decode es)) {es. W.typed u es v}"
proof (rule inj_onI)
 fix es fs
 assume es: "es\<in>{es. W.typed u es v}" and fs: "fs\<in>{es. W.typed u es v}"
 and h: "display_tuple u (decode es)=display_tuple u (decode fs)"
 have raw: "decode es=decode fs" by (rule injD[OF displayed_tuple_injective h])
 have "encode u (decode es)=encode u (decode fs)" by (simp only: raw)
 then show "es=fs" using es fs by (simp add: encode_decode)
qed

theorem native_display_unique:
 assumes ty: "W.typed u es v"
 shows "\<exists>!q. raw_typed adm u q v \<and> encode u q=es \<and> display_tuple u q=display_tuple u (decode es)"
proof (rule ex1I[where a="decode es"])
 show "raw_typed adm u (decode es) v \<and> encode u (decode es)=es \<and> display_tuple u (decode es)=display_tuple u (decode es)"
  using decode_typed[OF ty] encode_decode[OF ty] by simp
next
 fix q assume h: "raw_typed adm u q v \<and> encode u q=es \<and> display_tuple u q=display_tuple u (decode es)"
 have eq: "display_tuple u q=display_tuple u (decode es)" using h by blast
 show "q=decode es" by (rule injD[OF displayed_tuple_injective eq])
qed
end
ML \<open>
val roots = @{thms decode_encode native_comparison.encode_decode native_comparison.encoding_bijective
 native_comparison.action_preservation native_comparison.domain_preservation
 positions_from_edges kinds_from_edges edges_injective displayed_tuple_injective tuple_lengths
 native_length_preserved native_comparison.native_display_injective native_comparison.native_display_unique};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
