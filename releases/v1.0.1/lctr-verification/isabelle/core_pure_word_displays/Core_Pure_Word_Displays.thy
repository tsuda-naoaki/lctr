theory Core_Pure_Word_Displays
 imports "LCTR_Core_Word_Encoding.Core_Word_Encoding"
begin
definition native_positions where "native_positions u es=u#map terminal es"
definition native_kinds where "native_kinds es=map kind_of es"
definition source_display where "source_display u es=(length es,native_positions u es)"
fun direction where "direction Src=False" | "direction TrPlus=True" | "direction TrMinus=False"
definition transport_kind where "transport_kind s=(if s then TrPlus else TrMinus)"
definition directions where "directions es=map direction (native_kinds es)"
definition transport_display where "transport_display u es=(length es,native_positions u es,directions es)"

lemma native_tuple:
 "display_tuple u (decode es)=(length es,native_positions u es,native_kinds es)"
 by (simp add: display_tuple_def decode_def raw_positions_def raw_kinds_def native_positions_def native_kinds_def comp_def)
theorem native_position_length: "length(native_positions u es)=length es+1"
 by (simp add: native_positions_def)
lemma source_kind [simp]: "source_atom e \<longleftrightarrow> kind_of e=Src"
 by (cases e) simp_all
lemma transport_kind_roundtrip:
 "\<not>source_atom e \<Longrightarrow> transport_kind(direction(kind_of e))=kind_of e"
 by (cases e) (simp_all add: transport_kind_def)
theorem source_kind_list_constant:
 "source_only es \<Longrightarrow> native_kinds es=replicate (length es) Src"
 by (induction es) (auto simp: source_only_def native_kinds_def split: comparison_atom.splits)
theorem transport_kinds_recovered:
 "transport_only es \<Longrightarrow> map transport_kind (directions es)=native_kinds es"
 by (induction es) (auto simp: transport_only_def directions_def native_kinds_def intro: transport_kind_roundtrip)
theorem direction_length: "length(directions es)=length es"
 by (simp add: directions_def native_kinds_def)
theorem source_direction_is_not_transport: "transport_kind(direction Src)\<noteq>Src"
 by (simp add: transport_kind_def)
theorem pure_display_shapes:
 "length(snd(source_display u es))=fst(source_display u es)+1 \<and>
  length(fst(snd(transport_display u fs)))=fst(transport_display u fs)+1 \<and>
  length(snd(snd(transport_display u fs)))=fst(transport_display u fs)"
 by (simp add: source_display_def transport_display_def native_position_length direction_length)

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

theorem source_positions_suffice:
 assumes es: "es\<in>source_words u v" and fs: "fs\<in>source_words u v"
 and pos: "native_positions u es=native_positions u fs"
 shows "es=fs"
proof -
 have ty1: "es\<in>{es. W.typed u es v}" and ty2: "fs\<in>{es. W.typed u es v}"
 and s1: "source_only es" and s2: "source_only fs"
  using es fs by (auto simp: source_words_def)
 have len: "length es=length fs"
  using arg_cong[OF pos, where f=length] by (simp add: native_position_length)
 have kinds: "native_kinds es=native_kinds fs"
  by (simp only: source_kind_list_constant[OF s1] source_kind_list_constant[OF s2] len)
 have tuple: "display_tuple u (decode es)=display_tuple u (decode fs)"
  by (simp only: native_tuple len pos kinds)
 show ?thesis by (rule inj_onD[OF native_display_injective tuple ty1 ty2])
qed

theorem source_display_injective: "inj_on (source_display u) (source_words u v)"
proof (rule inj_onI)
 fix es fs assume es: "es\<in>source_words u v" and fs: "fs\<in>source_words u v"
 and eq: "source_display u es=source_display u fs"
 have pos: "native_positions u es=native_positions u fs" using eq by (simp add: source_display_def)
 show "es=fs" by (rule source_positions_suffice[OF es fs pos])
qed

theorem transport_display_injective: "inj_on (transport_display u) (transport_words u v)"
proof (rule inj_onI)
 fix es fs assume es: "es\<in>transport_words u v" and fs: "fs\<in>transport_words u v"
 and eq: "transport_display u es=transport_display u fs"
 have ty1: "es\<in>{es. W.typed u es v}" and ty2: "fs\<in>{es. W.typed u es v}"
 and t1: "transport_only es" and t2: "transport_only fs"
  using es fs by (auto simp: transport_words_def)
 have pos: "native_positions u es=native_positions u fs"
 and signs: "directions es=directions fs" and len: "length es=length fs"
  using eq by (auto simp: transport_display_def)
 have mapped: "map transport_kind (directions es)=map transport_kind(directions fs)"
  by (simp only: signs)
 have kinds: "native_kinds es=native_kinds fs"
  using mapped by (simp only: transport_kinds_recovered[OF t1] transport_kinds_recovered[OF t2])
 have tuple: "display_tuple u (decode es)=display_tuple u (decode fs)"
  by (simp only: native_tuple len pos kinds)
 show "es=fs" by (rule inj_onD[OF native_display_injective tuple ty1 ty2])
qed

theorem source_unique_display_preimage:
 assumes p: "es\<in>source_words u v"
 shows "\<exists>!q. q\<in>source_words u v \<and> source_display u q=source_display u es"
proof (rule ex1I[where a=es])
 show "es\<in>source_words u v \<and> source_display u es=source_display u es" using p by simp
next
 fix q assume h: "q\<in>source_words u v \<and> source_display u q=source_display u es"
 show "q=es" by (rule inj_onD[OF source_display_injective h[THEN conjunct2] h[THEN conjunct1] p])
qed
theorem transport_unique_display_preimage:
 assumes p: "es\<in>transport_words u v"
 shows "\<exists>!q. q\<in>transport_words u v \<and> transport_display u q=transport_display u es"
proof (rule ex1I[where a=es])
 show "es\<in>transport_words u v \<and> transport_display u es=transport_display u es" using p by simp
next
 fix q assume h: "q\<in>transport_words u v \<and> transport_display u q=transport_display u es"
 show "q=es" by (rule inj_onD[OF transport_display_injective h[THEN conjunct2] h[THEN conjunct1] p])
qed
end
ML \<open>
val roots = @{thms native_position_length source_kind_list_constant native_comparison.source_positions_suffice
 native_comparison.source_display_injective transport_kinds_recovered direction_length
 native_comparison.transport_display_injective native_comparison.source_unique_display_preimage
 native_comparison.transport_unique_display_preimage pure_display_shapes source_direction_is_not_transport};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
