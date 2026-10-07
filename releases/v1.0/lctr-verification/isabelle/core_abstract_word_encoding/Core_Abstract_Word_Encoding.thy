theory Core_Abstract_Word_Encoding
  imports "../core_typed_words/Core_Typed_Words"
begin

fun atoms where
  "atoms u [] = []" |
  "atoms u ((v,k)#es) = (k,u,v)#atoms v es"

definition edges where
  "edges es = map (\<lambda>(k,u,v). (v,k)) es"

definition display where
  "display u es = (length es, u#map fst es, map snd es)"

lemma decode_encode: "edges (atoms u es) = es"
  by (induction es arbitrary: u) (auto simp: edges_def split: prod.splits)

lemma tuple_lengths:
  "length (u#map fst es) = length es + 1 \<and> length (map snd es) = length es"
  by simp

lemma zip_projections: "zip (map fst es) (map snd es) = es"
  by (induction es) (auto split: prod.splits)

lemma display_edges_injective: "display u es = display u fs \<Longrightarrow> es=fs"
proof -
  assume h: "display u es = display u fs"
  have a: "map fst es = map fst fs" and b: "map snd es = map snd fs"
    using h unfolding display_def by auto
  have "zip (map fst es) (map snd es) = zip (map fst fs) (map snd fs)"
    by (simp only: a b)
  then show "es=fs" by (simp only: zip_projections)
qed

locale typed_kind_actions =
  typed_actions Y Adm "\<lambda>(k,u,v). u" "\<lambda>(k,u,v). v" dagger act
  for Y :: "'u\<Rightarrow>'x set" and Adm :: "('k\<times>'u\<times>'u) set"
    and dagger :: "('k\<times>'u\<times>'u)\<Rightarrow>('k\<times>'u\<times>'u)"
    and act :: "('k\<times>'u\<times>'u)\<Rightarrow>'x\<Rightarrow>'x\<Rightarrow>bool"
begin

fun valid_edges where
  "valid_edges u [] v = (u=v)" |
  "valid_edges u ((v,k)#es) z = ((k,u,v)\<in>Adm \<and> valid_edges v es z)"

lemma encode_decode: "typed u es v \<Longrightarrow> atoms u (edges es) = es"
  by (induction es arbitrary: u) (auto simp: edges_def split: prod.splits)

lemma valid_typed: "valid_edges u es v = typed u (atoms u es) v"
  by (induction es arbitrary: u) (auto split: prod.splits)

lemma typed_valid: "typed u es v \<Longrightarrow> valid_edges u (edges es) v"
  using valid_typed encode_decode by metis

lemma encoding_bijective:
  "bij_betw (atoms u) {es. valid_edges u es v} {es. typed u es v}"
proof -
  have inj: "inj_on (atoms u) {es. valid_edges u es v}"
    unfolding inj_on_def using decode_encode by metis
  have im: "atoms u ` {es. valid_edges u es v} = {es. typed u es v}"
  proof
    show "atoms u ` {es. valid_edges u es v} \<subseteq> {es. typed u es v}"
      using valid_typed by blast
    show "{es. typed u es v} \<subseteq> atoms u ` {es. valid_edges u es v}"
      using typed_valid encode_decode by force
  qed
  show ?thesis using inj im unfolding bij_betw_def by blast
qed

lemma displayed_tuple_injective:
  assumes "typed u es v" "typed u fs v" "display u (edges es) = display u (edges fs)"
  shows "es=fs"
proof -
  have e: "edges es = edges fs" by (rule display_edges_injective[OF assms(3)])
  have "es = atoms u (edges es)" by (rule sym[OF encode_decode[OF assms(1)]])
  also have "... = atoms u (edges fs)" by (rule arg_cong[OF e])
  also have "... = fs" by (rule encode_decode[OF assms(2)])
  finally show ?thesis .
qed

lemma tuple_reconstruction:
  "valid_edges u es v = (\<exists>fs. typed u fs v \<and> edges fs=es)"
proof
  assume h: "valid_edges u es v"
  have t: "typed u (atoms u es) v" using h by (simp only: valid_typed)
  show "\<exists>fs. typed u fs v \<and> edges fs=es"
    by (rule exI[of _ "atoms u es"], rule conjI, rule t, rule decode_encode)
next
  assume h: "\<exists>fs. typed u fs v \<and> edges fs=es"
  then obtain fs where t: "typed u fs v" and e: "edges fs=es" by blast
  have "valid_edges u (edges fs) v" by (rule typed_valid[OF t])
  then show "valid_edges u es v" by (simp only: e)
qed

definition raw_action where
  "raw_action u es v a b = (valid_edges u es v \<and> a\<in>Y u \<and> sequence act (atoms u es) a b)"

lemma action_preservation:
  "action u (atoms u es) v a b = raw_action u es v a b"
  unfolding action_def raw_action_def using valid_typed by simp

lemma append_display: "edges (es@fs) = edges es @ edges fs"
  by (simp add: edges_def)

lemma append_encoding:
  "valid_edges u es v \<Longrightarrow> atoms u (es@fs) = atoms u es @ atoms v fs"
  by (induction es arbitrary: u) (auto split: prod.splits)

lemma reverse_encoding:
  "typed u es v \<Longrightarrow> atoms v (edges (map dagger (rev es))) = map dagger (rev es)"
  using typed_reverse encode_decode by blast

end

ML \<open>
val roots = @{thms decode_encode typed_kind_actions.encode_decode
  typed_kind_actions.encoding_bijective typed_kind_actions.displayed_tuple_injective
  tuple_lengths typed_kind_actions.tuple_reconstruction typed_kind_actions.action_preservation
  typed_kind_actions.append_display typed_kind_actions.append_encoding typed_kind_actions.reverse_encoding};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
