theory Core_Source_Match
  imports Main
begin

definition recovery where "recovery D f u a = inv_into (D u) (f u) a"
definition src_match where "src_match D f u v a = f v (recovery D f u a)"
definition src_graph where
  "src_graph D f u v a b = (a\<in>f u ` D u \<and> recovery D f u a\<in>D v \<and> b=src_match D f u v a)"

lemma recovery_domain:
  "a\<in>f u ` D u \<Longrightarrow> recovery D f u a\<in>D u"
  unfolding recovery_def by (rule inv_into_into)

lemma arrival_recovery:
  "a\<in>f u ` D u \<Longrightarrow> f u (recovery D f u a)=a"
  unfolding recovery_def by (rule f_inv_into_f)

lemma recover_arrival:
  "inj_on (f u) (D u) \<Longrightarrow> s\<in>D u \<Longrightarrow> recovery D f u (f u s)=s"
  unfolding recovery_def by (rule inv_into_f_f)

theorem l1_iff_injective:
  "(\<forall>a\<in>f ` D. \<exists>!s. s\<in>D \<and> f s=a) = inj_on f D"
  unfolding inj_on_def by blast

theorem src_graph_iff_same_recovery:
  assumes inj: "inj_on (f v) (D v)" and a: "a\<in>f u ` D u" and b: "b\<in>f v ` D v"
  shows "src_graph D f u v a b = (recovery D f u a = recovery D f v b)"
proof
  assume h: "src_graph D f u v a b"
  have dom: "recovery D f u a\<in>D v" using h unfolding src_graph_def by blast
  have out: "b=f v (recovery D f u a)" using h unfolding src_graph_def src_match_def by blast
  show "recovery D f u a = recovery D f v b"
    using recover_arrival[where D=D and f=f and u=v and s="recovery D f u a", OF inj dom] out by simp
next
  assume eq: "recovery D f u a = recovery D f v b"
  have dom: "recovery D f u a\<in>D v"
    using recovery_domain[where D=D and f=f and u=v and a=b, OF b] eq by simp
  have out: "b=f v (recovery D f u a)"
    using arrival_recovery[where D=D and f=f and u=v and a=b, OF b] eq by simp
  show "src_graph D f u v a b" using a dom out unfolding src_graph_def src_match_def by blast
qed

theorem same_source_native_match:
  assumes "a\<in>f u ` D u" "b\<in>f v ` D v" "recovery D f u a = recovery D f v b"
  shows "recovery D f u a\<in>D v \<and> src_match D f u v a=b"
  using recovery_domain[where D=D and f=f and u=v and a=b, OF assms(2)]
    arrival_recovery[where D=D and f=f and u=v and a=b, OF assms(2)] assms(3)
  unfolding src_match_def by auto

theorem source_match_inverse_graph:
  assumes "inj_on (f u) (D u)" "inj_on (f v) (D v)"
    "a\<in>f u ` D u" "b\<in>f v ` D v"
  shows "src_graph D f u v a b = src_graph D f v u b a"
  using src_graph_iff_same_recovery[OF assms(2,3,4)]
    src_graph_iff_same_recovery[OF assms(1,4,3)] by auto

theorem source_match_functional:
  "src_graph D f u v a b \<Longrightarrow> src_graph D f u v a c \<Longrightarrow> b=c"
  unfolding src_graph_def by blast

theorem source_match_injective:
  assumes inj: "inj_on (f v) (D v)"
    and ab: "src_graph D f u v a c" and bb: "src_graph D f u v b c"
  shows "a=b"
proof -
  have a: "a\<in>f u ` D u" and b: "b\<in>f u ` D u" and c: "c\<in>f v ` D v"
    using ab bb unfolding src_graph_def src_match_def by blast+
  have eq: "recovery D f u a = recovery D f u b"
    using src_graph_iff_same_recovery[OF inj a c] src_graph_iff_same_recovery[OF inj b c] ab bb by auto
  show "a=b" using arrival_recovery[where D=D and f=f and u=u and a=a, OF a]
    arrival_recovery[where D=D and f=f and u=u and a=b, OF b] eq by metis
qed

datatype kind = Src | TrPlus | TrMinus
fun admissible where
  "admissible adm Src u v = True" |
  "admissible adm TrPlus u v = adm u v" |
  "admissible adm TrMinus u v = adm v u"

fun atom where
  "atom D f tr Src u v a b = src_graph D f u v a b" |
  "atom D f tr TrPlus u v a b = tr u v a b" |
  "atom D f tr TrMinus u v a b = tr v u b a"

fun runs where
  "runs D f tr adm u [] a v b = (u=v \<and> a=b \<and> a\<in>f u ` D u)" |
  "runs D f tr adm u ((k,w)#rest) a v b = (admissible adm k u w \<and>
    (\<exists>mid. atom D f tr k u w a mid \<and> runs D f tr adm w rest mid v b))"

definition orbit where
  "orbit D f tr adm p q = (\<exists>word. runs D f tr adm (fst p) word (snd p) (fst q) (snd q))"

theorem source_word_action:
  "runs D f tr adm u [(Src,v)] a v b = src_graph D f u v a b"
  by (auto simp: src_graph_def src_match_def)

theorem equal_recovery_orbit:
  assumes a: "a\<in>f u ` D u" and b: "b\<in>f v ` D v"
    and eq: "recovery D f u a = recovery D f v b"
  shows "orbit D f tr adm (u,a) (v,b)"
proof -
  have src: "src_graph D f u v a b"
    using a same_source_native_match[OF a b eq] unfolding src_graph_def by blast
  have run: "runs D f tr adm u [(Src,v)] a v b"
    using source_word_action[where D=D and f=f and tr=tr and adm=adm and u=u and v=v and a=a and b=b] src by blast
  show ?thesis unfolding orbit_def
    by (rule exI[where x="[(Src,v)]"]) (use run in \<open>simp only: fst_conv snd_conv\<close>)
qed

theorem mutual_arrival_order_separation:
  assumes a: "a\<in>f u ` D u" and b: "b\<in>f v ` D v"
    and anti: "\<And>s t. r s t \<Longrightarrow> r t s \<Longrightarrow> s=t"
    and ab: "r (recovery D f u a) (recovery D f v b)"
    and ba: "r (recovery D f v b) (recovery D f u a)"
  shows "orbit D f tr adm (u,a) (v,b)"
  by (rule equal_recovery_orbit[OF a b anti[OF ab ba]])

theorem equal_display_not_source_match:
  "\<not>src_graph (\<lambda>u::bool. {u}) (\<lambda>_ _. ()) False True () ()"
proof -
  have mem: "inv_into {False} (\<lambda>_::bool. ()) () \<in> {False}"
    by (rule inv_into_into) auto
  have rec: "recovery (\<lambda>u::bool. {u}) (\<lambda>_ _. ()) False () = False"
    using mem unfolding recovery_def by simp
  show ?thesis using rec unfolding src_graph_def by simp
qed

ML \<open>
val roots = @{thms l1_iff_injective recovery_domain arrival_recovery recover_arrival
  src_graph_iff_same_recovery same_source_native_match source_match_inverse_graph
  source_match_functional source_match_injective source_word_action equal_recovery_orbit
  mutual_arrival_order_separation equal_display_not_source_match};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
