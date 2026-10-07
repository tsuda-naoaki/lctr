theory Core_Local_Loop_Bridge
 imports "LCTR_Core_Local_Loop_Realization.Core_Local_Loop_Realization"
  "LCTR_Core_Local_Loop_Specification.Core_Local_Loop_Specification"
begin

fun lift where
 "lift u []=[]" |
 "lift u ((v,s)#es)=(if s then Forward u v else Backward u v)#lift v es"
fun project_atom where
 "project_atom (Source u v)=(v,False)" |
 "project_atom (Forward u v)=(v,True)" |
 "project_atom (Backward u v)=(v,False)"
definition project where "project es=map project_atom es"

lemma encoded_pure: "transport_only (lift u es)"
 by (induction es arbitrary: u) (auto simp: transport_only_def split: prod.splits if_splits)
lemma length_preserved: "length (lift u es)=length es"
 by (induction es arbitrary: u) (auto split: prod.splits)
lemma decode_encode: "project (lift u es)=es"
 by (induction es arbitrary: u) (auto simp: project_def split: prod.splits)
lemma encoding_injective: "lift u es=lift u fs \<Longrightarrow> es=fs"
 using decode_encode by metis

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

lemma lift_typed:
 "Core_Local_Loop_Specification.path adm u es v = W.typed u (lift u es) v"
 by (induction es arbitrary: u) (auto simp: step_def split: prod.splits)

lemma encode_decode:
 "W.typed u es v \<Longrightarrow> transport_only es \<Longrightarrow> lift u (project es)=es"
proof (induction es arbitrary: u)
 case Nil
 then show ?case by (simp add: project_def)
next
 case (Cons a es)
 then show ?case by (cases a) (auto simp: project_def transport_only_def)
qed

definition native_spec where
 "native_spec b s=\<lparr>base=b,word=lift b (fst s),specified={b}\<times>snd s\<rparr>"

lemma native_spec_fields:
 assumes raw: "Core_Local_Loop_Specification.valid_spec adm (\<lambda>u. f u ` D u) b s"
 shows "valid_spec(native_spec b s) \<and> base(native_spec b s)=b \<and>
  word(native_spec b s)=lift b (fst s) \<and> specified(native_spec b s)={b}\<times>snd s"
 using raw encoded_pure[of b "fst s"]
 by (auto simp: native_spec_def valid_spec_def Core_Local_Loop_Specification.valid_spec_def
  regions_def lift_typed)

lemma native_spec_positive:
 "Core_Local_Loop_Specification.valid_spec adm (\<lambda>u. f u ` D u) b s \<Longrightarrow>
  0<length(word(native_spec b s))"
 by (simp add: native_spec_def length_preserved Core_Local_Loop_Specification.valid_spec_def)

lemma candidate_partial_injection:
 "Core_Local_Loop_Specification.path adm u es v \<Longrightarrow>
  (\<forall>a b c. W.action u (lift u es) v a b \<longrightarrow> W.action u (lift u es) v a c \<longrightarrow> b=c) \<and>
  (\<forall>a b c. W.action u (lift u es) v a c \<longrightarrow> W.action u (lift u es) v b c \<longrightarrow> a=b)"
 using W.action_functional W.action_injective by blast

end
ML \<open>
val roots = @{thms encoded_pure length_preserved decode_encode native_comparison.encode_decode
 encoding_injective native_comparison.native_spec_fields native_comparison.native_spec_positive
 native_comparison.candidate_partial_injection};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
