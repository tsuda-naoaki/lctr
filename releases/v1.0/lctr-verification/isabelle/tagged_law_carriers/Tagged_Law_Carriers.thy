theory Tagged_Law_Carriers
  imports "LCTR_Law_Index_Encoding.Law_Index_Encoding"
begin

definition tag_encode where
  "tag_encode b x=map_option (\<lambda>v. (b,v)) x"
definition tag_decode where
  "tag_decode b z=(case z of None\<Rightarrow>None | Some(a,x)\<Rightarrow>if a=b then Some x else None)"
definition source_carrier where
  "source_carrier X b=Some ` X b"
definition target_carrier where
  "target_carrier X b=(\<lambda>x. Some(b,x)) ` X b"

lemma decode_encode: "tag_decode b (tag_encode b x)=x"
  by (cases x) (simp_all add: tag_decode_def tag_encode_def)
lemma encode_injective: "inj(tag_encode b)"
  by (rule injI) (metis decode_encode)
lemma encode_typed:
  "tag_encode b ` source_carrier X b\<subseteq>target_carrier X b"
  by (auto simp: tag_encode_def source_carrier_def target_carrier_def)
lemma decode_typed:
  "tag_decode b ` target_carrier X b\<subseteq>source_carrier X b"
  by (auto simp: tag_decode_def source_carrier_def target_carrier_def)
lemma encode_decode:
  "z\<in>target_carrier X b \<Longrightarrow> tag_encode b(tag_decode b z)=z"
  by (auto simp: target_carrier_def tag_encode_def tag_decode_def)
lemma tagged_carrier_bijection:
  "carrier_bijection (source_carrier X b) (target_carrier X b) (tag_encode b) (tag_decode b)"
proof (unfold_locales)
  show "tag_encode b ` source_carrier X b\<subseteq>target_carrier X b" by (rule encode_typed)
  show "tag_decode b ` target_carrier X b\<subseteq>source_carrier X b" by (rule decode_typed)
  show "\<And>t. t\<in>source_carrier X b \<Longrightarrow> tag_decode b(tag_encode b t)=t" by (rule decode_encode)
  show "\<And>z. z\<in>target_carrier X b \<Longrightarrow> tag_encode b(tag_decode b z)=z" by (rule encode_decode)
qed
lemma tagged_bij_betw:
  "bij_betw(tag_encode b)(source_carrier X b)(target_carrier X b)"
  by (auto simp: bij_betw_def inj_on_def source_carrier_def target_carrier_def tag_encode_def image_image)
lemma padding_not_in_carrier: "None\<notin>target_carrier X b"
  by (auto simp: target_carrier_def)
lemma carrier_tag_unique:
  "z\<in>target_carrier X a \<Longrightarrow> z\<in>target_carrier X b \<Longrightarrow> a=b"
  by (auto simp: target_carrier_def)
lemma empty_carrier_supported:
  "X b={} \<Longrightarrow> source_carrier X b={} \<and> target_carrier X b={} \<and>
    bij_betw(tag_encode b)(source_carrier X b)(target_carrier X b)"
  by (simp add: source_carrier_def target_carrier_def bij_betw_def)
lemma selected_carrier_embedding:
  "bij_betw(tag_encode b)(source_carrier X b)(target_carrier X b) \<and>
    (\<forall>v. tag_decode b(tag_encode b v)=v) \<and>
    (\<forall>v\<in>target_carrier X b. tag_encode b(tag_decode b v)=v)"
  by (intro conjI allI ballI; (rule tagged_bij_betw | rule decode_encode | rule encode_decode); assumption?)

ML \<open>
val roots = @{thms decode_encode encode_injective encode_typed decode_typed encode_decode
 tagged_carrier_bijection tagged_bij_betw padding_not_in_carrier carrier_tag_unique
 empty_carrier_supported selected_carrier_embedding};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
