theory Tagged_Native_Law_Family
  imports "LCTR_Tagged_Law_Carriers.Tagged_Law_Carriers"
begin

definition field_embed where "field_embed b x=Some(b,x)"
definition field_project where "field_project b z=the(tag_decode b z)"

lemma field_bijection:
  "carrier_bijection X (field_embed b ` X) (field_embed b) (field_project b)"
  unfolding carrier_bijection_def field_embed_def field_project_def tag_decode_def
  by auto
lemma field_padding_excluded: "None\<notin>field_embed b ` X"
  by (auto simp: field_embed_def)

locale tagged_native_family =
  fixes d :: "('t,'a,'x,'y) law_family" and b :: "'s"
  assumes wf: "well_typed_family d"
begin

sublocale fields: full_family_encoding "time_carrier d"
  "field_embed b ` time_carrier d" "field_embed b" "field_project b" d
  "\<lambda>a. field_embed (b,a) ` input_carrier d a"
  "\<lambda>a. field_embed (b,a) ` output_carrier d a"
  "\<lambda>a. field_embed (b,a)" "\<lambda>a. field_project (b,a)"
  "\<lambda>a. field_embed (b,a)" "\<lambda>a. field_project (b,a)"
  unfolding full_family_encoding_def full_family_encoding_axioms_def
  using wf by (auto intro: field_bijection)

sublocale indices: law_index_encoding "law_indices d"
  "field_embed b ` law_indices d" "field_embed b" "field_project b" fields.encoded
  unfolding law_index_encoding_def law_index_encoding_axioms_def
  using fields.encoded_well_typed by (auto intro: field_bijection)

abbreviation encoded_family where "encoded_family \<equiv> indices.encoded"

lemma encoded_carriers:
  "time_carrier encoded_family=field_embed b ` time_carrier d"
  "law_indices encoded_family=field_embed b ` law_indices d"
  "input_carrier encoded_family (field_embed b a)=field_embed(b,a) ` input_carrier d a"
  "output_carrier encoded_family (field_embed b a)=field_embed(b,a) ` output_carrier d a"
  by (simp only: indices.selectors fields.selectors;
    simp add: field_project_def field_embed_def tag_decode_def)+

lemma encoded_component:
  "components encoded_family (field_embed b a)=
    full_component_transport (field_embed b) (field_project b)
      (field_embed(b,a)) (field_embed(b,a)) (components d a)"
  by (simp only: indices.selectors fields.selectors;
    simp add: field_project_def field_embed_def tag_decode_def)

lemma encoded_evaluation_values:
  "input_value(components encoded_family (field_embed b a))(field_embed b t)=
    field_embed(b,a)(input_value(components d a)t)"
  "output_value(components encoded_family (field_embed b a))(field_embed b t)=
    field_embed(b,a)(output_value(components d a)t)"
  by (simp only: encoded_component;
    simp add: full_component_transport_def field_project_def field_embed_def tag_decode_def)+

lemma encoded_evaluation_domain:
  "eval_domain(components encoded_family (field_embed b a))=
    map_prod (field_embed b) (field_embed(b,a)) ` eval_domain(components d a)"
  by (simp only: encoded_component full_component_transport_def law_component.select_convs)

lemma encoded_relation:
  "law_relation(components encoded_family (field_embed b a))=
    map_prod (map_prod (field_embed b) (field_embed(b,a))) (field_embed(b,a)) `
      law_relation(components d a)"
  by (simp only: encoded_component full_component_transport_def law_component.select_convs)

lemma condition1: "K1 encoded_family\<longleftrightarrow>K1 d"
  by (simp only: indices.condition1 fields.condition1)
lemma condition2: "K2 encoded_family\<longleftrightarrow>K2 d"
  by (simp only: indices.condition2 fields.condition2)
lemma condition3: "K3 encoded_family\<longleftrightarrow>K3 d"
  by (simp only: indices.condition3 fields.condition3)
lemma condition4: "K4 encoded_family\<longleftrightarrow>K4 d"
  by (simp only: indices.condition4 fields.condition4)
lemma condition5: "K5 encoded_family\<longleftrightarrow>K5 d"
  by (simp only: indices.condition5 fields.condition5)
lemma all_conditions_preserved:
  "all_conditions encoded_family\<longleftrightarrow>all_conditions d"
  by (simp only: indices.all_conditions_preserved fields.all_conditions_preserved)
lemma common_times_image:
  "common_times encoded_family=field_embed b ` common_times d"
  by (simp only: indices.common_times_preserved fields.common_times_image)
lemma encoded_well_typed: "well_typed_family encoded_family"
  by (rule indices.encoded_well_typed)
lemma encoded_padding_excluded:
  "None\<notin>time_carrier encoded_family \<and> None\<notin>law_indices encoded_family"
  by (simp only: encoded_carriers field_padding_excluded; simp)

end

ML \<open>
val roots = @{thms field_bijection field_padding_excluded tagged_native_family.encoded_carriers
 tagged_native_family.encoded_component tagged_native_family.encoded_evaluation_values
 tagged_native_family.encoded_evaluation_domain tagged_native_family.encoded_relation
 tagged_native_family.condition1 tagged_native_family.condition2 tagged_native_family.condition3
 tagged_native_family.condition4 tagged_native_family.condition5 tagged_native_family.all_conditions_preserved
 tagged_native_family.common_times_image tagged_native_family.encoded_well_typed
 tagged_native_family.encoded_padding_excluded};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
