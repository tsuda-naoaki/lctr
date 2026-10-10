theory Dynamics_Refinement_Complete_Alignment
 imports LCTR_Heterogeneous_Presentation_Isomorphisms.Heterogeneous_Presentation_Isomorphisms
begin

lemma part_on_subset:
 assumes "part_on A L" "S\<subseteq>A"
 shows "part_on S L"
 using assms unfolding part_on_def pre_on_def by blast

lemma generated_canonical_partial_order:
 assumes a: "antisym (reach_on (C//EC) (source_quotient_edges C EC ord))"
 shows "part_on (C//EC)
   (\<lambda>x y. (x,y)\<in>reach_on (C//EC) (source_quotient_edges C EC ord))"
 using reach_refl[where Q="C//EC" and E="source_quotient_edges C EC ord"]
   reach_trans[where Q="C//EC" and E="source_quotient_edges C EC ord"] a
 unfolding part_on_def pre_on_def refl_on_def trans_def antisym_def by blast

lemma complete_canonical_admissible:
 assumes ec: "equiv C EC" and eb: "equiv B EB"
   and a: "antisym (reach_on (C//EC) (source_quotient_edges C EC ord))"
 shows "native_admissible C B EC EB ord R (\<lambda>c. EC``{c}) (\<lambda>b. EB``{b})
    (reach_on (C//EC) (source_quotient_edges C EC ord)) (image_rel EC EB R) \<and>
   part_on (C//EC) (\<lambda>x y. (x,y)\<in>reach_on (C//EC) (source_quotient_edges C EC ord))"
 using alignment_canonical_admissible[OF ec eb] generated_canonical_partial_order[OF a] by iprover

lemmas complete_mutual_factor_inverse = heterogeneous_mutual_inverse
lemmas complete_mutual_iff_iso = heterogeneous_mutual_iff_iso
lemmas complete_missing_projection_surjectivity_control = alignment_missing_projection_surjectivity_control

context presentation_universe
begin
definition valid_classes where
 "valid_classes={X\<in>UNIV//U.E. \<exists>P. part_on (times P) (nf_le P) \<and> X=U.E``{P}}"
definition canonical_form where
 "canonical_form EC EB ord R =
   encode (\<lambda>c. EC``{c}) (\<lambda>b. EB``{b})
    (\<lambda>x y. (x,y)\<in>reach_on (C//EC) (source_quotient_edges C EC ord))
    (image_rel EC EB R)"

lemma valid_class_member:
 assumes po: "part_on (times P) (nf_le P)"
 shows "U.E``{P}\<in>valid_classes"
 unfolding valid_classes_def
proof (rule CollectI, rule conjI)
 show "U.E``{P}\<in>UNIV//U.E" by (rule quotientI) simp
 show "\<exists>Q. part_on (times Q) (nf_le Q) \<and> U.E``{P}=U.E``{Q}"
   by (rule exI[of _ P]) (simp add: po)
qed

lemmas complete_refinement_refl = U.refinement_refl
lemmas complete_refinement_trans = U.refinement_trans
lemmas complete_refinement_descends = U.refines_desc

lemma complete_isomorphism_class_partial_order:
 "part_on valid_classes (qrel UNIV U.E U.refines)"
 by (rule part_on_subset[OF U.isomorphism_class_partial_order])
    (auto simp: valid_classes_def)

lemma complete_native_canonical_greatest:
 assumes ec: "equiv C EC" and eb: "equiv B EB" and typed: "R\<subseteq>C\<times>B"
   and a: "antisym (reach_on (C//EC) (source_quotient_edges C EC ord))"
   and po: "part_on (q`C) L"
   and adm: "native_admissible C B EC EB ord R q p
     {(x,y). x\<in>q`C \<and> y\<in>q`C \<and> L x y} trj"
 shows "part_on (times (canonical_form EC EB ord R)) (nf_le (canonical_form EC EB ord R)) \<and>
   U.refines (encode q p L trj) (canonical_form EC EB ord R)"
proof -
 have cp: "part_on ((\<lambda>c. EC``{c})`C)
   (\<lambda>x y. (x,y)\<in>reach_on (C//EC) (source_quotient_edges C EC ord))"
   by (simp only: canonical_projection_surjective) (rule generated_canonical_partial_order[OF a])
 have cp': "part_on (times (canonical_form EC EB ord R)) (nf_le (canonical_form EC EB ord R))"
   unfolding canonical_form_def by (rule universe_encoded_partial_order[OF cp])
 have rr: "U.refines (encode q p L trj) (canonical_form EC EB ord R)"
   unfolding canonical_form_def by (rule universe_native_canonical_greatest[OF ec eb typed po adm])
 show ?thesis using cp' rr by iprover
qed

lemma complete_native_canonical_class_greatest:
 assumes ec: "equiv C EC" and eb: "equiv B EB" and typed: "R\<subseteq>C\<times>B"
   and a: "antisym (reach_on (C//EC) (source_quotient_edges C EC ord))"
   and po: "part_on (q`C) L"
   and adm: "native_admissible C B EC EB ord R q p
     {(x,y). x\<in>q`C \<and> y\<in>q`C \<and> L x y} trj"
 shows "U.E``{encode q p L trj}\<in>valid_classes \<and>
   U.E``{canonical_form EC EB ord R}\<in>valid_classes \<and>
   qrel UNIV U.E U.refines
    (U.E``{encode q p L trj}) (U.E``{canonical_form EC EB ord R})"
proof -
 have cp: "part_on (times (canonical_form EC EB ord R)) (nf_le (canonical_form EC EB ord R))"
   and rr: "U.refines (encode q p L trj) (canonical_form EC EB ord R)"
   using complete_native_canonical_greatest[OF ec eb typed a po adm] by iprover+
 have pp: "part_on (times (encode q p L trj)) (nf_le (encode q p L trj))"
   by (rule universe_encoded_partial_order[OF po])
 have pc: "U.E``{encode q p L trj}\<in>valid_classes"
   by (rule valid_class_member[OF pp])
 have cc: "U.E``{canonical_form EC EB ord R}\<in>valid_classes"
   by (rule valid_class_member[OF cp])
 have qr: "qrel UNIV U.E U.refines
    (U.E``{encode q p L trj}) (U.E``{canonical_form EC EB ord R})"
   using rr U.class_refinement_relation by blast
 show ?thesis using pc cc qr by iprover
qed

lemma complete_source_native_canonical_class_greatest:
 assumes po: "part_on (q`C) L"
   and a: "antisym (reach_on (C//least_equiv C (generator_c C D B Rel Bind))
      (source_quotient_edges C (least_equiv C (generator_c C D B Rel Bind)) ord))"
   and adm: "native_admissible C B
     (least_equiv C (generator_c C D B Rel Bind))
     (least_equiv B (generator_b C D B Rel Bind))
     ord (source_rel C D B Rel) q p
     {(x,y). x\<in>q`C \<and> y\<in>q`C \<and> L x y} trj"
 shows "U.E``{encode q p L trj}\<in>valid_classes \<and>
   U.E``{canonical_form
       (least_equiv C (generator_c C D B Rel Bind))
       (least_equiv B (generator_b C D B Rel Bind)) ord (source_rel C D B Rel)}\<in>valid_classes \<and>
   qrel UNIV U.E U.refines (U.E``{encode q p L trj})
     (U.E``{canonical_form
       (least_equiv C (generator_c C D B Rel Bind))
       (least_equiv B (generator_b C D B Rel Bind)) ord (source_rel C D B Rel)})"
 by (rule complete_native_canonical_class_greatest[
     OF least_equiv_equivalence[OF source_generator_carriers(2)]
        least_equiv_equivalence[OF source_generator_carriers(3)]
        source_generator_carriers(1) a po adm])
end

ML \<open>
val roots = @{thms presentation_universe.complete_refinement_refl
 presentation_universe.complete_refinement_trans complete_mutual_factor_inverse
 complete_mutual_iff_iso presentation_universe.complete_refinement_descends
 presentation_universe.complete_isomorphism_class_partial_order complete_canonical_admissible
 presentation_universe.complete_native_canonical_greatest
 presentation_universe.complete_native_canonical_class_greatest
 presentation_universe.complete_source_native_canonical_class_greatest
 complete_missing_projection_surjectivity_control};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = if null (Thm_Deps.all_oracles @{thms part_on_subset generated_canonical_partial_order})
  then () else error "Unexpected support oracle dependency";
\<close>
end
