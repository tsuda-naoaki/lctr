theory Presentation_Quotient_Universe
 imports LCTR_Heterogeneous_Canonical_Refinement.Heterogeneous_Canonical_Refinement
begin

type_synonym ('c,'b) presentation_normal_form =
 "('c\<Rightarrow>'c set) \<times> ('b\<Rightarrow>'b set) \<times>
  ('c set\<Rightarrow>'c set\<Rightarrow>bool) \<times> ('c set\<times>'b set) set"

definition nf_qc :: "('c,'b) presentation_normal_form \<Rightarrow> 'c\<Rightarrow>'c set"
 where "nf_qc P=fst P"
definition nf_qb :: "('c,'b) presentation_normal_form \<Rightarrow> 'b\<Rightarrow>'b set"
 where "nf_qb P=fst(snd P)"
definition nf_le :: "('c,'b) presentation_normal_form \<Rightarrow> 'c set\<Rightarrow>'c set\<Rightarrow>bool"
 where "nf_le P=fst(snd(snd P))"
definition nf_raw :: "('c,'b) presentation_normal_form \<Rightarrow> ('c set\<times>'b set) set"
 where "nf_raw P=snd(snd(snd P))"

locale presentation_universe =
 fixes C :: "'c set" and B :: "'b set"
begin
definition times where "times P=nf_qc P`C"
definition states where "states P=nf_qb P`B"
definition trajectory where "trajectory P=nf_raw P \<inter> (times P\<times>states P)"
definition encode where
 "encode q p L R=(fiber_encode C q\<circ>q, fiber_encode B p\<circ>p,
                  fiber_order C q L, fiber_relation C q B p R)"

sublocale U: presentations C B times states nf_qc nf_qb nf_le trajectory
 by unfold_locales (simp_all add: times_def states_def trajectory_def)

lemma encode_projections:
 "nf_qc (encode q p L R)=fiber_encode C q\<circ>q"
 "nf_qb (encode q p L R)=fiber_encode B p\<circ>p"
 "nf_le (encode q p L R)=fiber_order C q L"
 unfolding encode_def nf_qc_def nf_qb_def nf_le_def by simp_all

lemma encode_trajectory:
 assumes t: "R\<subseteq>(q`C)\<times>(p`B)"
 shows "trajectory (encode q p L R)=fiber_relation C q B p R"
 using fiber_relation_typed[OF t]
 by (auto simp: trajectory_def times_def states_def encode_projections
   encode_def nf_raw_def nf_qc_def nf_qb_def fiber_carrier_def image_image Int_absorb1)

lemma universe_refinement_iff:
 assumes rt: "R\<subseteq>(q`C)\<times>(p`B)" and ut: "U\<subseteq>(r`C)\<times>(s`B)"
 shows "U.refines (encode q p L R) (encode r s M U) \<longleftrightarrow>
   (\<exists>f g. presentation_arrow C B r s M U q p L R f g)"
proof -
 have e: "U.refines (encode q p L R) (encode r s M U) \<longleftrightarrow>
   (\<exists>F G. presentation_arrow C B
     (fiber_encode C r\<circ>r) (fiber_encode B s\<circ>s)
     (fiber_order C r M) (fiber_relation C r B s U)
     (fiber_encode C q\<circ>q) (fiber_encode B p\<circ>p)
     (fiber_order C q L) (fiber_relation C q B p R) F G)"
   unfolding U.refines_def U.family_arrow_is_heterogeneous
   by (simp only: encode_projections encode_trajectory[OF rt] encode_trajectory[OF ut])
 show ?thesis using e heterogeneous_arrow_encoding_iff[OF ut rt, where L=M and M=L] by blast
qed

lemma universe_class_refinement_iff:
 assumes rt: "R\<subseteq>(q`C)\<times>(p`B)" and ut: "U\<subseteq>(r`C)\<times>(s`B)"
 shows "qrel UNIV U.E U.refines
   (U.E``{encode q p L R}) (U.E``{encode r s M U}) \<longleftrightarrow>
   (\<exists>f g. presentation_arrow C B r s M U q p L R f g)"
 using U.class_refinement_relation universe_refinement_iff[OF rt ut] by blast

lemmas universe_class_partial_order = U.isomorphism_class_partial_order

lemma universe_encoded_partial_order:
 assumes po: "part_on (q`C) L"
 shows "part_on (times (encode q p L R)) (nf_le (encode q p L R))"
 unfolding times_def encode_projections
 by (simp only: encoded_projection_image) (rule fiber_partial_order[OF po])

lemma universe_native_canonical_greatest:
 assumes ec: "equiv C EC" and eb: "equiv B EB" and typed: "R\<subseteq>C\<times>B"
   and po: "part_on (q`C) L"
   and adm: "native_admissible C B EC EB ord R q p
     {(x,y). x\<in>q`C \<and> y\<in>q`C \<and> L x y} trj"
 shows "U.refines (encode q p L trj)
   (encode (\<lambda>c. EC``{c}) (\<lambda>b. EB``{b})
    (\<lambda>x y. (x,y)\<in>reach_on (C//EC) (source_quotient_edges C EC ord))
    (image_rel EC EB R))"
proof -
 have t: "trj\<subseteq>(q`C)\<times>(p`B)"
   using adm typed unfolding native_admissible_def by auto
 have tc: "image_rel EC EB R \<subseteq>
     ((\<lambda>c. EC``{c})`C)\<times>((\<lambda>b. EB``{b})`B)"
   using typed unfolding image_rel_def by auto
 have a: "\<exists>f g. presentation_arrow C B (\<lambda>c. EC``{c}) (\<lambda>b. EB``{b})
    (\<lambda>x y. (x,y)\<in>reach_on (C//EC) (source_quotient_edges C EC ord))
    (image_rel EC EB R) q p L trj f g"
   using heterogeneous_native_canonical_arrow[OF ec eb typed po adm] by blast
 show ?thesis by (rule universe_refinement_iff[OF t tc, THEN iffD2, OF a])
qed

lemma universe_native_canonical_class_greatest:
 assumes ec: "equiv C EC" and eb: "equiv B EB" and typed: "R\<subseteq>C\<times>B"
   and po: "part_on (q`C) L"
   and adm: "native_admissible C B EC EB ord R q p
     {(x,y). x\<in>q`C \<and> y\<in>q`C \<and> L x y} trj"
 shows "qrel UNIV U.E U.refines (U.E``{encode q p L trj})
   (U.E``{encode (\<lambda>c. EC``{c}) (\<lambda>b. EB``{b})
    (\<lambda>x y. (x,y)\<in>reach_on (C//EC) (source_quotient_edges C EC ord))
    (image_rel EC EB R)})"
 using universe_native_canonical_greatest[OF ec eb typed po adm] U.class_refinement_relation by blast

lemma universe_source_native_canonical_class_greatest:
 assumes po: "part_on (q`C) L"
   and adm: "native_admissible C B
     (least_equiv C (generator_c C D B Rel Bind))
     (least_equiv B (generator_b C D B Rel Bind))
     ord (source_rel C D B Rel) q p
     {(x,y). x\<in>q`C \<and> y\<in>q`C \<and> L x y} trj"
 shows "qrel UNIV U.E U.refines (U.E``{encode q p L trj})
   (U.E``{encode
     (\<lambda>c. least_equiv C (generator_c C D B Rel Bind)``{c})
     (\<lambda>b. least_equiv B (generator_b C D B Rel Bind)``{b})
     (\<lambda>x y. (x,y)\<in>reach_on (C//least_equiv C (generator_c C D B Rel Bind))
       (source_quotient_edges C (least_equiv C (generator_c C D B Rel Bind)) ord))
     (image_rel (least_equiv C (generator_c C D B Rel Bind))
       (least_equiv B (generator_b C D B Rel Bind)) (source_rel C D B Rel))})"
 by (rule universe_native_canonical_class_greatest[
     OF least_equiv_equivalence[OF source_generator_carriers(2)]
        least_equiv_equivalence[OF source_generator_carriers(3)]
        source_generator_carriers(1) po adm])
end

ML \<open>
val roots = @{thms presentation_universe.encode_projections
 presentation_universe.encode_trajectory presentation_universe.universe_refinement_iff
 presentation_universe.universe_class_refinement_iff
 presentation_universe.universe_class_partial_order
 presentation_universe.universe_encoded_partial_order
 presentation_universe.universe_native_canonical_greatest
 presentation_universe.universe_native_canonical_class_greatest
 presentation_universe.universe_source_native_canonical_class_greatest};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
