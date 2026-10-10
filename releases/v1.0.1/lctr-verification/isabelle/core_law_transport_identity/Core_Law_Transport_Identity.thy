theory Core_Law_Transport_Identity
 imports "LCTR_Core_Law_Transport.Core_Law_Family_Transport"
begin

definition same_component_content where
 "same_component_content c e \<longleftrightarrow>
 eval_times c=eval_times e \<and> eval_domain c=eval_domain e \<and>
 law_relation c=law_relation e \<and>
 (\<forall>t\<in>eval_times c. input_value c t=input_value e t \<and> output_value c t=output_value e t)"

definition same_family_content where
 "same_family_content d e \<longleftrightarrow>
 time_carrier d=time_carrier e \<and> law_indices d=law_indices e \<and>
 (\<forall>a\<in>law_indices d. input_carrier d a=input_carrier e a \<and>
 output_carrier d a=output_carrier e a \<and> same_component_content (components d a) (components e a)) \<and>
 (\<forall>P\<subseteq>time_carrier d. admissible_common d P \<longleftrightarrow> admissible_common e P) \<and>
 (\<forall>psi. typed_reindex_family d psi \<longrightarrow> (faithful_family d psi \<longleftrightarrow> faithful_family e psi))"

lemma identity_reindex_unique:
 assumes r: "reindex_on Z e" and s: "\<forall>z\<in>Z. forward_map e z=z"
 shows "\<forall>z\<in>Z. forward_map e z=z \<and> inverse_map e z=z"
 using r s unfolding reindex_on_def by metis

lemma component_identity_transport:
 "component_transport id id (c::('t,'x,'y) law_component)=c"
 by (cases c) (simp add: component_transport_def pair_change_def tuple_change_def)

lemma tuple_identity_reindex: "tuple_change id=id"
 by (rule ext) (simp add: tuple_change_def)

lemma conjugate_identity_transport:
 "conjugate_reindex id id (phi::'t carrier_reindex)=phi"
 by (cases phi) (simp add: conjugate_reindex_def)

locale identity_law_transport = law_transport T T f g d
 for T::"'t set" and f::"'t\<Rightarrow>'t" and g::"'t\<Rightarrow>'t"
 and d::"('t,'a,'x,'y) law_family" +
 assumes same: "\<And>t. t\<in>T \<Longrightarrow> f t=t"
begin
lemma inverse_same: "t\<in>T \<Longrightarrow> g t=t"
 using left_inverse same by metis

lemma image_same: "S\<subseteq>T \<Longrightarrow> f ` S=S"
proof -
 assume s: "S\<subseteq>T"
 have "f ` S=id ` S" by (rule image_cong[OF refl]) (use s same in auto)
 then show ?thesis by simp
qed

lemma tuple_same:
 "z\<in>tuple_carrier d a \<Longrightarrow> tuple_change f z=z \<and> tuple_change g z=z"
 unfolding tuple_carrier_def source_time tuple_change_def
 using same inverse_same by auto

lemma component_same:
 assumes a: "a\<in>law_indices d"
 shows "same_component_content (components target a) (old a)"
proof -
 have times: "f ` eval_times(old a)=eval_times(old a)"
  by (rule image_same[OF component_bounds(1)[OF a]])
 have ep: "pair_change f z=z" if "z\<in>eval_domain(old a)" for z
  using component_bounds(2)[OF a] that same unfolding pair_change_def by auto
 have rp: "tuple_change f z=z" if "z\<in>law_relation(old a)" for z
  using component_bounds(3)[OF a] that same unfolding tuple_change_def by auto
 have ed: "pair_change f ` eval_domain(old a)=eval_domain(old a)"
  using ep by (metis image_cong id_apply image_ident)
 have rd: "tuple_change f ` law_relation(old a)=law_relation(old a)"
  using rp by (metis image_cong id_apply image_ident)
 have vals: "\<forall>t\<in>eval_times(old a). g t=t"
  using component_bounds(1)[OF a] inverse_same by blast
 show ?thesis using times ed rd vals
  by (simp add: same_component_content_def component_transport_def)
qed

lemma conjugated_same:
 assumes p: "typed_reindex_family d phi" and a: "a\<in>law_indices d"
 and z: "z\<in>tuple_carrier d a"
 shows "forward_map(conjugated phi a)z=forward_map(phi a)z \<and>
 inverse_map(conjugated phi a)z=inverse_map(phi a)z"
proof -
 have typed: "reindex_on (tuple_carrier d a) (phi a)"
  using p a unfolding typed_reindex_family_def by blast
 have fw: "forward_map(phi a)z\<in>tuple_carrier d a"
  and iv: "inverse_map(phi a)z\<in>tuple_carrier d a"
  using typed z unfolding reindex_on_def by blast+
 show ?thesis
  using tuple_same[OF z] tuple_same[OF fw] tuple_same[OF iv]
  by (simp add: conjugated_def conjugate_reindex_def)
qed

lemma conjugates_same:
 assumes p: "typed_reindex_family d phi"
 shows "conjugates phi psi \<longleftrightarrow> same_reindex_family d psi phi"
 using conjugated_same[OF p]
 unfolding conjugates_def same_reindex_family_def tuple_carrier_def source_time by simp

lemma faithful_identity_transport:
 assumes ps: "typed_reindex_family d psi"
 shows "faithful_family target psi \<longleftrightarrow> faithful_family d psi"
proof
 assume h: "faithful_family target psi"
 obtain phi where pt: "typed_reindex_family d phi" and hp: "faithful_family d phi"
 and eq: "conjugates phi psi" using h unfolding target_def by auto
 have samephi: "same_reindex_family d psi phi"
  by (rule iffD1[OF conjugates_same[OF pt] eq])
 have iff: "faithful_family d psi \<longleftrightarrow> faithful_family d phi"
  using wf ps pt samephi unfolding well_typed_family_def by blast
 show "faithful_family d psi" using iff hp by blast
next
 assume h: "faithful_family d psi"
 have eq: "conjugates psi psi"
  using conjugates_same[OF ps, of psi] by (simp add: same_reindex_family_def)
 show "faithful_family target psi" using ps h eq unfolding target_def by auto
qed

lemma admissible_identity_transport:
 assumes p: "P\<subseteq>T"
 shows "admissible_common target P \<longleftrightarrow> admissible_common d P"
 using image_same p by (auto simp: admissible_family_image)

lemma family_identity_from_values: "same_family_content d target"
proof -
 have cs: "\<forall>a\<in>law_indices d. same_component_content (old a) (components target a)"
  using component_same by (auto simp: same_component_content_def)
 show ?thesis using cs faithful_identity_transport admissible_identity_transport
  by (simp add: same_family_content_def source_time)
qed
end

lemma family_identity_transport:
 assumes wf: "well_typed_family d"
 shows "same_family_content d (law_transport.target (time_carrier d) (time_carrier d) id id d)"
proof -
 interpret ident: identity_law_transport "time_carrier d" id id d
  by unfold_locales (simp_all add: wf)
 show ?thesis by (rule ident.family_identity_from_values)
qed

ML \<open>
val roots = @{thms identity_reindex_unique component_identity_transport tuple_identity_reindex
 conjugate_identity_transport identity_law_transport.faithful_identity_transport
 family_identity_transport identity_law_transport.family_identity_from_values};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
