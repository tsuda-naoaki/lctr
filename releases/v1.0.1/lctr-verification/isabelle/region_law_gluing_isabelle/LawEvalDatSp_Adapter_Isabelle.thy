theory LawEvalDatSp_Adapter_Isabelle
imports Law_Candidate_Relation_Isabelle
begin

record ('idx, 'time, 'in, 'out) paper_law_eval_dat =
  paper_law_idx :: "'idx set"
  paper_eval_dom :: "'idx => ('time * 'in) set"
  paper_out_val_sp :: "'idx => 'out set"
  paper_cand_rel :: "'idx => (('time * 'in) * 'out) set"

definition law_eval_dat_sp_member ::
  "('idx, 'time, 'in, 'out) paper_law_eval_dat => bool" where
  "law_eval_dat_sp_member LD =
   (paper_law_idx LD \<noteq> {}
    \<and> (\<forall>a\<in>paper_law_idx LD.
      paper_cand_rel LD a
      \<subseteq> paper_eval_dom LD a \<times> paper_out_val_sp LD a))"

definition paper_k_cand_rel_right_unique ::
  "('idx, 'time, 'in, 'out) paper_law_eval_dat => bool" where
  "paper_k_cand_rel_right_unique LD =
   (\<forall>a\<in>paper_law_idx LD.
      right_unique
        (paper_eval_dom LD a)
        (paper_out_val_sp LD a)
        (paper_cand_rel LD a))"

definition to_generic_law_dat ::
  "('idx, 'time, 'in, 'out) paper_law_eval_dat
   => ('idx, 'time * 'in, 'out) law_dat" where
  "to_generic_law_dat LD =
   \<lparr> law_idx = paper_law_idx LD,
      in_val_sp = paper_eval_dom LD,
      out_val_sp = paper_out_val_sp LD,
      cand_rel = paper_cand_rel LD \<rparr>"

lemma adapter_law_idx[simp]:
  "law_idx (to_generic_law_dat LD) = paper_law_idx LD"
  unfolding to_generic_law_dat_def by simp

lemma adapter_input_carrier_is_eval_dom[simp]:
  "in_val_sp (to_generic_law_dat LD) a = paper_eval_dom LD a"
  unfolding to_generic_law_dat_def by simp

lemma adapter_output_carrier[simp]:
  "out_val_sp (to_generic_law_dat LD) a = paper_out_val_sp LD a"
  unfolding to_generic_law_dat_def by simp

lemma adapter_cand_rel[simp]:
  "cand_rel (to_generic_law_dat LD) a = paper_cand_rel LD a"
  unfolding to_generic_law_dat_def by simp

lemma law_eval_dat_sp_member_derives_well_typed:
  assumes member: "law_eval_dat_sp_member LD"
      and aidx: "a \<in> paper_law_idx LD"
  shows "cand_rel_well_typed (to_generic_law_dat LD) a"
  using member aidx
  unfolding law_eval_dat_sp_member_def cand_rel_well_typed_def
  by simp

lemma paper_k_derives_generic_k:
  assumes kval: "paper_k_cand_rel_right_unique LD"
  shows "k_cand_rel_right_unique (to_generic_law_dat LD)"
  using kval
  unfolding paper_k_cand_rel_right_unique_def
            k_cand_rel_right_unique_def
  by simp

definition paper_cand_rel_dom ::
  "('idx, 'time, 'in, 'out) paper_law_eval_dat
   => 'idx => ('time * 'in) set" where
  "paper_cand_rel_dom LD a =
   cand_rel_dom
     (paper_eval_dom LD a)
     (paper_out_val_sp LD a)
     (paper_cand_rel LD a)"

lemma adapter_domain_is_paper_domain[simp]:
  "cand_rel_dom_of (to_generic_law_dat LD) a = paper_cand_rel_dom LD a"
  unfolding cand_rel_dom_of_def paper_cand_rel_dom_def by simp

lemma restricted_graph_equality_gives_pointwise:
  assumes xD: "x \<in> D"
      and fg: "restricted_graph D f = restricted_graph D g"
  shows "f x = g x"
proof -
  have "(x, f x) \<in> restricted_graph D f"
    using xD unfolding restricted_graph_def by auto
  then have "(x, f x) \<in> restricted_graph D g"
    using fg by simp
  then show ?thesis
    unfolding restricted_graph_def by auto
qed

theorem law_eval_dat_sp_partial_output_map_adapter:
  assumes member: "law_eval_dat_sp_member LD"
      and aidx: "a \<in> paper_law_idx LD"
      and kval: "paper_k_cand_rel_right_unique LD"
  shows "\<exists>f.
    maps_dom_into
      (paper_cand_rel_dom LD a)
      (paper_out_val_sp LD a) f
    \<and> paper_cand_rel LD a =
      restricted_graph (paper_cand_rel_dom LD a) f
    \<and> (\<forall>g.
      maps_dom_into
        (paper_cand_rel_dom LD a)
        (paper_out_val_sp LD a) g
      \<longrightarrow> paper_cand_rel LD a =
        restricted_graph (paper_cand_rel_dom LD a) g
      \<longrightarrow> (\<forall>x\<in>paper_cand_rel_dom LD a. g x = f x))"
proof -
  let ?GD = "to_generic_law_dat LD"
  have wt: "cand_rel_well_typed ?GD a"
    using law_eval_dat_sp_member_derives_well_typed[OF member aidx] .
  have gk: "k_cand_rel_right_unique ?GD"
    using paper_k_derives_generic_k[OF kval] .
  have aidxG: "a \<in> law_idx ?GD"
    using aidx by simp
  obtain f where
      fmap:
        "maps_dom_into
          (cand_rel_dom_of ?GD a)
          (out_val_sp ?GD a) f"
    and graph:
        "cand_rel ?GD a =
          restricted_graph (cand_rel_dom_of ?GD a) f"
    and uniq_graph:
        "\<forall>g.
          maps_dom_into
            (cand_rel_dom_of ?GD a)
            (out_val_sp ?GD a) g
          \<longrightarrow> cand_rel ?GD a =
            restricted_graph (cand_rel_dom_of ?GD a) g
          \<longrightarrow>
            restricted_graph (cand_rel_dom_of ?GD a) g =
            restricted_graph (cand_rel_dom_of ?GD a) f"
    using law_candidate_relation_partial_output_map[OF aidxG wt gk]
    by auto
  show ?thesis
  proof (intro exI conjI)
    show "maps_dom_into
      (paper_cand_rel_dom LD a)
      (paper_out_val_sp LD a) f"
      using fmap by simp
    show "paper_cand_rel LD a =
      restricted_graph (paper_cand_rel_dom LD a) f"
      using graph by simp
    show "\<forall>g.
      maps_dom_into
        (paper_cand_rel_dom LD a)
        (paper_out_val_sp LD a) g
      \<longrightarrow> paper_cand_rel LD a =
        restricted_graph (paper_cand_rel_dom LD a) g
      \<longrightarrow> (\<forall>x\<in>paper_cand_rel_dom LD a. g x = f x)"
    proof (intro allI impI)
      fix g
      assume gmap:
        "maps_dom_into
          (paper_cand_rel_dom LD a)
          (paper_out_val_sp LD a) g"
      assume ggraph:
        "paper_cand_rel LD a =
          restricted_graph (paper_cand_rel_dom LD a) g"
      have rg:
        "restricted_graph (paper_cand_rel_dom LD a) g =
         restricted_graph (paper_cand_rel_dom LD a) f"
        using uniq_graph gmap ggraph by simp
      show "\<forall>x\<in>paper_cand_rel_dom LD a. g x = f x"
        using restricted_graph_equality_gives_pointwise[OF _ rg]
        by auto
    qed
  qed
qed

lemma adapter_empty_eval_domain:
  assumes "paper_eval_dom LD a = {}"
  shows "paper_cand_rel_dom LD a = {}"
  using assms unfolding paper_cand_rel_dom_def cand_rel_dom_def by auto

end
