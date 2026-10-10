theory Law_Candidate_Relation_Isabelle
imports Main
begin

definition right_unique :: "'a set => 'b set => ('a * 'b) set => bool" where
  "right_unique X Y R =
   (\<forall>x\<in>X. \<forall>y0\<in>Y. \<forall>y1\<in>Y.
    (x,y0) \<in> R \<longrightarrow> (x,y1) \<in> R \<longrightarrow> y0 = y1)"

definition cand_rel_dom :: "'a set => 'b set => ('a * 'b) set => 'a set" where
  "cand_rel_dom X Y R = {x \<in> X. \<exists>y\<in>Y. (x,y) \<in> R}"

definition restricted_graph :: "'a set => ('a => 'b) => ('a * 'b) set" where
  "restricted_graph D f = {(x, f x) |x. x \<in> D}"

definition out_choice :: "('a * 'b) set => 'a => 'b" where
  "out_choice R x = (SOME y. (x,y) \<in> R)"

definition maps_dom_into :: "'a set => 'b set => ('a => 'b) => bool" where
  "maps_dom_into D Y f = (\<forall>x\<in>D. f x \<in> Y)"

record ('idx, 'inp, 'out) law_dat =
  law_idx :: "'idx set"
  in_val_sp :: "'idx => 'inp set"
  out_val_sp :: "'idx => 'out set"
  cand_rel :: "'idx => ('inp * 'out) set"

definition cand_rel_well_typed :: "('idx, 'inp, 'out) law_dat => 'idx => bool" where
  "cand_rel_well_typed LD a =
   (cand_rel LD a \<subseteq> in_val_sp LD a \<times> out_val_sp LD a)"

definition k_cand_rel_right_unique :: "('idx, 'inp, 'out) law_dat => bool" where
  "k_cand_rel_right_unique LD =
   (\<forall>a\<in>law_idx LD.
    right_unique (in_val_sp LD a) (out_val_sp LD a) (cand_rel LD a))"

definition cand_rel_dom_of :: "('idx, 'inp, 'out) law_dat => 'idx => 'inp set" where
  "cand_rel_dom_of LD a =
   cand_rel_dom (in_val_sp LD a) (out_val_sp LD a) (cand_rel LD a)"

lemma out_choice_in_relation:
  assumes xd: "x \<in> cand_rel_dom X Y R"
  shows "(x, out_choice R x) \<in> R"
proof -
  from xd obtain y where "(x,y) \<in> R"
    unfolding cand_rel_dom_def by auto
  then show ?thesis unfolding out_choice_def by (rule someI)
qed

lemma out_choice_in_output:
  assumes t: "R \<subseteq> X \<times> Y"
      and xd: "x \<in> cand_rel_dom X Y R"
  shows "out_choice R x \<in> Y"
  using t out_choice_in_relation[OF xd] by auto

lemma right_unique_choice:
  assumes t: "R \<subseteq> X \<times> Y"
      and ru: "right_unique X Y R"
      and p: "(x,y) \<in> R"
  shows "y = out_choice R x"
proof -
  have xX: "x \<in> X" and yY: "y \<in> Y" using t p by auto
  have xd: "x \<in> cand_rel_dom X Y R"
    using t p unfolding cand_rel_dom_def by auto
  have cr: "(x, out_choice R x) \<in> R" using out_choice_in_relation[OF xd] .
  have cy: "out_choice R x \<in> Y" using out_choice_in_output[OF t xd] .
  show ?thesis using ru xX yY cy p cr unfolding right_unique_def by auto
qed

lemma relation_equals_restricted_graph:
  assumes t: "R \<subseteq> X \<times> Y"
      and ru: "right_unique X Y R"
  shows "R = restricted_graph (cand_rel_dom X Y R) (out_choice R)"
proof
  show "R \<subseteq> restricted_graph (cand_rel_dom X Y R) (out_choice R)"
  proof
    fix p assume pR: "p \<in> R"
    obtain x y where pxy: "p = (x,y)" by (cases p) auto
    have xd: "x \<in> cand_rel_dom X Y R"
      using t pR pxy unfolding cand_rel_dom_def by auto
    have eq: "y = out_choice R x"
      using right_unique_choice[OF t ru] pR pxy by simp
    show "p \<in> restricted_graph (cand_rel_dom X Y R) (out_choice R)"
      using xd pxy eq unfolding restricted_graph_def by auto
  qed
next
  show "restricted_graph (cand_rel_dom X Y R) (out_choice R) \<subseteq> R"
    using out_choice_in_relation unfolding restricted_graph_def by auto
qed

theorem right_unique_relation_has_domain_graph:
  assumes t: "R \<subseteq> X \<times> Y"
      and ru: "right_unique X Y R"
  shows "\<exists>f.
   maps_dom_into (cand_rel_dom X Y R) Y f
   \<and> R = restricted_graph (cand_rel_dom X Y R) f
   \<and> (\<forall>g.
     maps_dom_into (cand_rel_dom X Y R) Y g
     \<longrightarrow> R = restricted_graph (cand_rel_dom X Y R) g
     \<longrightarrow> restricted_graph (cand_rel_dom X Y R) g =
                    restricted_graph (cand_rel_dom X Y R) f)"
proof (intro exI conjI)
  show "maps_dom_into (cand_rel_dom X Y R) Y (out_choice R)"
    using out_choice_in_output[OF t] unfolding maps_dom_into_def by auto
  show "R = restricted_graph (cand_rel_dom X Y R) (out_choice R)"
    using relation_equals_restricted_graph[OF t ru] .
  show "\<forall>g.
     maps_dom_into (cand_rel_dom X Y R) Y g
     \<longrightarrow> R = restricted_graph (cand_rel_dom X Y R) g
     \<longrightarrow> restricted_graph (cand_rel_dom X Y R) g =
                    restricted_graph (cand_rel_dom X Y R) (out_choice R)"
    using relation_equals_restricted_graph[OF t ru] by auto
qed

theorem law_candidate_relation_partial_output_map:
  assumes aidx: "a \<in> law_idx LD"
      and t: "cand_rel_well_typed LD a"
      and kval: "k_cand_rel_right_unique LD"
  shows "\<exists>f.
   maps_dom_into (cand_rel_dom_of LD a) (out_val_sp LD a) f
   \<and> cand_rel LD a = restricted_graph (cand_rel_dom_of LD a) f
   \<and> (\<forall>g.
     maps_dom_into (cand_rel_dom_of LD a) (out_val_sp LD a) g
     \<longrightarrow> cand_rel LD a = restricted_graph (cand_rel_dom_of LD a) g
     \<longrightarrow> restricted_graph (cand_rel_dom_of LD a) g =
                    restricted_graph (cand_rel_dom_of LD a) f)"
proof -
  have wt: "cand_rel LD a \<subseteq> in_val_sp LD a \<times> out_val_sp LD a"
    using t unfolding cand_rel_well_typed_def .
  have ru: "right_unique (in_val_sp LD a) (out_val_sp LD a) (cand_rel LD a)"
    using kval aidx unfolding k_cand_rel_right_unique_def by auto
  show ?thesis
    using right_unique_relation_has_domain_graph[OF wt ru]
    unfolding cand_rel_dom_of_def .
qed

lemma empty_input_carrier_domain: "cand_rel_dom {} Y R = {}"
  unfolding cand_rel_dom_def by auto

lemma empty_output_carrier_domain: "cand_rel_dom X {} R = {}"
  unfolding cand_rel_dom_def by auto

lemma empty_paper_carriers_graph_exists:
  assumes "R \<subseteq> {} \<times> {}"
  shows "\<exists>f. R = restricted_graph (cand_rel_dom {} {} R) f"
  using assms unfolding cand_rel_dom_def restricted_graph_def by auto

end
