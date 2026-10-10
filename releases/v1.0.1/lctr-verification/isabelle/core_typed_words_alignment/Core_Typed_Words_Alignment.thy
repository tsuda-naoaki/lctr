theory Core_Typed_Words_Alignment
  imports "../core_typed_words/Core_Typed_Words"
begin

lemmas empty_action = typed_actions.empty_action
lemmas append_action = typed_actions.action_append
lemmas append_domain = typed_actions.action_append_domain
lemmas reverse_action = typed_actions.action_reverse
lemmas action_functional = typed_actions.action_functional
lemmas action_injective = typed_actions.action_injective

context typed_actions
begin
lemma reverse_domain:
  assumes t: "typed u es v"
  shows "(\<exists>a. action v (map dagger (rev es)) u b a) =
    (\<exists>a. action u es v a b)"
  using action_reverse[OF t] by blast
end

locale tagged_words =
  typed_actions "\<lambda>u. {u}\<times>Y u" Adm src dst dagger act
  for Y :: "'u\<Rightarrow>'x set" and Adm :: "'e set"
    and src dst :: "'e\<Rightarrow>'u" and dagger :: "'e\<Rightarrow>'e"
    and act :: "'e\<Rightarrow>('u\<times>'x)\<Rightarrow>('u\<times>'x)\<Rightarrow>bool"
begin

lemma tags_disjoint:
  "p\<in>{u}\<times>Y u \<Longrightarrow> p\<in>{v}\<times>Y v \<Longrightarrow> u=v"
  by auto

lemma tagged_carrier:
  "carrier = Sigma UNIV Y"
  unfolding carrier_def by auto

lemma orbit_equivalence:
  "equiv (Sigma UNIV Y) {(a,b). orbit a b}"
  using typed_actions.orbit_equivalence[OF typed_actions_axioms tags_disjoint]
  by (simp only: tagged_carrier)

lemma loop_identity_iff_local_projection_injective:
  "loop_identity =
    (\<forall>u. inj_on (\<lambda>a. {(x,y). orbit x y}``{a}) ({u}\<times>Y u))"
  by (rule typed_actions.loop_identity_iff_local_projection_injective[
    OF typed_actions_axioms tags_disjoint])

end

lemma disjoint_union_tag_bridge:
  fixes A :: "'u\<Rightarrow>'x set"
  assumes disj: "\<And>i j x. x\<in>A i \<Longrightarrow> x\<in>A j \<Longrightarrow> i=j"
  shows "bij_betw snd (Sigma UNIV A) (\<Union>i. A i)"
proof -
  have inj: "inj_on snd (Sigma UNIV A)"
  proof (rule inj_onI)
    fix p q
    assume p: "p\<in>Sigma UNIV A" and q: "q\<in>Sigma UNIV A"
      and e: "snd p=snd q"
    have pi: "snd p\<in>A (fst p)" and qi: "snd q\<in>A (fst q)"
      using p q by auto
    have "fst p=fst q" using disj[OF pi] qi e by auto
    with e show "p=q" by (cases p; cases q) auto
  qed
  have image: "snd ` Sigma UNIV A = (\<Union>i. A i)"
  proof
    show "snd ` Sigma UNIV A \<subseteq> (\<Union>i. A i)" by auto
    show "(\<Union>i. A i) \<subseteq> snd ` Sigma UNIV A"
    proof
      fix x
      assume "x\<in>(\<Union>i. A i)"
      then obtain i where xi: "x\<in>A i" by blast
      have "(i,x)\<in>Sigma UNIV A" using xi by simp
      then show "x\<in>snd ` Sigma UNIV A" by (force intro: image_eqI)
    qed
  qed
  show ?thesis using inj image unfolding bij_betw_def by blast
qed

lemma overlapping_regions_lose_tags:
  "\<not> inj_on snd (Sigma UNIV (\<lambda>_::bool. {()}))"
proof
  assume h: "inj_on snd (Sigma UNIV (\<lambda>_::bool. {()}))"
  have eq: "(False,())=(True,())"
    using h unfolding inj_on_def by auto
  then show False by simp
qed

ML \<open>
val roots = @{thms empty_action append_action append_domain reverse_action
  action_functional action_injective typed_actions.reverse_domain
  tagged_words.orbit_equivalence tagged_words.loop_identity_iff_local_projection_injective
  disjoint_union_tag_bridge overlapping_regions_lose_tags};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
