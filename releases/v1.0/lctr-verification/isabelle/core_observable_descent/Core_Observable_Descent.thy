theory Core_Observable_Descent
  imports Main
begin

locale observable_descent =
  fixes U :: "'u set" and L :: "'l set" and Q :: "'q set" and S :: "'s set"
    and A :: "'u \<Rightarrow> 'a set"
    and idx :: "'l \<Rightarrow> 'q"
    and theta :: "'u \<Rightarrow> 'a \<Rightarrow> 's"
    and val_range :: "'l \<Rightarrow> 'v set"
    and cmp :: "'u \<Rightarrow> 'l \<Rightarrow> 'a \<Rightarrow> 'v"
  assumes idx_onto: "idx ` L = Q"
    and theta_typed: "\<And>u a. u \<in> U \<Longrightarrow> a \<in> A u \<Longrightarrow> theta u a \<in> S"
    and cmp_typed: "\<And>u l a. u \<in> U \<Longrightarrow> l \<in> L \<Longrightarrow> a \<in> A u \<Longrightarrow> cmp u l a \<in> val_range l"
    and range_fiber: "\<And>l k. l \<in> L \<Longrightarrow> k \<in> L \<Longrightarrow> idx l = idx k \<Longrightarrow> val_range l = val_range k"
    and coverage: "\<And>q s. q \<in> Q \<Longrightarrow> s \<in> S \<Longrightarrow> \<exists>u\<in>U. \<exists>l\<in>L. \<exists>a\<in>A u. idx l = q \<and> theta u a = s"
    and value_fiber: "\<And>u v l k a b. u \<in> U \<Longrightarrow> v \<in> U \<Longrightarrow> l \<in> L \<Longrightarrow> k \<in> L \<Longrightarrow> a \<in> A u \<Longrightarrow> b \<in> A v \<Longrightarrow> idx l = idx k \<Longrightarrow> theta u a = theta v b \<Longrightarrow> cmp u l a = cmp v k b"
begin

definition representatives where
  "representatives q s = {w. fst w \<in> U \<and> fst (snd w) \<in> L \<and>
    snd (snd w) \<in> A (fst w) \<and> idx (fst (snd w)) = q \<and> theta (fst w) (snd (snd w)) = s}"
definition chosen where "chosen q s = (SOME w. w \<in> representatives q s)"
definition comparison where "comparison w = cmp (fst w) (fst (snd w)) (snd (snd w))"
definition canonical where "canonical q s = comparison (chosen q s)"
definition index_rep where "index_rep q = (SOME l. l \<in> L \<and> idx l = q)"
definition canonical_range where "canonical_range q = val_range (index_rep q)"

lemma representatives_nonempty:
  assumes q: "q \<in> Q" and s: "s \<in> S"
  shows "representatives q s \<noteq> {}"
  using coverage[OF q s] unfolding representatives_def by auto

lemma chosen_valid:
  assumes q: "q \<in> Q" and s: "s \<in> S"
  shows "chosen q s \<in> representatives q s"
  unfolding chosen_def by (rule someI_ex) (use representatives_nonempty[OF q s] in blast)

lemma index_rep_valid:
  assumes q: "q \<in> Q"
  shows "index_rep q \<in> L \<and> idx (index_rep q) = q"
proof -
  have "\<exists>l. l \<in> L \<and> idx l = q" using q idx_onto by blast
  then show ?thesis unfolding index_rep_def by (rule someI_ex)
qed

lemma range_independent:
  assumes q: "q \<in> Q" and l: "l \<in> L" and eq: "idx l = q"
  shows "val_range l = canonical_range q"
  unfolding canonical_range_def
  by (rule range_fiber[OF l]) (use index_rep_valid[OF q] eq in auto)

lemma representative_values_agree:
  assumes x: "x \<in> representatives q s" and y: "y \<in> representatives q s"
  shows "comparison x = comparison y"
  unfolding comparison_def
  by (rule value_fiber) (use x y in \<open>auto simp: representatives_def\<close>)

lemma canonical_representative:
  assumes q: "q \<in> Q" and s: "s \<in> S" and w: "w \<in> representatives q s"
  shows "canonical q s = comparison w"
  unfolding canonical_def by (rule representative_values_agree[OF chosen_valid[OF q s] w])

lemma canonical_typed:
  assumes q: "q \<in> Q" and s: "s \<in> S"
  shows "canonical q s \<in> canonical_range q"
proof -
  let ?w = "chosen q s"
  have w: "?w \<in> representatives q s" by (rule chosen_valid[OF q s])
  have typed: "comparison ?w \<in> val_range (fst (snd ?w))"
    unfolding comparison_def
    by (rule cmp_typed) (use w in \<open>auto simp: representatives_def\<close>)
  have range: "val_range (fst (snd ?w)) = canonical_range q"
    by (rule range_independent[OF q]) (use w in \<open>auto simp: representatives_def\<close>)
  show ?thesis using typed range unfolding canonical_def by simp
qed

lemma canonical_unique:
  assumes q: "q \<in> Q" and s: "s \<in> S"
    and agrees: "\<And>w. w \<in> representatives q s \<Longrightarrow> f q s = comparison w"
  shows "f q s = canonical q s"
  using agrees[OF chosen_valid[OF q s]] unfolding canonical_def .

lemma local_change_compatibility:
  assumes u: "u \<in> U" and v: "v \<in> U" and l: "l \<in> L" and a: "a \<in> A u"
    and domain: "admitted v u l a"
    and commutes: "\<And>v u l a. v \<in> U \<Longrightarrow> u \<in> U \<Longrightarrow> l \<in> L \<Longrightarrow> a \<in> A u \<Longrightarrow>
      admitted v u l a \<Longrightarrow> changed v u l a = cmp u l a"
  shows "canonical (idx l) (theta u a) = changed v u l a"
proof -
  have q: "idx l \<in> Q" using l idx_onto by blast
  have s: "theta u a \<in> S" by (rule theta_typed[OF u a])
  have w: "(u,l,a) \<in> representatives (idx l) (theta u a)"
    using u l a unfolding representatives_def by simp
  have "canonical (idx l) (theta u a) = cmp u l a"
    using canonical_representative[OF q s w] unfolding comparison_def by simp
  then show ?thesis using commutes[OF v u l a domain] by simp
qed
end

ML \<open>
val roots = @{thms observable_descent.representatives_nonempty
  observable_descent.chosen_valid observable_descent.index_rep_valid
  observable_descent.range_independent observable_descent.representative_values_agree
  observable_descent.canonical_representative observable_descent.canonical_typed
  observable_descent.canonical_unique observable_descent.local_change_compatibility};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int (length roots));
\<close>
end
