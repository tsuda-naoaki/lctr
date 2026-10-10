theory Core_Typed_Words
  imports Main
begin

fun sequence where
  "sequence act [] x y = (x=y)" |
  "sequence act (e#es) x y = (\<exists>z. act e x z \<and> sequence act es z y)"

lemma sequence_append:
  "sequence act (es@fs) x y = (\<exists>z. sequence act es x z \<and> sequence act fs z y)"
  by (induction es arbitrary: x) auto

lemma sequence_functional:
  assumes functional: "\<And>e a b c. e\<in>set es \<Longrightarrow> act e a b \<Longrightarrow> act e a c \<Longrightarrow> b=c"
    and ab: "sequence act es a b" and ac: "sequence act es a c"
  shows "b=c"
  using assms by (induction es arbitrary: a) (auto, metis)

lemma sequence_reverse:
  assumes inv: "\<And>e a b. e\<in>set es \<Longrightarrow> act (dagger e) b a = act e a b"
  shows "sequence act (map dagger (rev es)) b a = sequence act es a b"
  using inv
  by (induction es arbitrary: a b) (auto simp: sequence_append)

locale typed_actions =
  fixes Y :: "'u\<Rightarrow>'x set" and Adm :: "'e set"
    and src dst :: "'e\<Rightarrow>'u" and dagger :: "'e\<Rightarrow>'e"
    and act :: "'e\<Rightarrow>'x\<Rightarrow>'x\<Rightarrow>bool"
  assumes inv_adm: "e\<in>Adm \<Longrightarrow> dagger e\<in>Adm"
    and inv_src: "e\<in>Adm \<Longrightarrow> src (dagger e)=dst e"
    and inv_dst: "e\<in>Adm \<Longrightarrow> dst (dagger e)=src e"
    and invol: "e\<in>Adm \<Longrightarrow> dagger (dagger e)=e"
    and act_type: "e\<in>Adm \<Longrightarrow> act e a b \<Longrightarrow> a\<in>Y (src e) \<and> b\<in>Y (dst e)"
    and act_fun: "e\<in>Adm \<Longrightarrow> act e a b \<Longrightarrow> act e a c \<Longrightarrow> b=c"
    and act_inv: "e\<in>Adm \<Longrightarrow> act (dagger e) b a = act e a b"
begin

fun typed where
  "typed u [] v = (u=v)" |
  "typed u (e#es) v = (e\<in>Adm \<and> src e=u \<and> typed (dst e) es v)"

lemma typed_atoms: "typed u es v \<Longrightarrow> set es \<subseteq> Adm"
  by (induction es arbitrary: u) auto

lemma typed_append:
  "typed u (es@fs) v = (\<exists>m. typed u es m \<and> typed m fs v)"
  by (induction es arbitrary: u) auto

lemma typed_reverse:
  "typed u es v \<Longrightarrow> typed v (map dagger (rev es)) u"
  by (induction es arbitrary: u)
    (auto simp: typed_append inv_src inv_dst intro: inv_adm)

lemma sequence_end:
  assumes "typed u es v" "a\<in>Y u" "sequence act es a b"
  shows "b\<in>Y v"
  using assms by (induction es arbitrary: u a) (auto dest: act_type)

definition action where
  "action u es v a b = (typed u es v \<and> a\<in>Y u \<and> sequence act es a b)"

lemma empty_action: "action u [] u a b = (a\<in>Y u \<and> a=b)"
  by (simp add: action_def)

lemma action_append:
  assumes p: "typed u es v" and q: "typed v fs w"
  shows "action u (es@fs) w a b = (\<exists>c. action u es v a c \<and> action v fs w c b)"
  using p q sequence_end[where u=u and es=es and v=v]
  unfolding action_def by (auto simp: sequence_append typed_append)

lemma action_append_domain:
  assumes "typed u es v" "typed v fs w"
  shows "(\<exists>b. action u (es@fs) w a b) = (\<exists>c. action u es v a c \<and> (\<exists>b. action v fs w c b))"
  using action_append[OF assms] by blast

lemma action_reverse:
  assumes t: "typed u es v"
  shows "action v (map dagger (rev es)) u b a = action u es v a b"
proof -
  have tr: "typed v (map dagger (rev es)) u" by (rule typed_reverse[OF t])
  have inv: "\<And>e x y. e\<in>set es \<Longrightarrow> act (dagger e) y x = act e x y"
    using typed_atoms[OF t] act_inv by blast
  have eq: "sequence act (map dagger (rev es)) b a = sequence act es a b"
    by (rule sequence_reverse[where es=es and act=act and dagger=dagger and a=a and b=b, OF inv])
  show ?thesis using t tr eq sequence_end[OF t] sequence_end[OF tr]
    unfolding action_def by blast
qed

lemma action_functional:
  "action u es v a b \<Longrightarrow> action u es v a c \<Longrightarrow> b=c"
  using sequence_functional[of es act a b c] typed_atoms act_fun unfolding action_def by blast

lemma action_injective:
  assumes ab: "action u es v a c" and bb: "action u es v b c"
  shows "a=b"
proof -
  have t: "typed u es v" using ab unfolding action_def by blast
  have ra: "action v (map dagger (rev es)) u c a" using action_reverse[OF t, of c a] ab by blast
  have rb: "action v (map dagger (rev es)) u c b" using action_reverse[OF t, of c b] bb by blast
  show ?thesis by (rule action_functional[OF ra rb])
qed

definition orbit where "orbit a b = (\<exists>u es v. action u es v a b)"
definition carrier where "carrier = (\<Union>u. Y u)"

lemma orbit_refl: "a\<in>carrier \<Longrightarrow> orbit a a"
  unfolding carrier_def orbit_def using empty_action by blast

lemma orbit_sym: "orbit a b \<Longrightarrow> orbit b a"
  unfolding orbit_def using action_reverse unfolding action_def by blast

lemma orbit_trans:
  assumes disj: "\<And>u v x. x\<in>Y u \<Longrightarrow> x\<in>Y v \<Longrightarrow> u=v"
    and ab: "orbit a b" and bc: "orbit b c"
  shows "orbit a c"
proof -
  obtain u es v where p: "action u es v a b" using ab unfolding orbit_def by blast
  obtain v' fs w where q: "action v' fs w b c" using bc unfolding orbit_def by blast
  have bv: "b\<in>Y v" using p sequence_end unfolding action_def by blast
  have bv': "b\<in>Y v'" using q unfolding action_def by blast
  have veq: "v=v'" by (rule disj[OF bv bv'])
  have te: "typed u es v" and tf: "typed v fs w" using p q veq unfolding action_def by blast+
  have "action u (es@fs) w a c" using action_append[OF te tf, of a c] p q veq by blast
  then show ?thesis unfolding orbit_def by blast
qed

lemma orbit_equivalence:
  assumes disj: "\<And>u v x. x\<in>Y u \<Longrightarrow> x\<in>Y v \<Longrightarrow> u=v"
  shows "equiv carrier {(a,b). orbit a b}"
proof -
  have typed_membership: "\<And>a b. orbit a b \<Longrightarrow> a\<in>carrier \<and> b\<in>carrier"
  proof -
    fix a b
    assume "orbit a b"
    then obtain u es v where p: "action u es v a b" unfolding orbit_def by blast
    have t: "typed u es v" and ay: "a\<in>Y u" and run: "sequence act es a b"
      using p unfolding action_def by blast+
    have by_mem: "b\<in>Y v" by (rule sequence_end[OF t ay run])
    show "a\<in>carrier \<and> b\<in>carrier" using ay by_mem unfolding carrier_def by blast
  qed
  have rf: "refl_on carrier {(a,b). orbit a b}"
    unfolding refl_on_def using typed_membership orbit_refl by auto
  have sy: "sym {(a,b). orbit a b}"
    unfolding sym_def using orbit_sym by auto
  have tr: "trans {(a,b). orbit a b}"
    unfolding trans_def
  proof (intro allI impI)
    fix a b c
    assume ab: "(a,b)\<in>{(a,b). orbit a b}" and bc: "(b,c)\<in>{(a,b). orbit a b}"
    have oa: "orbit a b" using ab by simp
    have ob: "orbit b c" using bc by simp
    have "orbit a c" by (rule orbit_trans[OF disj oa ob])
    then show "(a,c)\<in>{(a,b). orbit a b}" by simp
  qed
  have rel_type: "{(a,b). orbit a b} \<subseteq> carrier\<times>carrier"
    using typed_membership by auto
  show ?thesis using rel_type rf sy tr unfolding equiv_def by blast
qed

definition loop_identity where
  "loop_identity = (\<forall>u es a b. action u es u a b \<longrightarrow> a=b)"

lemma loop_identity_iff_local_projection_injective:
  assumes disj: "\<And>u v x. x\<in>Y u \<Longrightarrow> x\<in>Y v \<Longrightarrow> u=v"
  shows "loop_identity = (\<forall>u. inj_on (\<lambda>a. {(x,y). orbit x y}``{a}) (Y u))"
proof -
  let ?E = "{(x,y). orbit x y}"
  have eqv: "equiv carrier ?E" by (rule orbit_equivalence[OF disj])
  have same: "\<And>u a b. a\<in>Y u \<Longrightarrow> b\<in>Y u \<Longrightarrow> (?E``{a}=?E``{b}) = orbit a b"
    using eq_equiv_class_iff[OF eqv] unfolding carrier_def by blast
  have closed: "\<And>u a b. a\<in>Y u \<Longrightarrow> b\<in>Y u \<Longrightarrow> orbit a b \<Longrightarrow> \<exists>es. action u es u a b"
  proof -
    fix u a b
    assume a: "a\<in>Y u" and b: "b\<in>Y u" and o: "orbit a b"
    obtain i es j where act: "action i es j a b" using o unfolding orbit_def by blast
    have ai: "a\<in>Y i" and bj: "b\<in>Y j" using act sequence_end unfolding action_def by blast+
    have "i=u" and "j=u" using disj[OF ai a] disj[OF bj b] by auto
    then show "\<exists>es. action u es u a b" using act by blast
  qed
  show ?thesis
  proof
    assume lid: "loop_identity"
    show "\<forall>u. inj_on (\<lambda>a. ?E``{a}) (Y u)"
    proof (intro allI inj_onI)
      fix u a b
      assume ay: "a\<in>Y u" and by_mem: "b\<in>Y u" and eq: "?E``{a}=?E``{b}"
      have o: "orbit a b" using same[OF ay by_mem] eq by blast
      obtain es where "action u es u a b" using closed[OF ay by_mem o] by blast
      then show "a=b" using lid unfolding loop_identity_def by blast
    qed
  next
    assume inj: "\<forall>u. inj_on (\<lambda>a. ?E``{a}) (Y u)"
    show loop_identity unfolding loop_identity_def
    proof (intro allI impI)
      fix u es a b
      assume p: "action u es u a b"
      have t: "typed u es u" and ay: "a\<in>Y u" and run: "sequence act es a b"
        using p unfolding action_def by blast+
      have by_mem: "b\<in>Y u" by (rule sequence_end[OF t ay run])
      have o: "orbit a b" using p unfolding orbit_def by blast
      have eq: "?E``{a}=?E``{b}" using same[OF ay by_mem] o by blast
      show "a=b" using inj eq ay by_mem unfolding inj_on_def by blast
    qed
  qed
qed

end

ML \<open>
val roots = @{thms sequence_append sequence_functional sequence_reverse
  typed_actions.action_append typed_actions.action_append_domain typed_actions.action_reverse
  typed_actions.action_functional typed_actions.action_injective typed_actions.orbit_equivalence
  typed_actions.loop_identity_iff_local_projection_injective};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
