theory Core_Affine_Realization
 imports Main
begin

definition order_condition where
 "order_condition S f r s \<longleftrightarrow> (\<forall>x\<in>S. \<forall>y\<in>S. s(f x)(f y) \<longleftrightarrow> r x y)"

theorem order_embedding_pullback_iff:
 assumes maps: "image f S \<subseteq> T" and inj: "inj_on f S"
 shows "order_condition S f r s \<longleftrightarrow>
  (\<lambda>x y. x\<in>S \<and> y\<in>S \<and> s(f x)(f y)) = (\<lambda>x y. x\<in>S \<and> y\<in>S \<and> r x y)"
 unfolding order_condition_def by (auto intro!: ext dest: fun_cong)

locale affine_realization =
 fixes P :: "'p set"
 and act :: "'p\<Rightarrow>'k::linordered_field\<Rightarrow>'p"
 and diff :: "'p\<Rightarrow>'p\<Rightarrow>'k"
 and lt :: "'p\<Rightarrow>'p\<Rightarrow>bool"
 assumes closed: "a\<in>P \<Longrightarrow> act a x\<in>P"
 and zero_action: "a\<in>P \<Longrightarrow> act a 0=a"
 and add_action: "a\<in>P \<Longrightarrow> act a (x+y)=act(act a x)y"
 and diff_spec: "a\<in>P \<Longrightarrow> b\<in>P \<Longrightarrow> (act a x=b \<longleftrightarrow> x=diff b a)"
 and strict_sign: "a\<in>P \<Longrightarrow> b\<in>P \<Longrightarrow> (lt a b \<longleftrightarrow> 0<diff b a)"
begin

theorem action_free:
 assumes a: "a\<in>P" and eq: "act a x=act a y"
 shows "x=y"
proof -
 have mem: "act a y\<in>P" by (rule closed[OF a])
 have x: "x=diff (act a y) a" using diff_spec[OF a mem, of x] eq by simp
 have y: "y=diff (act a y) a" using diff_spec[OF a mem, of y] by simp
 show ?thesis using x y by simp
qed

theorem action_transitive:
 assumes a: "a\<in>P" and b: "b\<in>P"
 shows "\<exists>!x. act a x=b"
 by (rule ex1I[of _ "diff b a"]) (simp_all add: diff_spec[OF a b])

theorem difference_reflexive:
 assumes a: "a\<in>P"
 shows "diff a a=0"
 using diff_spec[OF a a, of 0] zero_action[OF a] by simp

theorem difference_zero_iff:
 assumes a: "a\<in>P" and b: "b\<in>P"
 shows "diff b a=0 \<longleftrightarrow> a=b"
 using diff_spec[OF a b, of 0] zero_action[OF a] by auto

theorem difference_cocycle:
 assumes a: "a\<in>P" and b: "b\<in>P" and c: "c\<in>P"
 shows "diff c a=diff b a+diff c b"
proof -
 have ab: "act a (diff b a)=b" using diff_spec[OF a b] by simp
 have bc: "act b (diff c b)=c" using diff_spec[OF b c] by simp
 have ac: "act a (diff b a+diff c b)=c" by (simp only: add_action[OF a] ab bc)
 show ?thesis using diff_spec[OF a c, of "diff b a+diff c b"] ac by simp
qed

theorem difference_reverse:
 assumes a: "a\<in>P" and b: "b\<in>P"
 shows "diff a b= -diff b a"
proof -
 have sum: "diff b a+diff a b=0"
  using difference_cocycle[OF a b a] difference_reflexive[OF a] by simp
 have "diff a b= -diff b a+(diff b a+diff a b)" by simp
 also have "...= -diff b a" using sum by simp
 finally show ?thesis .
qed

theorem induced_strict_linear:
 "(\<forall>a\<in>P. \<not>lt a a) \<and>
  (\<forall>a\<in>P. \<forall>b\<in>P. \<forall>c\<in>P. lt a b \<longrightarrow> lt b c \<longrightarrow> lt a c) \<and>
  (\<forall>a\<in>P. \<forall>b\<in>P. a\<noteq>b \<longrightarrow> lt a b \<or> lt b a)"
proof -
 have irr: "\<And>a. a\<in>P \<Longrightarrow> \<not>lt a a"
  by (simp add: strict_sign difference_reflexive)
 have trans: "\<And>a b c. a\<in>P \<Longrightarrow> b\<in>P \<Longrightarrow> c\<in>P \<Longrightarrow> lt a b \<Longrightarrow> lt b c \<Longrightarrow> lt a c"
 proof -
  fix a b c assume a: "a\<in>P" and b: "b\<in>P" and c: "c\<in>P"
   and ab: "lt a b" and bc: "lt b c"
  have pos: "0<diff b a+diff c b" using ab bc strict_sign[OF a b] strict_sign[OF b c] by simp
  show "lt a c" using strict_sign[OF a c] difference_cocycle[OF a b c] pos by simp
 qed
 have total: "\<And>a b. a\<in>P \<Longrightarrow> b\<in>P \<Longrightarrow> a\<noteq>b \<Longrightarrow> lt a b \<or> lt b a"
 proof -
  fix a b assume a: "a\<in>P" and b: "b\<in>P" and neq: "a\<noteq>b"
  have nonzero: "diff b a\<noteq>0" using difference_zero_iff[OF a b] neq by simp
  consider (neg) "diff b a<0" | (pos) "0<diff b a"
   using less_linear[of "diff b a" 0] nonzero by blast
  then show "lt a b \<or> lt b a"
  proof cases
   case neg
   have "0<diff a b" using difference_reverse[OF a b] neg by simp
   then show ?thesis using strict_sign[OF b a] by blast
  next
   case pos
   then show ?thesis using strict_sign[OF a b] by blast
  qed
 qed
 show ?thesis using irr trans total by blast
qed

definition coordinate_difference where
 "coordinate_difference projection embedding x1 x0=diff (embedding(projection x1)) (embedding(projection x0))"

theorem coordinate_difference_sign:
 assumes prj: "image projection X\<subseteq>Q" and emb: "image embedding Q\<subseteq>P"
 and inj: "inj_on embedding Q" and x0: "x0\<in>X" and x1: "x1\<in>X"
 shows "lt(embedding(projection x0))(embedding(projection x1)) \<longleftrightarrow>
  0<coordinate_difference projection embedding x1 x0"
proof -
 have a: "embedding(projection x0)\<in>P" and b: "embedding(projection x1)\<in>P"
  using prj emb x0 x1 by blast+
 show ?thesis unfolding coordinate_difference_def by (rule strict_sign[OF a b])
qed
end

ML \<open>
val roots = @{thms order_embedding_pullback_iff affine_realization.action_free
 affine_realization.action_transitive affine_realization.difference_reflexive
 affine_realization.difference_zero_iff affine_realization.difference_cocycle
 affine_realization.difference_reverse affine_realization.induced_strict_linear
 affine_realization.coordinate_difference_sign};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
