theory Core_Law_Transport
  imports "LCTR_Core_Native_Law_Family.Core_Native_Law_Family"
begin
locale carrier_bijection =
  fixes T :: "'t set" and U :: "'u set" and f :: "'t \<Rightarrow> 'u" and g :: "'u \<Rightarrow> 't"
  assumes forward_typed: "image f T\<subseteq>U" and inverse_typed: "image g U\<subseteq>T"
    and left_inverse: "\<And>t. t\<in>T \<Longrightarrow> g(f t)=t"
    and right_inverse: "\<And>u. u\<in>U \<Longrightarrow> f(g u)=u"
begin
lemma injective: "inj_on f T"
proof (rule inj_onI)
  fix x y assume x: "x\<in>T" and y: "y\<in>T" and eq: "f x=f y"
  have "g(f x)=g(f y)" using eq by simp
  then show "x=y" using left_inverse[OF x] left_inverse[OF y] by simp
qed
lemma surjective: "image f T=U"
proof (rule antisym)
  show "image f T\<subseteq>U" by (rule forward_typed)
  show "U\<subseteq>image f T"
  proof (rule subsetI)
    fix u assume u: "u\<in>U"
    have gt: "g u\<in>T" using inverse_typed u by blast
    have "f(g u)\<in>image f T" by (rule imageI[OF gt])
    then show "u\<in>image f T" using right_inverse[OF u] by simp
  qed
qed
lemma image_as_inverse:
  assumes sub: "S\<subseteq>T"
  shows "image f S={u\<in>U. g u\<in>S}"
proof (rule equalityI)
  show "image f S\<subseteq>{u\<in>U. g u\<in>S}"
  proof (rule subsetI)
    fix u assume "u\<in>image f S"
    then obtain s where s: "s\<in>S" and us: "u=f s" by blast
    have st: "s\<in>T" using sub s by blast
    have fu: "f s\<in>U" using forward_typed st by blast
    show "u\<in>{u\<in>U. g u\<in>S}" using us fu s left_inverse[OF st] by simp
  qed
  show "{u\<in>U. g u\<in>S}\<subseteq>image f S"
  proof (rule subsetI)
    fix u assume "u\<in>{u\<in>U. g u\<in>S}"
    then have u: "u\<in>U" and gs: "g u\<in>S" by auto
    have "f(g u)\<in>image f S" by (rule imageI[OF gs])
    then show "u\<in>image f S" using right_inverse[OF u] by simp
  qed
qed
lemma inverse_image:
  assumes sub: "S\<subseteq>T"
  shows "image g (image f S)=S"
proof -
  have eq: "image (\<lambda>x. g(f x)) S=image id S"
    by (rule image_cong[OF refl]; use sub left_inverse in auto)
  show ?thesis using eq by (simp add: image_image)
qed
lemma image_injective:
  assumes a: "A\<subseteq>T" and b: "B\<subseteq>T"
  shows "(image f A=image f B)\<longleftrightarrow>A=B"
  using inverse_image[OF a] inverse_image[OF b] by metis
end

definition pair_change where "pair_change f z=(f(fst z),snd z)"
definition tuple_change where "tuple_change f z=((f(fst(fst z)),snd(fst z)),snd z)"
definition component_transport where
  "component_transport f g c=\<lparr>eval_times=image f(eval_times c),
    input_value=input_value c \<circ> g, output_value=output_value c \<circ> g,
    eval_domain=image (pair_change f)(eval_domain c),
    law_relation=image (tuple_change f)(law_relation c)\<rparr>"
definition conjugate_reindex where
  "conjugate_reindex h k p=\<lparr>forward_map=h \<circ> forward_map p \<circ> k,
    inverse_map=h \<circ> inverse_map p \<circ> k\<rparr>"

context carrier_bijection
begin
lemma conjugate_typed:
  assumes p: "reindex_on T p"
  shows "reindex_on U (conjugate_reindex f g p)"
proof -
  have pf: "image(forward_map p) T\<subseteq>T" and pi: "image(inverse_map p) T\<subseteq>T"
    using p unfolding reindex_on_def by auto
  have ft: "image(forward_map(conjugate_reindex f g p)) U\<subseteq>U"
    using pf forward_typed inverse_typed
    unfolding conjugate_reindex_def
    by (simp only: carrier_reindex.select_convs comp_def; blast)
  have it: "image(inverse_map(conjugate_reindex f g p)) U\<subseteq>U"
    using pi forward_typed inverse_typed
    unfolding conjugate_reindex_def
    by (simp only: carrier_reindex.select_convs comp_def; blast)
  have le: "\<And>u. u\<in>U \<Longrightarrow> inverse_map(conjugate_reindex f g p)(forward_map(conjugate_reindex f g p)u)=u"
  proof -
    fix u assume u: "u\<in>U"
    have gt: "g u\<in>T" using inverse_typed u by blast
    have pt: "forward_map p(g u)\<in>T" using pf gt by blast
    have lp: "inverse_map p(forward_map p(g u))=g u" using p gt unfolding reindex_on_def by blast
    show "inverse_map(conjugate_reindex f g p)(forward_map(conjugate_reindex f g p)u)=u"
      by (simp add: conjugate_reindex_def left_inverse[OF pt] lp right_inverse[OF u])
  qed
  have ri: "\<And>u. u\<in>U \<Longrightarrow> forward_map(conjugate_reindex f g p)(inverse_map(conjugate_reindex f g p)u)=u"
  proof -
    fix u assume u: "u\<in>U"
    have gt: "g u\<in>T" using inverse_typed u by blast
    have pt: "inverse_map p(g u)\<in>T" using pi gt by blast
    have rp: "forward_map p(inverse_map p(g u))=g u" using p gt unfolding reindex_on_def by blast
    show "forward_map(conjugate_reindex f g p)(inverse_map(conjugate_reindex f g p)u)=u"
      by (simp add: conjugate_reindex_def left_inverse[OF pt] rp right_inverse[OF u])
  qed
  show ?thesis using ft it le ri unfolding reindex_on_def by blast
qed
lemma conjugate_invariance:
  assumes p: "reindex_on T p" and sub: "P\<subseteq>T"
  shows "(image(forward_map(conjugate_reindex f g p))(image f P)=image f P)
    \<longleftrightarrow> image(forward_map p) P=P"
proof -
  have typed: "image(forward_map p) P\<subseteq>T" using p sub unfolding reindex_on_def by blast
  have eq: "image(forward_map(conjugate_reindex f g p))(image f P)=image f(image(forward_map p)P)"
    unfolding conjugate_reindex_def
    by (simp only: carrier_reindex.select_convs comp_apply image_image;
      rule image_cong[OF refl]; use sub left_inverse in auto)
  show ?thesis unfolding eq using image_injective[OF typed sub] .
qed
end

locale law_transport = carrier_bijection T U f g
  for T :: "'t set" and U :: "'u set" and f :: "'t\<Rightarrow>'u" and g :: "'u\<Rightarrow>'t" +
  fixes d :: "('t,'a,'x,'y) law_family"
  assumes source_time: "time_carrier d=T" and wf: "well_typed_family d"
begin
abbreviation old where "old a \<equiv> components d a"
abbreviation moved where "moved a \<equiv> component_transport f g (old a)"
lemma component_bounds:
  assumes a: "a\<in>law_indices d"
  shows "eval_times(old a)\<subseteq>T"
    and "eval_domain(old a)\<subseteq>T\<times>input_carrier d a"
    and "law_relation(old a)\<subseteq>(T\<times>input_carrier d a)\<times>output_carrier d a"
  using wf a unfolding well_typed_family_def source_time by auto
lemma domain_forward:
  assumes a: "a\<in>law_indices d" and t: "t\<in>T"
  shows "(f t,x)\<in>eval_domain(moved a) \<longleftrightarrow> (t,x)\<in>eval_domain(old a)"
proof
  assume h: "(f t,x)\<in>eval_domain(moved a)"
  obtain s where s: "(s,x)\<in>eval_domain(old a)" and eq: "f s=f t"
    using h unfolding component_transport_def pair_change_def by auto
  have st: "s\<in>T" using component_bounds(2)[OF a] s by auto
  have "s=t" by (rule inj_onD[OF injective eq st t])
  then show "(t,x)\<in>eval_domain(old a)" using s by simp
next
  assume h: "(t,x)\<in>eval_domain(old a)"
  have "pair_change f(t,x)\<in>image(pair_change f)(eval_domain(old a))" by (rule imageI[OF h])
  then show "(f t,x)\<in>eval_domain(moved a)" by (simp add: component_transport_def pair_change_def)
qed
lemma relation_forward:
  assumes a: "a\<in>law_indices d" and t: "t\<in>T"
  shows "((f t,x),y)\<in>law_relation(moved a) \<longleftrightarrow> ((t,x),y)\<in>law_relation(old a)"
proof
  assume h: "((f t,x),y)\<in>law_relation(moved a)"
  obtain s where s: "((s,x),y)\<in>law_relation(old a)" and eq: "f s=f t"
    using h unfolding component_transport_def tuple_change_def by auto
  have st: "s\<in>T" using component_bounds(3)[OF a] s by auto
  have "s=t" by (rule inj_onD[OF injective eq st t])
  then show "((t,x),y)\<in>law_relation(old a)" using s by simp
next
  assume h: "((t,x),y)\<in>law_relation(old a)"
  have "tuple_change f((t,x),y)\<in>image(tuple_change f)(law_relation(old a))" by (rule imageI[OF h])
  then show "((f t,x),y)\<in>law_relation(moved a)" by (simp add: component_transport_def tuple_change_def)
qed
lemma evaluation_tuple:
  assumes a: "a\<in>law_indices d" and t: "t\<in>eval_times(old a)"
  shows "((f t,input_value(moved a)(f t)),output_value(moved a)(f t))=
    tuple_change f ((t,input_value(old a)t),output_value(old a)t)"
  using component_bounds(1)[OF a] t left_inverse
  by (auto simp: component_transport_def tuple_change_def)
lemma condition1_component:
  assumes a: "a\<in>law_indices d"
  shows "individual_admissible(moved a)\<longleftrightarrow>individual_admissible(old a)"
proof -
  have nonempty: "(eval_times(moved a)\<noteq>{})=(eval_times(old a)\<noteq>{})"
    by (simp add: component_transport_def)
  have pointwise: "\<And>t. t\<in>eval_times(old a) \<Longrightarrow>
    ((f t,input_value(moved a)(f t))\<in>eval_domain(moved a) \<longleftrightarrow>
      (t,input_value(old a)t)\<in>eval_domain(old a))"
  proof -
    fix t assume t: "t\<in>eval_times(old a)"
    have tt: "t\<in>T" using component_bounds(1)[OF a] t by blast
    show "(f t,input_value(moved a)(f t))\<in>eval_domain(moved a) \<longleftrightarrow>
      (t,input_value(old a)t)\<in>eval_domain(old a)"
      using domain_forward[OF a tt, of "input_value(old a)t"] left_inverse[OF tt]
      by (simp add: component_transport_def)
  qed
  show ?thesis using nonempty pointwise
    unfolding individual_admissible_def
    by (simp only: component_transport_def law_component.select_convs; blast)
qed
lemma condition2_component:
  assumes a: "a\<in>law_indices d"
  shows "right_unique(moved a)\<longleftrightarrow>right_unique(old a)"
proof
  assume h: "right_unique(moved a)"
  show "right_unique(old a)"
    unfolding right_unique_def
  proof (intro allI impI)
    fix t x y z
    assume y: "((t,x),y)\<in>law_relation(old a)" and z: "((t,x),z)\<in>law_relation(old a)"
    have tt: "t\<in>T" using component_bounds(3)[OF a] y by auto
    have yy: "((f t,x),y)\<in>law_relation(moved a)" using relation_forward[OF a tt] y by simp
    have zz: "((f t,x),z)\<in>law_relation(moved a)" using relation_forward[OF a tt] z by simp
    show "y=z" using h yy zz unfolding right_unique_def by blast
  qed
next
  assume h: "right_unique(old a)"
  show "right_unique(moved a)"
    unfolding right_unique_def
  proof (intro allI impI)
    fix u x y z
    assume y: "((u,x),y)\<in>law_relation(moved a)" and z: "((u,x),z)\<in>law_relation(moved a)"
    obtain t where yt: "((t,x),y)\<in>law_relation(old a)" and uf: "u=f t"
      using y unfolding component_transport_def tuple_change_def by auto
    have tt: "t\<in>T" using component_bounds(3)[OF a] yt by auto
    have zt: "((t,x),z)\<in>law_relation(old a)" using relation_forward[OF a tt] z uf by simp
    show "y=z" using h yt zt unfolding right_unique_def by blast
  qed
qed
lemma generated_component:
  assumes a: "a\<in>law_indices d"
  shows "generated_member(moved a)\<longleftrightarrow>generated_member(old a)"
proof -
  have pointwise: "\<And>t. t\<in>eval_times(old a) \<Longrightarrow>
    (((f t,input_value(moved a)(f t)),output_value(moved a)(f t))\<in>law_relation(moved a) \<longleftrightarrow>
      ((t,input_value(old a)t),output_value(old a)t)\<in>law_relation(old a))"
  proof -
    fix t assume t: "t\<in>eval_times(old a)"
    have tt: "t\<in>T" using component_bounds(1)[OF a] t by blast
    show "((f t,input_value(moved a)(f t)),output_value(moved a)(f t))\<in>law_relation(moved a) \<longleftrightarrow>
      ((t,input_value(old a)t),output_value(old a)t)\<in>law_relation(old a)"
      using relation_forward[OF a tt, of "input_value(old a)t" "output_value(old a)t"] left_inverse[OF tt]
      by (simp add: component_transport_def)
  qed
  show ?thesis using pointwise unfolding generated_member_def
    by (simp only: component_transport_def law_component.select_convs; blast)
qed
lemma valid_times_image:
  assumes a: "a\<in>law_indices d"
  shows "valid_times(moved a)=image f(valid_times(old a))"
proof -
  have pointwise: "\<And>t. t\<in>eval_times(old a) \<Longrightarrow>
    (((f t,input_value(moved a)(f t)),output_value(moved a)(f t))\<in>law_relation(moved a) \<longleftrightarrow>
      ((t,input_value(old a)t),output_value(old a)t)\<in>law_relation(old a))"
  proof -
    fix t assume t: "t\<in>eval_times(old a)"
    have tt: "t\<in>T" using component_bounds(1)[OF a] t by blast
    show "((f t,input_value(moved a)(f t)),output_value(moved a)(f t))\<in>law_relation(moved a) \<longleftrightarrow>
      ((t,input_value(old a)t),output_value(old a)t)\<in>law_relation(old a)"
      using relation_forward[OF a tt, of "input_value(old a)t" "output_value(old a)t"] left_inverse[OF tt]
      by (simp add: component_transport_def)
  qed
  have times: "eval_times(moved a)=image f(eval_times(old a))" by (simp add: component_transport_def)
  show ?thesis using pointwise unfolding valid_times_def times by blast
qed
end
ML \<open>
val roots = @{thms carrier_bijection.image_as_inverse carrier_bijection.inverse_image
 law_transport.evaluation_tuple law_transport.condition1_component law_transport.condition2_component
 law_transport.generated_component law_transport.valid_times_image};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
