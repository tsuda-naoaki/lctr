theory Full_Carrier_Component_Transport
  imports "LCTR_Core_Law_Transport.Core_Law_Transport"
begin

lemma carrier_bijection_product:
  assumes f: "carrier_bijection A B f g" and h: "carrier_bijection C D h k"
  shows "carrier_bijection (A\<times>C) (B\<times>D) (map_prod f h) (map_prod g k)"
  using f h unfolding carrier_bijection_def by auto

context carrier_bijection
begin
lemma image_membership_at_source:
  assumes S: "S\<subseteq>T" and x: "x\<in>T"
  shows "f x\<in>f ` S \<longleftrightarrow> x\<in>S"
proof
  assume h: "f x\<in>f ` S"
  then obtain y where y: "y\<in>S" "f x=f y" by (auto simp only: image_iff)
  have yt: "y\<in>T" using S y by blast
  have "x=y" using arg_cong[OF y(2), of g] left_inverse[OF x] left_inverse[OF yt] by simp
  then show "x\<in>S" using y by simp
next
  assume "x\<in>S" then show "f x\<in>f ` S" by blast
qed
end

definition full_component_transport where
  "full_component_transport ft gt fx fy c =
    \<lparr>eval_times=ft ` eval_times c,
     input_value=fx \<circ> input_value c \<circ> gt,
     output_value=fy \<circ> output_value c \<circ> gt,
     eval_domain=map_prod ft fx ` eval_domain c,
     law_relation=map_prod (map_prod ft fx) fy ` law_relation c\<rparr>"

locale full_component_encoding =
  tm: carrier_bijection T U ft gt +
  ix: carrier_bijection X V fx gx +
  oy: carrier_bijection Y W fy gy
  for T :: "'t set" and U :: "'u set" and ft :: "'t\<Rightarrow>'u" and gt :: "'u\<Rightarrow>'t"
    and X :: "'x set" and V :: "'v set" and fx :: "'x\<Rightarrow>'v" and gx :: "'v\<Rightarrow>'x"
    and Y :: "'y set" and W :: "'w set" and fy :: "'y\<Rightarrow>'w" and gy :: "'w\<Rightarrow>'y" +
  fixes c :: "('t,'x,'y) law_component"
  assumes times_typed: "eval_times c\<subseteq>T"
    and inputs_typed: "input_value c ` eval_times c\<subseteq>X"
    and outputs_typed: "output_value c ` eval_times c\<subseteq>Y"
    and domain_typed: "eval_domain c\<subseteq>T\<times>X"
    and relation_typed: "law_relation c\<subseteq>eval_domain c\<times>Y"
begin

abbreviation moved where "moved \<equiv> full_component_transport ft gt fx fy c"
abbreviation pair_map where "pair_map \<equiv> map_prod ft fx"
abbreviation tuple_map where "tuple_map \<equiv> map_prod pair_map fy"

sublocale pair: carrier_bijection "T\<times>X" "U\<times>V" pair_map "map_prod gt gx"
  by (rule carrier_bijection_product[OF tm.carrier_bijection_axioms ix.carrier_bijection_axioms])
sublocale tup: carrier_bijection "(T\<times>X)\<times>Y" "(U\<times>V)\<times>W"
  tuple_map "map_prod (map_prod gt gx) gy"
  by (rule carrier_bijection_product[OF pair.carrier_bijection_axioms oy.carrier_bijection_axioms])

lemma relation_carrier: "law_relation c\<subseteq>(T\<times>X)\<times>Y"
  using domain_typed relation_typed by auto

lemma moved_bounds:
  "eval_times moved\<subseteq>U"
  "input_value moved ` eval_times moved\<subseteq>V"
  "output_value moved ` eval_times moved\<subseteq>W"
  "eval_domain moved\<subseteq>U\<times>V"
  "law_relation moved\<subseteq>eval_domain moved\<times>W"
proof -
  have li: "\<And>t. t\<in>eval_times c \<Longrightarrow> gt(ft t)=t"
    using times_typed tm.left_inverse by blast
  have iv: "\<And>t. t\<in>eval_times c \<Longrightarrow> fx(input_value c t)\<in>V"
    using inputs_typed ix.forward_typed by blast
  have ov: "\<And>t. t\<in>eval_times c \<Longrightarrow> fy(output_value c t)\<in>W"
    using outputs_typed oy.forward_typed by blast
  show "eval_times moved\<subseteq>U"
    using times_typed tm.forward_typed by (auto simp: full_component_transport_def; blast)
  show "input_value moved ` eval_times moved\<subseteq>V"
    using iv li by (auto simp: full_component_transport_def)
  show "output_value moved ` eval_times moved\<subseteq>W"
    using ov li by (auto simp: full_component_transport_def)
  show "eval_domain moved\<subseteq>U\<times>V"
    using domain_typed pair.forward_typed by (auto simp: full_component_transport_def; blast)
  show "law_relation moved\<subseteq>eval_domain moved\<times>W"
    using relation_typed oy.forward_typed by (auto simp: full_component_transport_def; blast)
qed

lemma domain_membership:
  assumes "t\<in>T" "x\<in>X"
  shows "(ft t,fx x)\<in>eval_domain moved \<longleftrightarrow> (t,x)\<in>eval_domain c"
  using pair.image_membership_at_source[OF domain_typed, of "(t,x)"] assms
  by (simp add: full_component_transport_def)

lemma relation_membership:
  assumes "t\<in>T" "x\<in>X" "y\<in>Y"
  shows "((ft t,fx x),fy y)\<in>law_relation moved \<longleftrightarrow> ((t,x),y)\<in>law_relation c"
  using tup.image_membership_at_source[OF relation_carrier, of "((t,x),y)"] assms
  by (simp add: full_component_transport_def)

lemma evaluation_values:
  assumes t: "t\<in>eval_times c"
  shows "input_value moved (ft t)=fx(input_value c t)"
    and "output_value moved (ft t)=fy(output_value c t)"
  using tm.left_inverse times_typed t by (auto simp: full_component_transport_def)

lemma evaluation_domain:
  assumes t: "t\<in>eval_times c"
  shows "(ft t,input_value moved(ft t))\<in>eval_domain moved \<longleftrightarrow>
    (t,input_value c t)\<in>eval_domain c"
proof -
  have tt: "t\<in>T" using times_typed t by blast
  have xx: "input_value c t\<in>X" using inputs_typed t by blast
  show ?thesis by (simp only: evaluation_values(1)[OF t] domain_membership[OF tt xx])
qed

lemma evaluation_relation:
  assumes t: "t\<in>eval_times c"
  shows "((ft t,input_value moved(ft t)),output_value moved(ft t))\<in>law_relation moved
    \<longleftrightarrow> ((t,input_value c t),output_value c t)\<in>law_relation c"
proof -
  have tt: "t\<in>T" using times_typed t by blast
  have xx: "input_value c t\<in>X" using inputs_typed t by blast
  have yy: "output_value c t\<in>Y" using outputs_typed t by blast
  show ?thesis by (simp only: evaluation_values[OF t] relation_membership[OF tt xx yy])
qed

lemma individual_admissibility:
  "individual_admissible moved \<longleftrightarrow> individual_admissible c"
proof -
  have times: "eval_times moved=ft ` eval_times c" by (simp add: full_component_transport_def)
  show ?thesis by (simp add: individual_admissible_def times evaluation_domain)
qed

lemma right_uniqueness:
  "right_unique moved \<longleftrightarrow> right_unique c"
proof
  assume h: "right_unique moved"
  show "right_unique c" unfolding right_unique_def
  proof (intro allI impI)
    fix t x y z
    assume a: "((t,x),y)\<in>law_relation c" and b: "((t,x),z)\<in>law_relation c"
    have yy: "y\<in>Y" and zz: "z\<in>Y" using relation_carrier a b by auto
    have ma: "((ft t,fx x),fy y)\<in>law_relation moved"
      using imageI[OF a, of tuple_map] by (simp add: full_component_transport_def)
    have mb: "((ft t,fx x),fy z)\<in>law_relation moved"
      using imageI[OF b, of tuple_map] by (simp add: full_component_transport_def)
    have eq: "fy y=fy z" using h ma mb unfolding right_unique_def by blast
    show "y=z" by (rule inj_onD[OF oy.injective eq yy zz])
  qed
next
  assume h: "right_unique c"
  show "right_unique moved" unfolding right_unique_def
  proof (intro allI impI)
    fix u v w z
    assume a: "((u,v),w)\<in>law_relation moved" and b: "((u,v),z)\<in>law_relation moved"
    obtain t x y where aa: "((t,x),y)\<in>law_relation c" "u=ft t" "v=fx x" "w=fy y"
      using a by (auto simp: full_component_transport_def)
    obtain s q r where bb: "((s,q),r)\<in>law_relation c" "u=ft s" "v=fx q" "z=fy r"
      using b by (auto simp: full_component_transport_def)
    have tt: "t\<in>T" "s\<in>T" and xx: "x\<in>X" "q\<in>X"
      using relation_carrier aa(1) bb(1) by auto
    have ts: "t=s" using inj_onD[OF tm.injective _ tt(1) tt(2)] aa(2) bb(2) by simp
    have xq: "x=q" using inj_onD[OF ix.injective _ xx(1) xx(2)] aa(3) bb(3) by simp
    have yr: "y=r" using h aa(1) bb(1) ts xq unfolding right_unique_def by blast
    show "w=z" using aa(4) bb(4) yr by simp
  qed
qed

lemma generated_membership:
  "generated_member moved \<longleftrightarrow> generated_member c"
proof -
  have times: "eval_times moved=ft ` eval_times c" by (simp add: full_component_transport_def)
  show ?thesis using evaluation_relation unfolding generated_member_def times by blast
qed

lemma valid_times_image:
  "valid_times moved=ft ` valid_times c"
proof -
  have times: "eval_times moved=ft ` eval_times c" by (simp add: full_component_transport_def)
  show ?thesis using evaluation_relation unfolding valid_times_def times by blast
qed

lemma reindex_transport:
  assumes p: "reindex_on ((T\<times>X)\<times>Y) p"
  shows "reindex_on ((U\<times>V)\<times>W)
    (conjugate_reindex tuple_map (map_prod (map_prod gt gx) gy) p)"
  by (rule tup.conjugate_typed[OF p])

lemma invariant_transport:
  assumes p: "reindex_on ((T\<times>X)\<times>Y) p"
  shows "image_invariant moved
      (conjugate_reindex tuple_map (map_prod (map_prod gt gx) gy) p)
    \<longleftrightarrow> image_invariant c p"
  using tup.conjugate_invariance[OF p relation_carrier]
  by (simp only: image_invariant_def full_component_transport_def law_component.select_convs)

end

ML \<open>
val roots = @{thms carrier_bijection_product carrier_bijection.image_membership_at_source
 full_component_encoding.moved_bounds full_component_encoding.domain_membership
 full_component_encoding.relation_membership full_component_encoding.evaluation_values
 full_component_encoding.individual_admissibility full_component_encoding.right_uniqueness
 full_component_encoding.generated_membership full_component_encoding.valid_times_image
 full_component_encoding.reindex_transport full_component_encoding.invariant_transport};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
