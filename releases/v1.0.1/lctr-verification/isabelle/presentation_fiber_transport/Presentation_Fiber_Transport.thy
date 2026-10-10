theory Presentation_Fiber_Transport
  imports LCTR_Presentation_Fiber_Encoding.Presentation_Fiber_Encoding
    LCTR_Core_Preorder_Quotient.Core_Preorder_Quotient
begin

definition fiber_relation where
  "fiber_relation C q B r R =
    (\<lambda>(t,s). (fiber_encode C q t,fiber_encode B r s))`R"
definition fiber_order where
  "fiber_order C q L X Y = L (fiber_decode C q X) (fiber_decode C q Y)"

lemma fiber_decode_injective:
  "inj_on (fiber_decode C q) (fiber_carrier C q)"
proof (rule inj_onI)
  fix X Y assume X: "X\<in>fiber_carrier C q" and Y: "Y\<in>fiber_carrier C q"
    and eq: "fiber_decode C q X=fiber_decode C q Y"
  have "fiber_encode C q (fiber_decode C q X)=fiber_encode C q (fiber_decode C q Y)"
    by (simp only: eq)
  then show "X=Y" by (simp only: fiber_encode_decode[OF X] fiber_encode_decode[OF Y])
qed

lemma fiber_partial_order:
  assumes p: "part_on (q`C) L"
  shows "part_on (fiber_carrier C q) (fiber_order C q L)"
proof -
  have p_refl: "\<forall>x\<in>q`C. L x x"
    and p_trans: "\<forall>x\<in>q`C. \<forall>y\<in>q`C. \<forall>z\<in>q`C.
      L x y \<longrightarrow> L y z \<longrightarrow> L x z"
    and p_anti: "\<forall>x\<in>q`C. \<forall>y\<in>q`C. L x y \<longrightarrow> L y x \<longrightarrow> x=y"
    using p unfolding part_on_def pre_on_def by iprover+
  have refl: "\<forall>X\<in>fiber_carrier C q. fiber_order C q L X X"
  proof
    fix X assume X: "X\<in>fiber_carrier C q"
    have dx: "fiber_decode C q X\<in>q`C" by (rule fiber_decode_carrier[OF X])
    show "fiber_order C q L X X" unfolding fiber_order_def
      by (rule p_refl[rule_format, OF dx])
  qed
  have tr: "\<forall>X\<in>fiber_carrier C q. \<forall>Y\<in>fiber_carrier C q.
    \<forall>Z\<in>fiber_carrier C q.
    fiber_order C q L X Y \<longrightarrow> fiber_order C q L Y Z \<longrightarrow> fiber_order C q L X Z"
  proof (intro ballI impI)
    fix X Y Z assume X: "X\<in>fiber_carrier C q" and Y: "Y\<in>fiber_carrier C q"
      and Z: "Z\<in>fiber_carrier C q"
      and xy: "fiber_order C q L X Y" and yz: "fiber_order C q L Y Z"
    have dx: "fiber_decode C q X\<in>q`C" by (rule fiber_decode_carrier[OF X])
    have dy: "fiber_decode C q Y\<in>q`C" by (rule fiber_decode_carrier[OF Y])
    have dz: "fiber_decode C q Z\<in>q`C" by (rule fiber_decode_carrier[OF Z])
    show "fiber_order C q L X Z" unfolding fiber_order_def
      by (rule p_trans[rule_format, OF dx dy dz])
         (use xy yz in \<open>simp_all only: fiber_order_def\<close>)
  qed
  have anti: "\<forall>X\<in>fiber_carrier C q. \<forall>Y\<in>fiber_carrier C q.
    fiber_order C q L X Y \<longrightarrow> fiber_order C q L Y X \<longrightarrow> X=Y"
  proof (intro ballI impI)
    fix X Y assume X: "X\<in>fiber_carrier C q" and Y: "Y\<in>fiber_carrier C q"
      and xy: "fiber_order C q L X Y" and yx: "fiber_order C q L Y X"
    have dx: "fiber_decode C q X\<in>q`C" by (rule fiber_decode_carrier[OF X])
    have dy: "fiber_decode C q Y\<in>q`C" by (rule fiber_decode_carrier[OF Y])
    have eq: "fiber_decode C q X=fiber_decode C q Y"
      by (rule p_anti[rule_format, OF dx dy])
         (use xy yx in \<open>simp_all only: fiber_order_def\<close>)
    show "X=Y" by (rule inj_onD[OF fiber_decode_injective eq X Y])
  qed
  show ?thesis using refl tr anti unfolding part_on_def pre_on_def by iprover
qed

lemma fiber_relation_typed:
  assumes typed: "R\<subseteq>(q`C)\<times>(r`B)"
  shows "fiber_relation C q B r R \<subseteq> fiber_carrier C q \<times> fiber_carrier B r"
  using typed unfolding fiber_relation_def fiber_carrier_def by auto

lemma fiber_relation_roundtrip:
  assumes typed: "R\<subseteq>(q`C)\<times>(r`B)"
  shows "(\<lambda>(X,Y). (fiber_decode C q X,fiber_decode B r Y))`
    fiber_relation C q B r R = R"
proof -
  have eq: "\<And>p. p\<in>R \<Longrightarrow>
      (fiber_decode C q (fiber_encode C q (fst p)),
       fiber_decode B r (fiber_encode B r (snd p)))=p"
  proof -
    fix p assume "p\<in>R"
    then have t: "fst p\<in>q`C" and s: "snd p\<in>r`B" using typed by auto
    show "(fiber_decode C q (fiber_encode C q (fst p)),
       fiber_decode B r (fiber_encode B r (snd p)))=p"
      using fiber_decode_encode[OF t] fiber_decode_encode[OF s]
      by (cases p) auto
  qed
  have "(\<lambda>(X,Y). (fiber_decode C q X,fiber_decode B r Y))`
    fiber_relation C q B r R = id`R"
    unfolding fiber_relation_def image_image
    by (rule image_cong[OF refl]) (use eq in \<open>auto simp: case_prod_beta\<close>)
  then show ?thesis by simp
qed

lemma fiber_relation_equality_iff:
  assumes R: "R\<subseteq>(q`C)\<times>(r`B)" and S: "S\<subseteq>(q`C)\<times>(r`B)"
  shows "fiber_relation C q B r R = fiber_relation C q B r S \<longleftrightarrow> R=S"
proof
  assume e: "fiber_relation C q B r R = fiber_relation C q B r S"
  have "(\<lambda>(X,Y). (fiber_decode C q X,fiber_decode B r Y))`fiber_relation C q B r R =
        (\<lambda>(X,Y). (fiber_decode C q X,fiber_decode B r Y))`fiber_relation C q B r S"
    by (simp only: e)
  then show "R=S" by (simp only: fiber_relation_roundtrip[OF R] fiber_relation_roundtrip[OF S])
next
  assume "R=S" then show "fiber_relation C q B r R=fiber_relation C q B r S" by simp
qed

lemma fiber_relation_source_image:
  "fiber_relation C q B r ((\<lambda>(c,b). (q c,r b))`R) =
   (\<lambda>(c,b). (fiber_encode C q (q c),fiber_encode B r (r b)))`R"
  unfolding fiber_relation_def image_image by (simp add: case_prod_beta)

lemma fiber_order_source_iff:
  assumes c: "c\<in>C" and d: "d\<in>C"
  shows "fiber_order C q L (fiber_encode C q (q c)) (fiber_encode C q (q d)) \<longleftrightarrow> L (q c) (q d)"
proof -
  have qc: "q c\<in>q`C" and qd: "q d\<in>q`C" using c d by blast+
  show ?thesis unfolding fiber_order_def
    by (simp only: fiber_decode_encode[OF qc] fiber_decode_encode[OF qd])
qed

lemma fiber_maps_order_iff:
  assumes f: "f`(q`C)\<subseteq>r`C" and x: "x\<in>q`C" and y: "y\<in>q`C"
  shows "fiber_order C r M
    (fiber_map C q r f (fiber_encode C q x))
    (fiber_map C q r f (fiber_encode C q y))
    \<longleftrightarrow> M (f x) (f y)"
  unfolding fiber_order_def
  by (simp only: fiber_map_decodes[OF x f] fiber_map_decodes[OF y f])

ML \<open>
val roots = @{thms fiber_decode_injective fiber_partial_order fiber_relation_typed
  fiber_relation_roundtrip fiber_relation_equality_iff fiber_relation_source_image
  fiber_order_source_iff fiber_maps_order_iff};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
