theory Heterogeneous_Presentation_Arrows
  imports LCTR_Presentation_Fiber_Admissibility.Presentation_Fiber_Admissibility
begin

definition presentation_arrow where
 "presentation_arrow C B q p L R r s M U f g \<longleftrightarrow>
  f`(q`C)=r`C \<and> g`(p`B)=s`B \<and>
  (\<forall>c\<in>C. f(q c)=r c) \<and> (\<forall>b\<in>B. g(p b)=s b) \<and>
  (\<forall>x\<in>q`C. \<forall>y\<in>q`C. L x y \<longrightarrow> M (f x) (f y)) \<and>
  U=(\<lambda>(x,y). (f x,g y))`R"

lemma presentation_arrow_identity:
 "presentation_arrow C B q p L R q p L R id id"
 unfolding presentation_arrow_def by simp

lemma presentation_arrow_composition:
 assumes a: "presentation_arrow C B q p L R r s M U f g"
     and b: "presentation_arrow C B r s M U v w N V h k"
 shows "presentation_arrow C B q p L R v w N V (h\<circ>f) (k\<circ>g)"
proof -
 have fo: "f`(q`C)=r`C" "g`(p`B)=s`B"
   and ho: "h`(r`C)=v`C" "k`(s`B)=w`B"
   using a b unfolding presentation_arrow_def by iprover+
 have co: "\<forall>c\<in>C. (h\<circ>f)(q c)=v c"
   and bo: "\<forall>b\<in>B. (k\<circ>g)(p b)=w b"
   using a b unfolding presentation_arrow_def by auto
 have mo: "\<forall>x\<in>q`C. \<forall>y\<in>q`C. L x y \<longrightarrow> N ((h\<circ>f)x) ((h\<circ>f)y)"
 proof (intro ballI impI)
   fix x y assume x: "x\<in>q`C" and y: "y\<in>q`C" and xy: "L x y"
   have fx: "f x\<in>r`C" and fy: "f y\<in>r`C" using fo x y by blast+
   have fm: "M (f x) (f y)" using a x y xy unfolding presentation_arrow_def by blast
   have hm: "N (h(f x)) (h(f y))" using b fx fy fm unfolding presentation_arrow_def by blast
   show "N ((h\<circ>f)x) ((h\<circ>f)y)" using hm by simp
 qed
 have ru: "U=(\<lambda>(x,y). (f x,g y))`R"
   and uv: "V=(\<lambda>(x,y). (h x,k y))`U"
   using a b unfolding presentation_arrow_def by iprover+
 have rv: "V=(\<lambda>(x,y). ((h\<circ>f)x,(k\<circ>g)y))`R"
   by (simp only: uv ru image_image) (simp add: case_prod_beta)
 have to: "(h\<circ>f)`(q`C)=v`C" and so: "(k\<circ>g)`(p`B)=w`B"
   by (simp only: image_comp[symmetric] fo ho)+
 show ?thesis unfolding presentation_arrow_def using to so co bo mo rv by iprover
qed

lemma encoded_projection_image:
 "(fiber_encode C q \<circ> q)`C = fiber_carrier C q"
 unfolding fiber_carrier_def by (simp only: image_comp)

lemma presentation_encode_arrow:
 "presentation_arrow C B q p L R
   (fiber_encode C q\<circ>q) (fiber_encode B p\<circ>p)
   (fiber_order C q L) (fiber_relation C q B p R)
   (fiber_encode C q) (fiber_encode B p)"
proof -
 have mo: "\<forall>x\<in>q`C. \<forall>y\<in>q`C.
   L x y \<longrightarrow> fiber_order C q L (fiber_encode C q x) (fiber_encode C q y)"
   unfolding fiber_order_def by (simp add: fiber_decode_encode)
 show ?thesis unfolding presentation_arrow_def fiber_relation_def
   using mo by (simp add: image_comp)
qed

lemma presentation_decode_arrow:
 assumes typed: "R\<subseteq>(q`C)\<times>(p`B)"
 shows "presentation_arrow C B
   (fiber_encode C q\<circ>q) (fiber_encode B p\<circ>p)
   (fiber_order C q L) (fiber_relation C q B p R)
   q p L R (fiber_decode C q) (fiber_decode B p)"
proof -
 have to: "fiber_decode C q`((fiber_encode C q\<circ>q)`C)=q`C"
   and so: "fiber_decode B p`((fiber_encode B p\<circ>p)`B)=p`B"
   by (simp only: encoded_projection_image fiber_decode_image)+
 have co: "\<forall>c\<in>C. fiber_decode C q ((fiber_encode C q\<circ>q)c)=q c"
   and bo: "\<forall>b\<in>B. fiber_decode B p ((fiber_encode B p\<circ>p)b)=p b"
   by (simp add: fiber_decode_encode)+
 have mo: "\<forall>x\<in>(fiber_encode C q\<circ>q)`C.
   \<forall>y\<in>(fiber_encode C q\<circ>q)`C.
   fiber_order C q L x y \<longrightarrow> L (fiber_decode C q x) (fiber_decode C q y)"
   by (simp add: fiber_order_def)
 have tr: "R=(\<lambda>(X,Y). (fiber_decode C q X,fiber_decode B p Y))`fiber_relation C q B p R"
   by (rule fiber_relation_roundtrip[OF typed, symmetric])
 show ?thesis unfolding presentation_arrow_def using to so co bo mo tr by iprover
qed

lemma heterogeneous_arrow_encoding_iff:
 assumes R: "R\<subseteq>(q`C)\<times>(p`B)" and U: "U\<subseteq>(r`C)\<times>(s`B)"
 shows "(\<exists>f g. presentation_arrow C B q p L R r s M U f g) \<longleftrightarrow>
   (\<exists>F G. presentation_arrow C B
     (fiber_encode C q\<circ>q) (fiber_encode B p\<circ>p)
     (fiber_order C q L) (fiber_relation C q B p R)
     (fiber_encode C r\<circ>r) (fiber_encode B s\<circ>s)
     (fiber_order C r M) (fiber_relation C r B s U) F G)"
proof
 assume "\<exists>f g. presentation_arrow C B q p L R r s M U f g"
 then obtain f g where a: "presentation_arrow C B q p L R r s M U f g" by blast
 have d: "presentation_arrow C B
     (fiber_encode C q\<circ>q) (fiber_encode B p\<circ>p)
     (fiber_order C q L) (fiber_relation C q B p R)
     q p L R (fiber_decode C q) (fiber_decode B p)"
   by (rule presentation_decode_arrow[OF R])
 note da = presentation_arrow_composition[OF d a]
 note out = presentation_arrow_composition[OF da presentation_encode_arrow]
 show "\<exists>F G. presentation_arrow C B
     (fiber_encode C q\<circ>q) (fiber_encode B p\<circ>p)
     (fiber_order C q L) (fiber_relation C q B p R)
     (fiber_encode C r\<circ>r) (fiber_encode B s\<circ>s)
     (fiber_order C r M) (fiber_relation C r B s U) F G"
   using out by blast
next
 assume "\<exists>F G. presentation_arrow C B
     (fiber_encode C q\<circ>q) (fiber_encode B p\<circ>p)
     (fiber_order C q L) (fiber_relation C q B p R)
     (fiber_encode C r\<circ>r) (fiber_encode B s\<circ>s)
     (fiber_order C r M) (fiber_relation C r B s U) F G"
 then obtain F G where a: "presentation_arrow C B
     (fiber_encode C q\<circ>q) (fiber_encode B p\<circ>p)
     (fiber_order C q L) (fiber_relation C q B p R)
     (fiber_encode C r\<circ>r) (fiber_encode B s\<circ>s)
     (fiber_order C r M) (fiber_relation C r B s U) F G" by blast
 note ea = presentation_arrow_composition[OF presentation_encode_arrow a]
 note out = presentation_arrow_composition[OF ea presentation_decode_arrow[OF U]]
 show "\<exists>f g. presentation_arrow C B q p L R r s M U f g" using out by blast
qed

context presentations
begin
lemma family_arrow_is_heterogeneous:
 "arrow i j f g \<longleftrightarrow>
  presentation_arrow C B (qc i) (qb i) (le i) (trj i)
    (qc j) (qb j) (le j) (trj j) f g"
 unfolding arrow_def presentation_arrow_def ontoC ontoB by simp
end

ML \<open>
val roots = @{thms presentation_arrow_identity presentation_arrow_composition
 encoded_projection_image presentation_encode_arrow presentation_decode_arrow
 heterogeneous_arrow_encoding_iff presentations.family_arrow_is_heterogeneous};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
