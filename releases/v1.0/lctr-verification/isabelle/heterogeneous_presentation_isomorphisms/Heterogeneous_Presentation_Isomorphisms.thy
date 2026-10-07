theory Heterogeneous_Presentation_Isomorphisms
 imports LCTR_Presentation_Quotient_Universe.Presentation_Quotient_Universe
begin

definition presentation_iso where
 "presentation_iso C B q p L R r s M U f g h k \<longleftrightarrow>
  f`(q`C)=r`C \<and> g`(p`B)=s`B \<and>
  h`(r`C)=q`C \<and> k`(s`B)=p`B \<and>
  (\<forall>x\<in>q`C. h(f x)=x) \<and> (\<forall>x\<in>r`C. f(h x)=x) \<and>
  (\<forall>y\<in>p`B. k(g y)=y) \<and> (\<forall>y\<in>s`B. g(k y)=y) \<and>
  (\<forall>c\<in>C. f(q c)=r c) \<and> (\<forall>b\<in>B. g(p b)=s b) \<and>
  (\<forall>x\<in>q`C. \<forall>y\<in>q`C. M (f x) (f y) \<longleftrightarrow> L x y) \<and>
  (\<forall>x\<in>q`C. \<forall>y\<in>p`B. (f x,g y)\<in>U \<longleftrightarrow> (x,y)\<in>R)"

lemma source_commuting_inverse:
 assumes f: "\<forall>c\<in>C. f(q c)=r c" and h: "\<forall>c\<in>C. h(r c)=q c"
 shows "\<forall>x\<in>q`C. h(f x)=x"
 using f h by auto

lemma heterogeneous_mutual_inverse:
 assumes f: "presentation_arrow C B q p L R r s M U f g"
   and h: "presentation_arrow C B r s M U q p L R h k"
 shows "(\<forall>x\<in>q`C. h(f x)=x) \<and> (\<forall>x\<in>r`C. f(h x)=x) \<and>
        (\<forall>y\<in>p`B. k(g y)=y) \<and> (\<forall>y\<in>s`B. g(k y)=y)"
proof -
 have fc: "\<forall>c\<in>C. f(q c)=r c" and hc: "\<forall>c\<in>C. h(r c)=q c"
   and gb: "\<forall>b\<in>B. g(p b)=s b" and kb: "\<forall>b\<in>B. k(s b)=p b"
   using f h unfolding presentation_arrow_def by iprover+
 show ?thesis using source_commuting_inverse[OF fc hc] source_commuting_inverse[OF hc fc]
   source_commuting_inverse[OF gb kb] source_commuting_inverse[OF kb gb] by iprover
qed

lemma heterogeneous_mutual_structural_iso:
 assumes typed: "R\<subseteq>(q`C)\<times>(p`B)"
   and f: "presentation_arrow C B q p L R r s M U f g"
   and h: "presentation_arrow C B r s M U q p L R h k"
 shows "presentation_iso C B q p L R r s M U f g h k"
proof -
 note inv=heterogeneous_mutual_inverse[OF f h]
 have fi: "\<forall>x\<in>q`C. h(f x)=x" and gi: "\<forall>y\<in>p`B. k(g y)=y"
   using inv by iprover+
 have fo: "f`(q`C)=r`C" using f unfolding presentation_arrow_def by iprover
 have fm: "\<forall>x\<in>q`C. \<forall>y\<in>q`C. L x y \<longrightarrow> M(f x)(f y)"
   and hm: "\<forall>x\<in>r`C. \<forall>y\<in>r`C. M x y \<longrightarrow> L(h x)(h y)"
   using f h unfolding presentation_arrow_def by iprover+
 have order: "\<forall>x\<in>q`C. \<forall>y\<in>q`C. M(f x)(f y) \<longleftrightarrow> L x y"
 proof (intro ballI)
   fix x y assume x: "x\<in>q`C" and y: "y\<in>q`C"
   have fx: "f x\<in>r`C" and fy: "f y\<in>r`C" using fo x y by blast+
   have ix: "h(f x)=x" and iy: "h(f y)=y"
     using fi x y by blast+
   show "M(f x)(f y) \<longleftrightarrow> L x y"
     using fm[rule_format,OF x y] hm[rule_format,OF fx fy] ix iy by auto
 qed
 have image: "U=(\<lambda>(x,y). (f x,g y))`R"
   using f unfolding presentation_arrow_def by iprover
 have trajectory: "\<forall>x\<in>q`C. \<forall>y\<in>p`B. (f x,g y)\<in>U \<longleftrightarrow> (x,y)\<in>R"
 proof (intro ballI)
   fix x y assume x: "x\<in>q`C" and y: "y\<in>p`B"
   show "(f x,g y)\<in>U \<longleftrightarrow> (x,y)\<in>R"
   proof
     assume "(f x,g y)\<in>U"
     then obtain a b where ab: "(a,b)\<in>R" "f a=f x" "g b=g y"
       unfolding image by auto
     have a: "a\<in>q`C" and b: "b\<in>p`B" using typed ab(1) by auto
     have ax: "a=x" using fi[rule_format,OF a] fi[rule_format,OF x] ab(2) by metis
     have byeq: "b=y" using gi[rule_format,OF b] gi[rule_format,OF y] ab(3) by metis
     show "(x,y)\<in>R" using ab(1) ax byeq by simp
   next
     assume "(x,y)\<in>R" then show "(f x,g y)\<in>U" unfolding image by force
   qed
 qed
 show ?thesis using inv order trajectory f h
   unfolding presentation_iso_def presentation_arrow_def by iprover
qed

lemma heterogeneous_iso_forward:
 fixes q :: "'c\<Rightarrow>'t" and p :: "'b\<Rightarrow>'s"
   and r :: "'c\<Rightarrow>'u" and s :: "'b\<Rightarrow>'v"
 assumes rt: "R\<subseteq>(q`C)\<times>(p`B)" and ut: "U\<subseteq>(r`C)\<times>(s`B)"
   and e: "presentation_iso C B q p L R r s M U f g h k"
 shows "presentation_arrow C B q p L R r s M U f g"
proof -
 have traj: "\<forall>x\<in>q`C. \<forall>y\<in>p`B. (f x,g y)\<in>U \<longleftrightarrow> (x,y)\<in>R"
   and fo: "f`(q`C)=r`C" and go: "g`(p`B)=s`B"
   using e unfolding presentation_iso_def by iprover+
 have image: "U=(\<lambda>(x,y). (f x,g y))`R"
 proof (rule set_eqI)
   fix z :: "'u\<times>'v"
   obtain t v where z: "z=(t,v)" by (cases z) auto
   show "z\<in>U \<longleftrightarrow> z\<in>(\<lambda>(x,y). (f x,g y))`R"
   proof
     assume uz: "z\<in>U"
     have t: "t\<in>r`C" and v: "v\<in>s`B" using ut uz z by auto
     have tin: "t\<in>f`(q`C)" using t by (simp only: fo)
     have vin: "v\<in>g`(p`B)" using v by (simp only: go)
     obtain x where x: "x\<in>q`C" "f x=t" using tin by auto
     obtain y where y: "y\<in>p`B" "g y=v" using vin by auto
     have xy: "(x,y)\<in>R" using traj[rule_format,OF x(1) y(1)] uz z x(2) y(2) by simp
     show "z\<in>(\<lambda>(x,y). (f x,g y))`R" using xy z x(2) y(2) by force
   next
     assume "z\<in>(\<lambda>(x,y). (f x,g y))`R"
     then obtain x y where xy: "(x,y)\<in>R" "z=(f x,g y)" by auto
     have x: "x\<in>q`C" and y: "y\<in>p`B" using rt xy(1) by auto
     show "z\<in>U" using traj[rule_format,OF x y] xy by simp
   qed
 qed
 have order: "\<forall>x\<in>q`C. \<forall>y\<in>q`C. M(f x)(f y)\<longleftrightarrow>L x y"
   using e unfolding presentation_iso_def by iprover
 have mono: "\<forall>x\<in>q`C. \<forall>y\<in>q`C. L x y \<longrightarrow> M(f x)(f y)"
 proof (intro ballI impI)
   fix x y assume x: "x\<in>q`C" and y: "y\<in>q`C" and xy: "L x y"
   show "M(f x)(f y)" by (rule order[rule_format,OF x y, THEN iffD2, OF xy])
 qed
 show ?thesis using e image mono unfolding presentation_iso_def presentation_arrow_def by iprover
qed

lemma heterogeneous_iso_symmetric:
 assumes e: "presentation_iso C B q p L R r s M U f g h k"
 shows "presentation_iso C B r s M U q p L R h k f g"
proof -
 have hi: "\<forall>x\<in>r`C. f(h x)=x" and ki: "\<forall>y\<in>s`B. g(k y)=y"
   and ho: "h`(r`C)=q`C" and ko: "k`(s`B)=p`B"
   and order: "\<forall>x\<in>q`C. \<forall>y\<in>q`C. M(f x)(f y)\<longleftrightarrow>L x y"
   and traj: "\<forall>x\<in>q`C. \<forall>y\<in>p`B. (f x,g y)\<in>U\<longleftrightarrow>(x,y)\<in>R"
   using e unfolding presentation_iso_def by iprover+
 have cc: "\<forall>c\<in>C. h(r c)=q c"
   and cb: "\<forall>b\<in>B. k(s b)=p b"
   using e unfolding presentation_iso_def by auto
 have om: "\<forall>x\<in>r`C. \<forall>y\<in>r`C. L(h x)(h y)\<longleftrightarrow>M x y"
 proof (intro ballI)
   fix x y assume x: "x\<in>r`C" and y: "y\<in>r`C"
   have hx: "h x\<in>q`C" and hy: "h y\<in>q`C" using ho x y by blast+
   show "L(h x)(h y)\<longleftrightarrow>M x y"
     using order[rule_format,OF hx hy] hi[rule_format,OF x] hi[rule_format,OF y] by simp
 qed
 have tm: "\<forall>x\<in>r`C. \<forall>y\<in>s`B. (h x,k y)\<in>R\<longleftrightarrow>(x,y)\<in>U"
 proof (intro ballI)
   fix x y assume x: "x\<in>r`C" and y: "y\<in>s`B"
   have hx: "h x\<in>q`C" and ky: "k y\<in>p`B" using ho ko x y by blast+
   show "(h x,k y)\<in>R\<longleftrightarrow>(x,y)\<in>U"
     using traj[rule_format,OF hx ky] hi[rule_format,OF x] ki[rule_format,OF y] by simp
 qed
 show ?thesis using e cc cb om tm unfolding presentation_iso_def by iprover
qed

lemma heterogeneous_mutual_iff_iso:
 assumes rt: "R\<subseteq>(q`C)\<times>(p`B)" and ut: "U\<subseteq>(r`C)\<times>(s`B)"
 shows "((\<exists>f g. presentation_arrow C B q p L R r s M U f g) \<and>
         (\<exists>h k. presentation_arrow C B r s M U q p L R h k)) \<longleftrightarrow>
        (\<exists>f g h k. presentation_iso C B q p L R r s M U f g h k)"
proof
 assume a: "(\<exists>f g. presentation_arrow C B q p L R r s M U f g) \<and>
         (\<exists>h k. presentation_arrow C B r s M U q p L R h k)"
 then obtain f g h k where f: "presentation_arrow C B q p L R r s M U f g"
   and h: "presentation_arrow C B r s M U q p L R h k" by blast
 show "\<exists>f g h k. presentation_iso C B q p L R r s M U f g h k"
   using heterogeneous_mutual_structural_iso[OF rt f h] by blast
next
 assume "\<exists>f g h k. presentation_iso C B q p L R r s M U f g h k"
 then obtain f g h k where e: "presentation_iso C B q p L R r s M U f g h k" by blast
 have f: "presentation_arrow C B q p L R r s M U f g"
   by (rule heterogeneous_iso_forward[OF rt ut e])
 have h: "presentation_arrow C B r s M U q p L R h k"
   by (rule heterogeneous_iso_forward[OF ut rt heterogeneous_iso_symmetric[OF e]])
 show "(\<exists>f g. presentation_arrow C B q p L R r s M U f g) \<and>
       (\<exists>h k. presentation_arrow C B r s M U q p L R h k)" using f h by blast
qed

ML \<open>
val roots = @{thms source_commuting_inverse heterogeneous_mutual_inverse
 heterogeneous_mutual_structural_iso heterogeneous_iso_forward
 heterogeneous_iso_symmetric heterogeneous_mutual_iff_iso};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
