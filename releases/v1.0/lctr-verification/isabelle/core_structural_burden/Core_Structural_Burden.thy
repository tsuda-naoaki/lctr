theory Core_Structural_Burden
  imports Main
begin

definition burden where
  "burden R m F = {s. \<exists>a\<in>F. \<exists>b. R a b \<and> m b=s}"

lemma singleton_burden: "burden R m {a} = image m {b. R a b}"
  by (auto simp: burden_def)
lemma burden_mono: "F \<subseteq> G \<Longrightarrow> burden R m F \<subseteq> burden R m G"
  by (auto simp: burden_def)
lemma root_burden_subset: "a\<in>F \<Longrightarrow> burden R m {a} \<subseteq> burden R m F"
  by (rule burden_mono) auto
lemma burden_separation:
  assumes ha: "a\<in>F" and hn: "\<not> burden R m {a} \<subseteq> burden R m G"
  shows "burden R m F - burden R m G \<noteq> {}"
proof -
  obtain s where s: "s\<in>burden R m {a}" "s\<notin>burden R m G" using hn by blast
  have subset: "burden R m {a}\<subseteq>burden R m F" by (rule root_burden_subset[OF ha])
  have "s\<in>burden R m F" by (rule subsetD[OF subset s(1)])
  then show ?thesis using s(2) by blast
qed

lemma reach_map:
  assumes edges: "\<And>x y. R x y \<Longrightarrow> S (f x) (f y)" and h: "rtranclp R x y"
  shows "rtranclp S (f x) (f y)"
  using h
proof (induction rule: rtranclp_induct)
  case base then show ?case by simp
next
  case (step y z)
  then show ?case using edges by (meson rtranclp.rtrancl_into_rtrancl)
qed

lemma reach_transport:
  assumes bc: "bij c" and edges: "\<And>x y. R x y \<longleftrightarrow> S (c x) (c y)"
  shows "rtranclp R x y \<longleftrightarrow> rtranclp S (c x) (c y)"
proof
  assume h: "rtranclp R x y"
  show "rtranclp S (c x) (c y)"
    by (rule reach_map[where f=c and R=R and S=S, OF _ h]) (simp only: edges)
next
  assume h: "rtranclp S (c x) (c y)"
  have reverse_edges: "\<And>a b. S a b \<Longrightarrow> R (inv c a) (inv c b)"
    using edges bij_is_surj[OF bc] by (metis surj_f_inv_f)
  have "rtranclp R (inv c (c x)) (inv c (c y))"
    by (rule reach_map[where f="inv c" and R=S and S=R, OF reverse_edges h])
  then show "rtranclp R x y" by (simp add: inv_f_f bij_is_inj[OF bc])
qed

lemma burden_transport:
  assumes bc: "bij c" and bd: "bij d"
    and rel: "\<And>a b. R a b \<longleftrightarrow> Q (c a) (c b)"
    and targets: "\<And>a. d (m a)=n (c a)"
  shows "image d (burden R m F) = burden Q n (image c F)"
proof (rule set_eqI)
  fix t
  show "t\<in>image d (burden R m F) \<longleftrightarrow> t\<in>burden Q n (image c F)"
  proof
    assume "t\<in>image d (burden R m F)"
    then obtain a b where "a\<in>F" "R a b" "t=d (m b)" by (auto simp: burden_def)
    then show "t\<in>burden Q n (image c F)" using rel targets by (auto simp: burden_def)
  next
    assume "t\<in>burden Q n (image c F)"
    then obtain a cb where a: "a\<in>F" "Q (c a) cb" "n cb=t" by (auto simp: burden_def)
    obtain b where b: "cb=c b" using bij_is_surj[OF bc] unfolding surj_def by blast
    have rb: "R a b" using a(2) b rel[of a b] by simp
    have mb: "m b\<in>burden R m F" using a(1) rb unfolding burden_def by blast
    have im: "d (m b)\<in>image d (burden R m F)" by (rule imageI[OF mb])
    show "t\<in>image d (burden R m F)" using im a(3) b targets[of b] by simp
  qed
qed

definition count :: "nat \<Rightarrow> nat" where "count s = [8,3,8,9,5,5]!s"
typedef native_token = "{(s,i). s<6 \<and> 1\<le>i \<and> i\<le>count s}"
  morphisms rep_token abs_token
  by (rule exI[of _ "(0,1)"]) (simp add: count_def)
definition within :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "within s i j = (if s=0 then 1\<le>i \<and> i<8 \<and> j=i+1
    else if s=1 then (i,j)\<in>{(1,2),(2,3)}
    else if s=2 then (i,j)\<in>{(1,6),(6,7),(2,3),(3,8),(6,8)}
    else if s=3 then (1\<le>i \<and> i\<le>6 \<and> j=7) \<or> (i,j)\<in>{(7,8),(7,9)}
    else if s=4 then (i,j)\<in>{(1,3),(1,5),(3,5)}
    else if s=5 then (i,j)\<in>{(1,2),(2,3),(1,4),(1,5)} else False)"
definition edge :: "native_token \<Rightarrow> native_token \<Rightarrow> bool" where
  "edge a b = ((fst (rep_token a)=fst (rep_token b) \<and>
    within (fst (rep_token a)) (snd (rep_token a)) (snd (rep_token b))) \<or>
    (fst (rep_token a),fst (rep_token b))\<in>{(0,1),(1,2),(2,3),(2,4),(4,5)})"
datatype structural_token = StructTok native_token
datatype audit_status = Pass | Indeterminate | Unformed | Blocked | Fail
definition nativeBurden where "nativeBurden F = burden (rtranclp edge) StructTok F"
fun boundaryBurden where
  "boundaryBurden None = {}"
| "boundaryBurden (Some F) = nativeBurden F"
definition report where "report F B = (nativeBurden F, boundaryBurden B)"

lemma native_root_included: "a\<in>F \<Longrightarrow> StructTok a\<in>nativeBurden F"
  by (auto simp: nativeBurden_def burden_def)
lemma native_burden_upward:
  assumes ha: "StructTok a\<in>nativeBurden F" and hab: "rtranclp edge a b"
  shows "StructTok b\<in>nativeBurden F"
proof -
  obtain s where s: "s\<in>F" "rtranclp edge s a"
    using ha by (auto simp: nativeBurden_def burden_def)
  have "rtranclp edge s b" by (rule rtranclp_trans[OF s(2) hab])
  then show ?thesis using s(1) unfolding nativeBurden_def burden_def by blast
qed
lemma report_unique:
  "\<exists>!p. fst p=nativeBurden F \<and> snd p=boundaryBurden B"
  by (rule ex1I[of _ "report F B"]) (auto simp: report_def)
lemma native_burden_covariance:
  assumes bc: "bij c" and bd: "bij d"
    and edges: "\<And>a b. edge a b \<longleftrightarrow> edge (c a) (c b)"
    and targets: "\<And>a. d (StructTok a)=StructTok (c a)"
  shows "image d (nativeBurden F) = nativeBurden (image c F)"
proof -
  have reach: "\<And>a b. rtranclp edge a b \<longleftrightarrow> rtranclp edge (c a) (c b)"
    by (rule reach_transport[where c=c and R=edge and S=edge, OF bc edges])
  show ?thesis unfolding nativeBurden_def
    by (rule burden_transport[where c=c and d=d and R="rtranclp edge" and Q="rtranclp edge"
      and m=StructTok and n=StructTok,
      OF bc bd reach targets])
qed

lemma native_failed_burden_covariance:
  assumes bc: "bij c" and bd: "bij d"
    and edges: "\<And>a b. edge a b \<longleftrightarrow> edge (c a) (c b)"
    and targets: "\<And>a. d (StructTok a)=StructTok (c a)"
    and states: "\<And>a. t (c a)=s a"
  shows "image d (nativeBurden {a. s a=Fail}) = nativeBurden {b. t b=Fail}"
proof -
  have fibers: "image c {a. s a=Fail} = {b. t b=Fail}"
  proof (rule set_eqI)
    fix b
    obtain a where ba: "b=c a" using bij_is_surj[OF bc] unfolding surj_def by blast
    show "b\<in>image c {a. s a=Fail} \<longleftrightarrow> b\<in>{b. t b=Fail}"
    proof
      assume "b\<in>image c {a. s a=Fail}"
      then obtain a' where aa: "b=c a'" "s a'=Fail" by blast
      show "b\<in>{b. t b=Fail}" using aa states[of a'] by simp
    next
      assume "b\<in>{b. t b=Fail}"
      then have "s a=Fail" using ba states[of a] by simp
      then show "b\<in>image c {a. s a=Fail}" using ba by blast
    qed
  qed
  show ?thesis by (simp only: native_burden_covariance[OF bc bd edges targets] fibers)
qed

lemma boundary_burden_covariance:
  assumes bc: "bij c" and bd: "bij d"
    and edges: "\<And>a b. edge a b \<longleftrightarrow> edge (c a) (c b)"
    and targets: "\<And>a. d (StructTok a)=StructTok (c a)"
  shows "image d (boundaryBurden B) = boundaryBurden (map_option (\<lambda>F. image c F) B)"
  by (cases B) (simp_all add: native_burden_covariance[OF bc bd edges targets])

ML \<open>
val roots = @{thms singleton_burden burden_mono root_burden_subset burden_separation reach_map reach_transport burden_transport native_root_included native_burden_upward report_unique native_burden_covariance native_failed_burden_covariance boundary_burden_covariance};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
