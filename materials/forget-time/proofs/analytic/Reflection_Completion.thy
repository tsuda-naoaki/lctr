theory Reflection_Completion
  imports Circle_Measure Thermal_Smoothness
begin

definition reflection_unfold :: "real \<Rightarrow> real\<times>real \<Rightarrow> real\<times>real" where
  "reflection_unfold L x=(abs(snd x),if 0<snd x then fst x+L else 3*L-fst x)"

definition reflection_fold :: "real \<Rightarrow> real\<times>real \<Rightarrow> real\<times>real" where
  "reflection_fold L z=(if snd z<2*L then (snd z-L,fst z) else (3*L-snd z,-fst z))"

definition reflection_motion :: "real \<Rightarrow> real \<Rightarrow> real\<times>real \<Rightarrow> real\<times>real" where
  "reflection_motion L u x=reflection_fold L
    (fst(reflection_unfold L x),circle_motion (4*L) (2*fst(reflection_unfold L x)) u (snd(reflection_unfold L x)))"

lemma reflection_fold_unfold:
  assumes "-L<q" "q<L" "p\<noteq>0"
  shows "reflection_fold L (reflection_unfold L (q,p))=(q,p)"
  using assms unfolding reflection_fold_def reflection_unfold_def
  by (auto simp: abs_if; linarith)

lemma reflection_unfold_fold:
  assumes "0<s" "0<y" "y<4*L" "y\<noteq>2*L"
  shows "reflection_unfold L (reflection_fold L (s,y))=(s,y)"
  using assms unfolding reflection_fold_def reflection_unfold_def
  by (auto simp: abs_if; linarith)

lemma reflection_local_agreement:
  assumes L: "0<L" and q: "-L<q" "q<L" and p: "p\<noteq>0"
    and y: "-L<q+2*p*u" "q+2*p*u<L"
  shows "reflection_motion L u (q,p)=(q+2*p*u,p)"
proof (cases "0<p")
  case True
  have wrap: "wrap (4*L) (q+L+2*p*u)=q+L+2*p*u"
    by (rule wrap_identity) (use L y in linarith)+
  show ?thesis using True L y
    by (simp add: reflection_motion_def reflection_unfold_def reflection_fold_def circle_motion_def abs_of_pos wrap; linarith)
next
  case False
  have neg: "p<0" using False p by linarith
  have wrap: "wrap (4*L) (3*L-q+2*(-p)*u)=3*L-q+2*(-p)*u"
    by (rule wrap_identity) (use L y in \<open>simp add: algebra_simps; linarith\<close>)+
  have np: "\<not>0<p" using neg by simp
  show ?thesis
    by (simp only: reflection_motion_def reflection_unfold_def reflection_fold_def
      circle_motion_def fst_conv snd_conv np if_False abs_of_neg[OF neg] wrap)
      (use y in \<open>auto simp: algebra_simps; linarith\<close>)
qed

lemma reflection_first_crossing:
  assumes "0<L" "0<p" "L<q+2*p*u" "q+2*p*u<3*L"
  shows "reflection_motion L u (q,p)=(2*L-(q+2*p*u),-p)"
proof -
  have wrap: "wrap (4*L) (q+L+2*p*u)=q+L+2*p*u"
    by (rule wrap_identity) (use assms in linarith)+
  show ?thesis using assms
    by (simp add: reflection_motion_def reflection_unfold_def reflection_fold_def circle_motion_def abs_of_pos wrap; linarith)
qed

lemma reflection_maps_measurable[measurable]:
  "reflection_unfold L\<in>measurable (lborel\<Otimes>\<^sub>M lborel) (lborel\<Otimes>\<^sub>M lborel)"
  "reflection_fold L\<in>measurable (lborel\<Otimes>\<^sub>M lborel) (lborel\<Otimes>\<^sub>M lborel)"
  "reflection_motion L u\<in>measurable (lborel\<Otimes>\<^sub>M lborel) (lborel\<Otimes>\<^sub>M lborel)"
  unfolding reflection_unfold_def reflection_fold_def reflection_motion_def circle_motion_def wrap_def frac_def
  by (measurable, measurable, measurable)

end
