theory Endpoint_Completions
  imports Complex_Main
begin

definition wrap :: "real \<Rightarrow> real \<Rightarrow> real" where
  "wrap w x = w*frac(x/w)"

lemma wrap_range:
  assumes "0<w"
  shows "0\<le>wrap w x" "wrap w x<w"
  unfolding wrap_def
  using assms frac_ge_0[of "x/w"] frac_lt_1[of "x/w"]
    mult_nonneg_nonneg mult_strict_left_mono by fastforce+

lemma wrap_identity:
  assumes "0<w" "0\<le>x" "x<w"
  shows "wrap w x=x"
proof -
  have "0\<le>x/w" "x/w<1" using assms by (simp_all add: divide_nonneg_pos divide_less_eq)
  then have "frac(x/w)=x/w" by (simp add: frac_eq)
  then show ?thesis using assms(1) by (simp add: wrap_def)
qed

lemma wrap_add_wrap:
  assumes "w\<noteq>0"
  shows "wrap w (wrap w x+y) = wrap w (x+y)"
  using assms by (simp add: wrap_def add_divide_distrib)

lemma wrap_one_lap:
  assumes w: "0<w" and x: "w\<le>x" "x<2*w"
  shows "wrap w x=x-w"
proof -
  have bd: "0\<le>(x-w)/w" "(x-w)/w<1"
    using w x by (simp_all add: divide_nonneg_pos divide_less_eq)
  have eq: "x/w=(x-w)/w+1" using w by (simp add: field_simps)
  have "frac(x/w)=(x-w)/w" by (simp only: eq frac_1_eq) (use bd in \<open>simp add: frac_eq\<close>)
  then show ?thesis using w by (simp add: wrap_def)
qed

lemma wrap_shift:
  assumes "w\<noteq>0"
  shows "wrap w (x+y)=wrap w (x+wrap w y)"
  using wrap_add_wrap[OF assms, of y x] by (simp add: add.commute)

definition circle_motion :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "circle_motion w v u x = wrap w (x+v*u)"

theorem circle_motion_group:
  assumes "0<w" "0\<le>x" "x<w"
  shows "circle_motion w v 0 x=x"
    "circle_motion w v u (circle_motion w v t x)=circle_motion w v (u+t) x"
proof -
  show "circle_motion w v 0 x=x"
    using wrap_identity[OF assms] by (simp add: circle_motion_def)
  show "circle_motion w v u (circle_motion w v t x)=circle_motion w v (u+t) x"
  proof -
    have nz: "w\<noteq>0" using assms(1) by simp
    show ?thesis unfolding circle_motion_def
      by (simp only: wrap_add_wrap[OF nz]) (simp add: algebra_simps)
  qed
qed

definition periodic_position :: "real \<Rightarrow> real \<Rightarrow> real" where
  "periodic_position L y = wrap (2*L) (y+L)-L"

definition reflecting_position :: "real \<Rightarrow> real \<Rightarrow> real" where
  "reflecting_position L y = L-abs(wrap (4*L) (y+L)-2*L)"

lemma endpoint_local_agreement:
  assumes "0<L" "-L\<le>y" "y<L"
  shows "periodic_position L y=y" "reflecting_position L y=y"
proof -
  have p: "wrap (2*L) (y+L)=y+L"
    by (rule wrap_identity) (use assms in linarith)+
  have r: "wrap (4*L) (y+L)=y+L"
    by (rule wrap_identity) (use assms in linarith)+
  show "periodic_position L y=y" by (simp add: periodic_position_def p)
  show "reflecting_position L y=y"
    using assms by (simp add: reflecting_position_def r abs_of_nonpos; linarith)
qed

lemma endpoint_after_first_crossing:
  assumes "0<L" "L<y" "y<3*L"
  shows "periodic_position L y=y-2*L"
    "reflecting_position L y=2*L-y"
proof -
  have f: "frac ((y+L)/(2*L)) = (y-L)/(2*L)"
  proof -
    have quot: "(y+L)/(2*L) = (y-L)/(2*L)+1"
      using assms(1) by (simp add: field_simps)
    have den: "0<2*L" using assms(1) by linarith
    have bd: "0\<le>(y-L)/(2*L)" "(y-L)/(2*L)<1"
    proof -
      show "0\<le>(y-L)/(2*L)"
        by (rule divide_nonneg_nonneg) (use assms in linarith)+
      have bound: "y-L<1*(2*L)" using assms by linarith
      show "(y-L)/(2*L)<1" using pos_divide_less_eq[OF den] bound by blast
    qed
    show ?thesis by (simp only: quot frac_1_eq) (use bd in \<open>simp add: frac_eq\<close>)
  qed
  show "periodic_position L y=y-2*L"
    by (simp only: periodic_position_def wrap_def f)
      (use assms(1) in \<open>simp add: field_simps\<close>)
  have r: "wrap (4*L) (y+L)=y+L"
    by (rule wrap_identity) (use assms in linarith)+
  show "reflecting_position L y=2*L-y"
    using assms by (simp add: reflecting_position_def r abs_of_nonneg; linarith)
qed

theorem endpoint_difference:
  assumes "0<L" "5*L/4<y" "y<7*L/4"
  shows "L/2 < reflecting_position L y-periodic_position L y"
proof -
  have bounds: "L<y" "y<3*L" using assms by linarith+
  show ?thesis using endpoint_after_first_crossing[OF assms(1) bounds] assms by linarith
qed

end
