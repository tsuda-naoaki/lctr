theory Gaussian_Coordinate_Range
  imports Hamiltonian_Transform
begin

lemma gaussian_coordinate_strict_mono:
  "strict_mono gaussian_coordinate"
proof (rule strict_monoI)
  fix a b :: real assume ab: "a<b"
  show "gaussian_coordinate a<gaussian_coordinate b"
  proof (rule DERIV_pos_imp_increasing[OF ab])
    fix x assume "a\<le>x" "x\<le>b"
    show "\<exists>y. DERIV gaussian_coordinate x :> y \<and> 0<y"
      using gaussian_coordinate_derivative[of x] by (intro exI[of _ "gaussian x"]) (simp add: gaussian_def)
  qed
qed

lemma gaussian_coordinate_odd:
  "gaussian_coordinate (-q) = -gaussian_coordinate q"
proof -
  have ref: "(LBINT x=0..-q. gaussian x)=(LBINT x=q..0. gaussian x)"
    using interval_integral_reflect[of 0 "ereal (-q)" gaussian]
    by (simp add: gaussian_def[abs_def] zero_ereal_def)
  have rev: "(LBINT x=q..0. gaussian x)=-(LBINT x=0..q. gaussian x)"
    by (rule interval_integral_endpoints_reverse)
  show ?thesis by (simp only: gaussian_coordinate_def ref rev)
qed

lemma gaussian_coordinate_limit:
  "(gaussian_coordinate \<longlongrightarrow> sqrt pi/2) at_top"
proof -
  have si: "set_integrable lborel {0..} gaussian"
    using gaussian_moment_0 by (simp add: gaussian_def[abs_def] set_integrable_def has_bochner_integral_iff)
  have integral_value: "(\<integral>x\<in>{0..}. gaussian x \<partial>lborel)=sqrt pi/2"
    using has_bochner_integral_integral_eq[OF gaussian_moment_0]
    by (simp add: gaussian_def[abs_def] set_lebesgue_integral_def)
  have lim: "((\<lambda>b. \<integral>x\<in>{0..b}. gaussian x \<partial>lborel) \<longlongrightarrow> sqrt pi/2) at_top"
    using tendsto_set_lebesgue_integral_at_top[OF _ si] integral_value by simp
  have eq: "\<forall>\<^sub>F b in at_top. (\<integral>x\<in>{0..b}. gaussian x \<partial>lborel)=gaussian_coordinate b"
    using eventually_ge_at_top[of "0::real"]
    by eventually_elim (simp add: gaussian_coordinate_def interval_integral_Icc zero_ereal_def)
  show ?thesis by (rule Lim_transform_eventually[OF lim eq])
qed

lemma gaussian_coordinate_upper:
  "gaussian_coordinate q < sqrt pi/2"
proof -
  have ev: "\<forall>\<^sub>F x in at_top. gaussian_coordinate (q+1)\<le>gaussian_coordinate x"
    using eventually_ge_at_top[of "q+1"]
    by eventually_elim (meson strict_mono_mono monoD gaussian_coordinate_strict_mono)
  have bound: "gaussian_coordinate (q+1)\<le>sqrt pi/2"
    by (rule tendsto_lowerbound[OF gaussian_coordinate_limit ev]) simp
  have "gaussian_coordinate q < gaussian_coordinate(q+1)"
    by (rule strict_monoD[OF gaussian_coordinate_strict_mono]) simp
  then show ?thesis using bound by linarith
qed

lemma gaussian_coordinate_bounds:
  "-sqrt pi/2 < gaussian_coordinate q" "gaussian_coordinate q < sqrt pi/2"
proof -
  show "-sqrt pi/2 < gaussian_coordinate q"
    using gaussian_coordinate_upper[of "-q"] by (simp add: gaussian_coordinate_odd; linarith)
  show "gaussian_coordinate q < sqrt pi/2" by (rule gaussian_coordinate_upper)
qed

lemma gaussian_coordinate_range:
  "range gaussian_coordinate = {-sqrt pi/2<..<sqrt pi/2}"
proof (rule set_eqI)
  fix y
  show "y\<in>range gaussian_coordinate \<longleftrightarrow> y\<in>{-sqrt pi/2<..<sqrt pi/2}"
  proof
    assume "y\<in>range gaussian_coordinate"
    then show "y\<in>{-sqrt pi/2<..<sqrt pi/2}"
      using gaussian_coordinate_bounds by auto
  next
    assume y: "y\<in>{-sqrt pi/2<..<sqrt pi/2}"
    then have lt: "max y (-y)<sqrt pi/2" by auto
    have ev: "\<forall>\<^sub>F b in at_top. 0<b \<and> max y (-y)<gaussian_coordinate b"
      using order_tendstoD(1)[OF gaussian_coordinate_limit lt]
        eventually_gt_at_top[of "0::real"] by eventually_elim auto
    obtain b where b: "0<b" "max y (-y)<gaussian_coordinate b"
      using eventually_happens[OF ev] by auto
    have byb: "y<gaussian_coordinate b" "-y<gaussian_coordinate b" using b(2) by auto
    have lo: "gaussian_coordinate (-b)\<le>y"
      using byb(2) by (simp add: gaussian_coordinate_odd; linarith)
    have hi: "y\<le>gaussian_coordinate b" using byb(1) by linarith
    have cont: "\<forall>x. -b\<le>x \<and> x\<le>b \<longrightarrow> isCont gaussian_coordinate x"
      by (intro allI impI) (rule DERIV_isCont[OF gaussian_coordinate_derivative])
    obtain x where "gaussian_coordinate x=y"
      using IVT[OF lo hi _ cont] b by auto
    then show "y\<in>range gaussian_coordinate" by blast
  qed
qed

end
