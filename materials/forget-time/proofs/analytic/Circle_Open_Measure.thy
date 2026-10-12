theory Circle_Open_Measure
  imports Circle_Measure
begin

lemma uniform_open_halfopen:
  fixes w :: real
  assumes w: "0<w"
  shows "uniform_measure lborel {0<..<w}=uniform_measure lborel {0..<w}"
proof -
  have a: "emeasure lborel {0<..<w}=ennreal w" using w by simp
  have b: "emeasure lborel {0..<w}=ennreal w" using w by simp
  show ?thesis unfolding uniform_measure_def a b
  proof (rule density_cong)
    show "(\<lambda>x. indicator {0<..<w} x/ennreal w)\<in>borel_measurable lborel" by measurable
    show "(\<lambda>x. indicator {0..<w} x/ennreal w)\<in>borel_measurable lborel" by measurable
    show "AE x in lborel. indicator {0<..<w} x/ennreal w=indicator {0..<w} x/ennreal w"
      using AE_lborel_singleton[of "0::real"]
      by eventually_elim (auto simp: indicator_def)
  qed
qed

theorem circle_skew_motion_preserves_open_product:
  assumes w: "0<w" and v: "v\<in>borel_measurable M"
  shows "distr (M\<Otimes>\<^sub>M uniform_measure lborel {0<..<w})
    (M\<Otimes>\<^sub>M uniform_measure lborel {0<..<w})
    (\<lambda>(p,y). (p,circle_motion w (v p) u y))
    =M\<Otimes>\<^sub>M uniform_measure lborel {0<..<w}"
  unfolding uniform_open_halfopen[OF w]
  by (rule circle_skew_motion_preserves_product[OF w v])

theorem circle_skew_composition:
  assumes "0<w"
  shows "(\<lambda>(p,y). (p,circle_motion w (v p) u y))
    ((\<lambda>(p,y). (p,circle_motion w (v p) t y)) x)
    =(\<lambda>(p,y). (p,circle_motion w (v p) (u+t) y)) x"
proof -
  have nz: "w\<noteq>0" using assms by simp
  show ?thesis by (cases x)
    (simp only: case_prod_conv circle_motion_def wrap_add_wrap[OF nz];
     simp add: algebra_simps)
qed

theorem circle_skew_identity:
  assumes w: "0<w" and M: "sigma_finite_measure M"
  shows "AE x in M\<Otimes>\<^sub>M uniform_measure lborel {0<..<w}.
    (\<lambda>(p,y). (p,circle_motion w (v p) 0 y)) x=x"
proof -
  let ?U = "uniform_measure lborel {0<..<w}"
  interpret M: sigma_finite_measure M by (rule M)
  interpret U: prob_space ?U by (rule prob_space_uniform_measure) (use w in auto)
  interpret MU: pair_sigma_finite M ?U by unfold_locales
  have uy: "AE y in ?U. 0<y \<and> y<w" by (rule AE_uniform_measureI) auto
  have mys: "{x\<in>space(M\<Otimes>\<^sub>M ?U). 0<snd x \<and> snd x<w}\<in>sets(M\<Otimes>\<^sub>M ?U)" by measurable
  have sy: "AE x in M\<Otimes>\<^sub>M ?U. 0<snd x \<and> snd x<w"
    by (rule MU.AE_pair_measure[OF mys]) (use uy in \<open>auto intro: AE_I2\<close>)
  have point: "(\<lambda>(p,y). (p,circle_motion w (v p) 0 y)) x=x"
    if "0<snd x" "snd x<w" for x
  proof -
    obtain p y where xy: "x=(p,y)" by (cases x) auto
    have y: "0\<le>y" "y<w" using that by (simp_all add: xy)
    have "circle_motion w (v p) 0 y=y" by (rule circle_motion_group(1)[OF w y])
    then show ?thesis by (simp add: xy)
  qed
  show ?thesis using sy by eventually_elim (blast intro: point)
qed

end
