theory Periodic_Group
  imports Periodic_Completion
begin

lemma periodic_transport:
  "periodic_fold L ((\<lambda>(p,y). (p,circle_motion (2*L) (2*p) t y)) (periodic_unfold L x))
    =periodic_motion L t x"
  by (simp add: periodic_fold_def periodic_unfold_def periodic_motion_def
    periodic_position_def circle_motion_def algebra_simps)

theorem periodic_preserves_state:
  assumes L: "0<L"
  shows "distr (strip_state L) (strip_state L) (periodic_motion L u)=strip_state L"
proof -
  let ?N = "periodic_state L"
  let ?H = "\<lambda>(p,y). (p,circle_motion (2*L) (2*p) u y)"
  have hm: "?H\<in>measurable ?N ?N"
    unfolding periodic_state_def gaussian_state_def circle_motion_def wrap_def frac_def by measurable
  have v: "(\<lambda>p. 2*p)\<in>borel_measurable gaussian_state" by (simp add: gaussian_state_def)
  have inv: "distr ?N ?N ?H=?N"
    unfolding periodic_state_def
    by (rule circle_skew_motion_preserves_open_product[OF _ v]) (use L in simp)
  have eq: "periodic_fold L \<circ> ?H \<circ> periodic_unfold L=periodic_motion L u"
    by (rule ext) (simp only: o_apply periodic_transport)
  show ?thesis using transported_invariant_measure[OF periodic_maps(1,2) hm
    periodic_unfold_pushforward[OF L] periodic_fold_pushforward[OF L] inv]
    by (simp only: eq)
qed

theorem periodic_group_law:
  assumes L: "0<L"
  shows "periodic_motion L u (periodic_motion L t x)=periodic_motion L (u+t) x"
proof -
  have nz: "2*L\<noteq>0" using L by simp
  have cancel: "(z-L)+a+L=z+a" for z a :: real by simp
  show ?thesis unfolding periodic_motion_def periodic_position_def
    by (simp only: fst_conv snd_conv cancel wrap_add_wrap[OF nz])
      (simp add: algebra_simps)
qed

theorem periodic_local_agreement:
  assumes "0<L" "-L<fst x+2 * snd x*u" "fst x+2 * snd x*u<L"
  shows "periodic_motion L u x=(fst x+2 * snd x*u,snd x)"
  unfolding periodic_motion_def
  using endpoint_local_agreement(1)[of L "fst x+2 * snd x*u"] assms by simp

theorem periodic_identity:
  assumes L: "0<L"
  shows "AE x in strip_state L. periodic_motion L 0 x=x"
proof -
  let ?N = "periodic_state L"
  let ?H = "\<lambda>(p,y). (p,circle_motion (2*L) (2*p) 0 y)"
  interpret G: prob_space gaussian_state by (rule gaussian_state_probability)
  have zero: "AE z in ?N. ?H z=z"
    unfolding periodic_state_def by (rule circle_skew_identity[OF _ G.sigma_finite_measure_axioms]) (use L in simp)
  have inv: "AE x in strip_state L. periodic_fold L (periodic_unfold L x)=x"
    by (simp add: periodic_inverses)
  show ?thesis using transported_identity[OF periodic_maps(1) periodic_unfold_pushforward[OF L] zero inv]
    by (simp only: periodic_transport)
qed

end
