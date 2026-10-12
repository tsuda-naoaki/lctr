theory Completion_Conjugacy
  imports "HOL-Probability.Probability"
begin

theorem transported_invariant_measure:
  assumes Um: "U\<in>measurable M N" and Fm: "F\<in>measurable N M"
    and Hm: "H\<in>measurable N N"
    and U: "distr M N U=N" and F: "distr N M F=M" and H: "distr N N H=N"
  shows "distr M M (F \<circ> H \<circ> U)=M"
proof -
  have hm: "H \<circ> U\<in>measurable M N" by (rule measurable_comp[OF Um Hm])
  have "distr M M (F \<circ> H \<circ> U)=distr (distr M N (H \<circ> U)) M F"
    using distr_distr[OF Fm hm] by (simp add: o_assoc)
  also have "...=M" using distr_distr[OF Hm Um] U F H by simp
  finally show ?thesis .
qed

theorem transported_group_law:
  fixes H :: "real \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes Um: "U\<in>measurable M N"
    and Hm: "\<And>t. H t\<in>measurable N N"
    and U: "distr M N U=N"
    and H: "\<And>t. distr N N (H t)=N"
    and inverse: "AE y in N. U(F y)=y"
    and group: "AE y in N. H u (H t y)=H (u+t) y"
  shows "AE x in M. F(H u (U(F(H t (U x)))))=F(H (u+t) (U x))"
proof -
  have hm: "H t \<circ> U\<in>measurable M N" by (rule measurable_comp[OF Um Hm])
  have push: "distr M N (H t \<circ> U)=N" using distr_distr[OF Hm Um] U H by simp
  have inv: "AE x in M. U(F(H t (U x)))=H t (U x)"
  proof -
    have "AE x in distr M N (H t \<circ> U). U(F x)=x" by (simp only: push inverse)
    then show ?thesis using AE_distrD[OF hm] by (simp add: o_def)
  qed
  have grp: "AE x in M. H u (H t (U x))=H (u+t) (U x)"
  proof -
    have gd: "AE y in distr M N U. H u (H t y)=H (u+t) y" by (simp only: U group)
    show ?thesis by (rule AE_distrD[OF Um gd])
  qed
  show ?thesis using inv grp by eventually_elim simp
qed

theorem transported_identity:
  assumes Um: "U\<in>measurable M N" and U: "distr M N U=N"
    and zero: "AE y in N. H y=y" and inverse: "AE x in M. F(U x)=x"
  shows "AE x in M. F(H(U x))=x"
proof -
  have zd: "AE y in distr M N U. H y=y" by (simp only: U zero)
  have "AE x in M. H(U x)=U x" by (rule AE_distrD[OF Um zd])
  then show ?thesis using inverse by eventually_elim simp
qed

end
