theory Core_Strict_Partial_Order
  imports Main
begin

lemma strict_part_contract:
  fixes A :: "'a set" and r :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes refl: "\<And>x. x\<in>A \<Longrightarrow> r x x"
    and trans: "\<And>x y z. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> z\<in>A \<Longrightarrow>
      r x y \<Longrightarrow> r y z \<Longrightarrow> r x z"
    and anti: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow>
      r x y \<Longrightarrow> r y x \<Longrightarrow> x=y"
  shows "(\<forall>x\<in>A. \<not> (r x x \<and> x\<noteq>x)) \<and>
    (\<forall>x\<in>A. \<forall>y\<in>A. \<forall>z\<in>A.
      (r x y \<and> x\<noteq>y) \<longrightarrow>
      (r y z \<and> y\<noteq>z) \<longrightarrow> (r x z \<and> x\<noteq>z))"
proof (intro conjI)
  show "\<forall>x\<in>A. \<not> (r x x \<and> x\<noteq>x)" by simp
  show "\<forall>x\<in>A. \<forall>y\<in>A. \<forall>z\<in>A.
      (r x y \<and> x\<noteq>y) \<longrightarrow>
      (r y z \<and> y\<noteq>z) \<longrightarrow> (r x z \<and> x\<noteq>z)"
  proof (intro ballI impI)
    fix x y z
    assume xA: "x\<in>A" and yA: "y\<in>A" and zA: "z\<in>A"
      and xy: "r x y \<and> x\<noteq>y" and yz: "r y z \<and> y\<noteq>z"
    have xz: "r x z" using trans[OF xA yA zA] xy yz by blast
    have ne: "x\<noteq>z"
    proof
      assume "x=z"
      then have yx: "r y x" using yz by simp
      have "x=y" using anti[OF xA yA] xy yx by blast
      then show False using xy by simp
    qed
    show "r x z \<and> x\<noteq>z" using xz ne by simp
  qed
qed

ML \<open>
val roots = @{thms strict_part_contract};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
