theory Core_Representation_Images
  imports LCTR_Factorization_Isabelle.Factorization_Isabelle
begin

locale representation_images =
  fixes A :: "'a set" and f :: "'a\<Rightarrow>'b::linorder" and g :: "'a\<Rightarrow>'c::linorder"
  assumes kernel: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> (f x=f y) = (g x=g y)"
    and ord: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> (f x<f y) = (g x<g y)"
begin
abbreviation F where "F \<equiv> factor_choice A f g"

lemma kernel_inclusion: "eqker_on A f\<subseteq>eqker_on A g"
  using kernel unfolding eqker_on_def by auto
lemma image_map_commutes: "x\<in>A \<Longrightarrow> F (f x)=g x"
  by (rule factor_choice_agrees[OF kernel_inclusion])
lemma image_map_unique:
  assumes commutes: "\<And>x. x\<in>A \<Longrightarrow> G (f x)=g x" and y: "y\<in>f`A"
  shows "G y=F y"
proof -
  obtain x where x: "x\<in>A" "y=f x" using y by blast
  have gx: "G (f x)=g x" by (rule commutes[OF x(1)])
  have fx: "F (f x)=g x" by (rule image_map_commutes[OF x(1)])
  show ?thesis using x gx fx by simp
qed
lemma image_map_range: "F ` (f`A) = g`A"
  using image_map_commutes by force
lemma image_map_injective: "inj_on F (f`A)"
proof (rule inj_onI)
  fix u v
  assume u: "u\<in>f`A" and v: "v\<in>f`A" and eq: "F u=F v"
  obtain x where x: "x\<in>A" "u=f x" using u by blast
  obtain y where y: "y\<in>A" "v=f y" using v by blast
  have "g x=g y" using eq x y image_map_commutes by simp
  then have "f x=f y" using kernel[OF x(1) y(1)] by blast
  then show "u=v" using x y by simp
qed
lemma image_map_bijective: "bij_betw F (f`A) (g`A)"
  by (simp add: bij_betw_def image_map_injective image_map_range)
lemma image_map_order:
  "u\<in>f`A \<Longrightarrow> v\<in>f`A \<Longrightarrow> (F u<F v) = (u<v)"
proof -
  assume u: "u\<in>f`A" and v: "v\<in>f`A"
  obtain x where x: "x\<in>A" "u=f x" using u by blast
  obtain y where y: "y\<in>A" "v=f y" using v by blast
  show ?thesis using ord[OF x(1) y(1)] x y image_map_commutes by simp
qed
lemma image_order_iso_exists_unique_on:
  "\<exists>F. bij_betw F (f`A) (g`A) \<and>
    (\<forall>u\<in>f`A. \<forall>v\<in>f`A. (F u<F v)=(u<v)) \<and>
    (\<forall>x\<in>A. F (f x)=g x) \<and>
    (\<forall>G. (\<forall>x\<in>A. G (f x)=g x) \<longrightarrow> (\<forall>y\<in>f`A. G y=F y))"
proof (rule exI[of _ F], intro conjI)
  show "bij_betw F (f`A) (g`A)" by (rule image_map_bijective)
  show "\<forall>u\<in>f`A. \<forall>v\<in>f`A. (F u<F v)=(u<v)"
    by (intro ballI, rule image_map_order)
  show "\<forall>x\<in>A. F (f x)=g x" by (intro ballI, rule image_map_commutes)
  show "\<forall>G. (\<forall>x\<in>A. G (f x)=g x) \<longrightarrow> (\<forall>y\<in>f`A. G y=F y)"
  proof (intro allI impI ballI)
    fix G y
    assume h: "\<forall>x\<in>A. G (f x)=g x" and y: "y\<in>f`A"
    show "G y=F y" by (rule image_map_unique[OF _ y]) (use h in blast)
  qed
qed
lemma restricted_graph_unique:
  assumes commutes: "\<And>x. x\<in>A \<Longrightarrow> G (f x)=g x"
  shows "{(y,G y) |y. y\<in>f`A} = {(y,F y) |y. y\<in>f`A}"
  using image_map_unique[OF commutes] by auto
end

lemma source_representation_image_uniqueness:
  fixes f :: "'a\<Rightarrow>'b::linorder" and g :: "'a\<Rightarrow>'c::linorder"
  assumes eq0: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> (f x=f y)=same x y"
    and eq1: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> (g x=g y)=same x y"
    and ord0: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> (f x<f y)=strict x y"
    and ord1: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> (g x<g y)=strict x y"
  shows "\<exists>F. bij_betw F (f`A) (g`A) \<and>
    (\<forall>u\<in>f`A. \<forall>v\<in>f`A. (F u<F v)=(u<v)) \<and>
    (\<forall>x\<in>A. F (f x)=g x) \<and>
    (\<forall>G. (\<forall>x\<in>A. G (f x)=g x) \<longrightarrow> (\<forall>y\<in>f`A. G y=F y))"
proof -
  interpret I: representation_images A f g
    by standard (simp_all add: eq0 eq1 ord0 ord1)
  show ?thesis by (rule I.image_order_iso_exists_unique_on)
qed

lemma empty_source_control:
  "bij_betw (factor_choice {} f g) (f`{}) (g`{})"
  "\<And>F G. {(y,F y) |y. y\<in>f`{}} = {(y,G y) |y. y\<in>f`{}}"
  by (simp_all add: bij_betw_def inj_on_def)
lemma missing_kernel_control: "\<not>(\<exists>F::unit\<Rightarrow>bool. \<forall>x. F ()=x)"
  by blast

ML \<open>
val roots = @{thms representation_images.image_map_commutes representation_images.image_map_unique
  representation_images.image_map_range representation_images.image_map_injective representation_images.image_map_bijective
  representation_images.image_map_order representation_images.image_order_iso_exists_unique_on
  representation_images.restricted_graph_unique source_representation_image_uniqueness empty_source_control missing_kernel_control};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
