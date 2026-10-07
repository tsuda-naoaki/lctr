theory Core_Representation_Alignment
  imports LCTR_Core_Representation_Images.Core_Representation_Images
begin

lemmas imageProjection_surjective = projection_surjective_onto_its_image

lemma imageMap_commutes:
  assumes kernel: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> f x=f y \<Longrightarrow> g x=g y"
    and x: "x\<in>A"
  shows "factor_choice A f g (f x)=g x"
proof -
  have inclusion: "eqker_on A f \<subseteq> eqker_on A g"
    using kernel unfolding eqker_on_def by auto
  show ?thesis by (rule factor_choice_agrees[OF inclusion x])
qed

lemma imageMap_unique:
  assumes kernel: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> f x=f y \<Longrightarrow> g x=g y"
    and commutes: "\<And>x. x\<in>A \<Longrightarrow> F (f x)=g x"
  shows "\<forall>y\<in>f`A. F y=factor_choice A f g y"
proof (intro ballI)
  fix y
  assume "y\<in>f`A"
  then obtain x where x: "x\<in>A" "y=f x" by blast
  have fx: "factor_choice A f g (f x)=g x"
    by (rule imageMap_commutes[where A=A and f=f and g=g and x=x])
       (fact kernel, fact x(1))
  show "F y=factor_choice A f g y"
    by (simp only: x(2); rule trans[OF commutes[OF x(1)] fx[symmetric]])
qed

lemmas imageMap_strict_order = representation_images.image_map_order
lemmas image_order_iso_exists_unique = representation_images.image_order_iso_exists_unique_on
lemmas source_representation_image_uniqueness = Core_Representation_Images.source_representation_image_uniqueness

lemma empty_source_image:
  "f ` {} = {}"
  by simp

lemmas missing_kernel_control = Core_Representation_Images.missing_kernel_control

ML \<open>
val roots = @{thms imageProjection_surjective imageMap_commutes imageMap_unique
  imageMap_strict_order image_order_iso_exists_unique source_representation_image_uniqueness
  empty_source_image missing_kernel_control};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
