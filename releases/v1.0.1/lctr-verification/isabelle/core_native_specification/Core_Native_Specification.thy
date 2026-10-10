theory Core_Native_Specification
  imports LCTR_Core_Token_Graph.Core_Token_Graph
begin

definition spec_carrier :: "bool \<Rightarrow> 'e set \<Rightarrow> 'l set \<Rightarrow> ('e + ('e\<times>'l)) set" where
  "spec_carrier a E L = (if a then Inr ` (E\<times>L) else Inl ` E)"
definition spec_at where "spec_at a e l = (if a then Inr (e,l) else Inl e)"
definition restriction where
  "restriction p x = (if p then x else case x of Inl e \<Rightarrow> Inl e | Inr z \<Rightarrow> Inl (fst z))"

lemma strict_specification: "spec_at False e l = Inl e" by (simp add: spec_at_def)
lemma approximate_specification: "spec_at True e l = Inr (e,l)" by (simp add: spec_at_def)
lemma strict_scale_independent: "spec_at False e l = spec_at False e m" by (simp add: spec_at_def)
lemma strict_restriction_identity:
  "x\<in>spec_carrier False E L \<Longrightarrow> restriction False x=x"
  by (auto simp: spec_carrier_def restriction_def)
lemma approximate_restriction_identity:
  "x\<in>spec_carrier True E L \<Longrightarrow> restriction True x=x"
  by (simp add: restriction_def)
lemma approximation_to_strict_projection:
  "restriction False (Inr (e,l))=Inl e" by (simp add: restriction_def)
lemma restriction_coherent:
  "(p\<longrightarrow>q) \<Longrightarrow> restriction p (spec_at q e l)=spec_at p e l"
  by (cases p; cases q) (simp_all add: restriction_def spec_at_def)

definition kind where "kind t = (fst t=3)"
lemma edge_kind: "(a,b)\<in>edges \<Longrightarrow> kind a \<Longrightarrow> kind b"
  using edge_allowed[of a b] by (auto simp: kind_def allowed_def)
definition arg_at where "arg_at e l t=(t,spec_at (kind t) e l)"
definition pred_arg where "pred_arg a x=(a,restriction (kind a) x)"
lemma predecessor_section_coherent:
  "(a,b)\<in>edges \<Longrightarrow> pred_arg a (spec_at (kind b) e l)=arg_at e l a"
  using edge_kind[of a b] restriction_coherent[of "kind a" "kind b" e l]
  by (auto simp: pred_arg_def arg_at_def)
definition evaluate where "evaluate K a=K (fst a) (snd a)"
lemma evaluation_exact: "evaluate K (t,x) = K t x" by (simp add: evaluate_def)

definition totalized where "totalized D P x = (\<exists>y\<in>D. x=y \<and> P y)"
lemma totalization_on_domain: "x\<in>D \<Longrightarrow> totalized D P x=P x" by (auto simp: totalized_def)
lemma totalization_off_domain: "x\<notin>D \<Longrightarrow> \<not>totalized D P x" by (auto simp: totalized_def)
lemma totalization_original_exists: "totalized D P x=(\<exists>y\<in>D. x=y \<and> P y)" by (simp add: totalized_def)
lemma restriction_unique_on_image:
  assumes pq: "p\<longrightarrow>q" and coh: "\<And>e l. e\<in>E \<Longrightarrow> l\<in>L \<Longrightarrow> f (spec_at q e l)=spec_at p e l"
    and e: "e\<in>E" and l: "l\<in>L"
  shows "f (spec_at q e l)=restriction p (spec_at q e l)"
proof -
  have r: "restriction p (spec_at q e l)=spec_at p e l"
    by (rule restriction_coherent[OF pq])
  show ?thesis using coh[OF e l] r by simp
qed
lemma strict_restriction_unique_with_scale:
  assumes l: "l\<in>L" and coh: "\<And>e m. e\<in>E \<Longrightarrow> m\<in>L \<Longrightarrow> f (spec_at False e m)=spec_at False e m"
    and x: "x\<in>spec_carrier False E L"
  shows "f x=x"
proof -
  obtain e where e: "e\<in>E" and xeq: "x=Inl e" using x by (auto simp: spec_carrier_def)
  show ?thesis using coh[OF e l] by (simp add: spec_at_def xeq)
qed
lemma empty_scale_uniqueness_control:
  "(\<forall>e::bool. \<forall>l\<in>({}::unit set). id e=e \<and> (\<not>e)=e) \<and> (id::bool\<Rightarrow>bool)\<noteq>Not"
proof (intro conjI)
  show "\<forall>e::bool. \<forall>l\<in>({}::unit set). id e=e \<and> (\<not>e)=e" by simp
  show "(id::bool\<Rightarrow>bool)\<noteq>Not"
  proof
    assume eq: "(id::bool\<Rightarrow>bool)=Not"
    have "id False=Not False" by (rule fun_cong[OF eq])
    then show False by simp
  qed
qed

ML \<open>
val roots = @{thms strict_specification approximate_specification strict_scale_independent
  strict_restriction_identity approximate_restriction_identity approximation_to_strict_projection
  restriction_coherent edge_kind predecessor_section_coherent evaluation_exact totalization_on_domain
  totalization_off_domain totalization_original_exists restriction_unique_on_image
  strict_restriction_unique_with_scale empty_scale_uniqueness_control};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
