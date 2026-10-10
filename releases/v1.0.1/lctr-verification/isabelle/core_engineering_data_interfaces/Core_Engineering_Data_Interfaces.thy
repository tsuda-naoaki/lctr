theory Core_Engineering_Data_Interfaces
  imports "../core_audit_state_transport/Core_Audit_State_Transport"
    "HOL-Library.Extended_Real"
begin

definition engineering_spec where
  "engineering_spec input ev scale observer target = (ev=(input,observer,target))"

lemma engineering_components:
  "engineering_spec input ev scale obs z = (fst ev=input \<and> fst (snd ev)=obs \<and> snd (snd ev)=z)"
  by (simp add: engineering_spec_def prod_eq_iff)

definition pair_spec where
  "pair_spec input_of operative a b =
    (\<exists>x obs z1 z2. operative x \<and> z1\<noteq>z2 \<and>
      a=(input_of x,obs,z1) \<and> b=(input_of x,obs,z2))"

lemma pair_common_context:
  "pair_spec input_of operative a b \<Longrightarrow>
    fst a=fst b \<and> fst (snd a)=fst (snd b) \<and> snd (snd a)\<noteq>snd (snd b) \<and>
    (\<exists>x. operative x \<and> fst a=input_of x)"
  by (auto simp: pair_spec_def)

definition closed_intervals :: "'a::linorder set \<Rightarrow> ('a\<times>'a) set" where
  "closed_intervals S = {(l,r). l\<in>S \<and> r\<in>S \<and> l\<le>r}"

lemma interval_membership:
  "((l,r)\<in>closed_intervals S) = (l\<in>S \<and> r\<in>S \<and> l\<le>r)"
  by (simp add: closed_intervals_def)

definition interval_audit :: "'a::linorder \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> audit_status" where
  "interval_audit l r theta = (if r\<le>theta then Pass else if theta<l then Fail else Indeterminate)"

lemma interval_pass: "(interval_audit l r theta=Pass) = (r\<le>theta)"
  by (simp add: interval_audit_def)

lemma interval_fail:
  assumes ordered: "l\<le>r"
  shows "(interval_audit l r theta=Fail) = (theta<l)"
  using ordered by (auto simp: interval_audit_def)

lemma interval_indeterminate:
  "(interval_audit l r theta=Indeterminate) = (l\<le>theta \<and> theta<r)"
  by (auto simp: interval_audit_def)

lemma interval_range:
  "interval_audit l r theta=Pass \<or> interval_audit l r theta=Fail \<or> interval_audit l r theta=Indeterminate"
  by (simp add: interval_audit_def)

lemma threshold_equality_pass: "interval_audit l r r=Pass"
  by (simp add: interval_audit_def)

lemma infinite_threshold_pass: "interval_audit (l::ereal) r \<infinity>=Pass"
  by (simp add: interval_audit_def)

definition view_data where "view_data carrier_at z obs l view=(carrier_at z,obs,l,view)"

lemma view_components:
  "fst (view_data carrier_at z obs l view)=carrier_at z \<and>
    fst (snd (view_data carrier_at z obs l view))=obs \<and>
    fst (snd (snd (view_data carrier_at z obs l view)))=l \<and>
    snd (snd (snd (view_data carrier_at z obs l view)))=view"
  by (simp add: view_data_def)

definition view_relation where "view_relation relation view q v = (relation q v \<and> q\<in>view)"

lemma restricted_relation:
  "view_relation relation view q v = (relation q v \<and> q\<in>view)"
  by (simp add: view_relation_def)

lemma restricted_domain:
  "(\<exists>v. view_relation relation view q v) = (q\<in>view \<and> (\<exists>v. relation q v))"
  by (auto simp: view_relation_def)

definition bulk where "bulk carriers = (carriers (0::nat)=carriers 1)"
definition following where
  "following carriers views relation = (carriers (0::nat)\<noteq>carriers 1 \<and>
    (\<forall>k<2. \<forall>q\<in>views k. \<exists>v. view_relation relation (views k) q v))"

lemma following_exact:
  "following carriers views relation = (carriers (0::nat)\<noteq>carriers 1 \<and>
    (\<forall>k<2. \<forall>q\<in>views k. \<exists>v. relation q v))"
  by (auto simp: following_def restricted_domain)

lemma following_not_bulk: "following carriers views relation \<Longrightarrow> \<not>bulk carriers"
  by (simp add: following_def bulk_def)

lemma empty_views: "following carriers (\<lambda>_. {}) relation = (carriers (0::nat)\<noteq>carriers 1)"
  by (simp add: following_def)

lemma missing_record_excludes_following:
  "k<2 \<Longrightarrow> q\<in>views k \<Longrightarrow> (\<forall>v. \<not>relation q v) \<Longrightarrow>
    \<not>following carriers views relation"
  by (auto simp: following_exact)

record 'q invasiveness_data =
  invasion_relation :: "('q\<times>'q) set"
  invasion_lower :: ereal
  invasion_upper :: ereal
  invasion_tolerance :: ereal

definition invasiveness_typed where
  "invasiveness_typed d = (0\<le>invasion_lower d \<and> 0\<le>invasion_upper d \<and>
    0\<le>invasion_tolerance d \<and> invasion_lower d\<le>invasion_upper d)"
definition invasiveness_audit where
  "invasiveness_audit d = interval_audit (invasion_lower d) (invasion_upper d) (invasion_tolerance d)"

lemma invasiveness_components:
  "let d=\<lparr>invasion_relation=relation,invasion_lower=l,invasion_upper=r,invasion_tolerance=theta\<rparr>
   in invasion_relation d=relation \<and> invasion_lower d=l \<and> invasion_upper d=r \<and> invasion_tolerance d=theta"
  by simp

lemma invasiveness_exact:
  assumes typed: "invasiveness_typed d"
  shows "(invasiveness_audit d=Pass) = (invasion_upper d\<le>invasion_tolerance d) \<and>
    ((invasiveness_audit d=Fail) = (invasion_tolerance d<invasion_lower d)) \<and>
    ((invasiveness_audit d=Indeterminate) =
      (invasion_lower d\<le>invasion_tolerance d \<and> invasion_tolerance d<invasion_upper d))"
  using typed by (simp add: invasiveness_typed_def invasiveness_audit_def interval_pass interval_fail interval_indeterminate)

ML \<open>
val roots = @{thms engineering_components pair_common_context interval_membership
  interval_pass interval_fail interval_indeterminate interval_range threshold_equality_pass
  infinite_threshold_pass view_components restricted_relation restricted_domain following_exact
  following_not_bulk empty_views missing_record_excludes_following invasiveness_components invasiveness_exact};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
