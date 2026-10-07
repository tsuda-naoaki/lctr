theory Core_Law_Input_Bundle
  imports "LCTR_Core_Native_Observables.Core_Native_Observables"
    "LCTR_Core_Record_Codes_Aligned.Core_Record_Codes" "HOL-Library.FuncSet"
begin
record ('q,'s,'v) law_observable =
  bundle_ranges :: "'q\<Rightarrow>'v set"
  bundle_values :: "('q\<times>'s)\<Rightarrow>'v"
record ('quot,'t,'s,'q,'v,'rec) law_input_bundle =
  bundle_quotient :: 'quot
  bundle_domain :: "'t set"
  bundle_trajectory :: "'t\<Rightarrow>'s"
  bundle_observables :: "('q,'s,'v) law_observable"
  bundle_records :: 'rec

type_synonym ('c,'b,'d,'q,'v,'win,'fld,'seq) concrete_law_bundle =
  "(('c\<Rightarrow>'c set)\<times>('b\<Rightarrow>'b set)\<times>('c set\<times>'c set)set\<times>('c set\<times>'b set)set,
    'c set,'b set,'q,'v,('win\<times>'fld\<times>'seq)set\<times>('d\<Rightarrow>'win\<times>'fld\<times>'seq)\<times>
    (('c set\<times>('win\<times>'fld\<times>'seq))set\<times>('b set\<times>('win\<times>'fld\<times>'seq))set)\<times>
    (('c set\<times>'b set)\<times>('win\<times>'fld\<times>'seq))set) law_input_bundle"

locale native_law_bundle =
  native_observables C D B R Bind source_order U L Q A idx record_map local_values local_obs compare val_range
  for C :: "'c set" and D :: "'d set" and B :: "'b set"
    and R :: "('c\<times>'d\<times>'b) set"
    and Bind :: "(('c\<times>'d\<times>'b)\<times>('c\<times>'d\<times>'b)) set"
    and source_order :: "('c\<times>'c) set"
    and U :: "'u set" and L :: "'l set" and Q :: "'q set"
    and A :: "'u\<Rightarrow>'a set" and idx :: "'l\<Rightarrow>'q"
    and record_map :: "'u\<Rightarrow>'a\<Rightarrow>'b"
    and local_values :: "'u\<Rightarrow>'l\<Rightarrow>'w set"
    and local_obs :: "'u\<Rightarrow>'l\<Rightarrow>'a\<Rightarrow>'w"
    and compare :: "'u\<Rightarrow>'l\<Rightarrow>'w\<Rightarrow>'v"
    and val_range :: "'l\<Rightarrow>'v set" +
  fixes window :: "'d\<Rightarrow>'win" and field :: "'d\<Rightarrow>'fld" and sequence :: "'d\<Rightarrow>'seq"
  assumes single: "\<And>t s s'. (t,s)\<in>trajectory_rel \<Longrightarrow> (t,s')\<in>trajectory_rel \<Longrightarrow> s=s'"
begin
sublocale rec: record_codes C D B R Bind window field sequence .
definition quotient_data where
  "quotient_data=(restrict (\<lambda>c. Image EC {c}) C, restrict (\<lambda>b. Image EB {b}) B,
    generated_order,trajectory_rel)"
definition record_data where
  "record_data=(rec.record_values,restrict rec.code D,(rec.time_records,rec.state_records),rec.pair_records)"
definition observable_data where
  "observable_data=\<lparr>bundle_ranges=restrict obs.canonical_range Q,
    bundle_values=restrict (\<lambda>p. obs.canonical(fst p)(snd p)) (Q\<times>State)\<rparr>"
definition observable_specification where
  "observable_specification (ob::('q,'b set,'v) law_observable) \<longleftrightarrow>
    bundle_ranges ob\<in>extensional Q \<and> bundle_values ob\<in>extensional(Q\<times>State) \<and>
    (\<forall>l\<in>L. bundle_ranges ob (idx l)=val_range l) \<and>
    (\<forall>u\<in>U. \<forall>l\<in>L. \<forall>a\<in>A u.
      bundle_values ob(idx l,local_state u a)=compare u l(local_obs u l a))"

lemma observable_spec: "observable_specification observable_data"
proof -
  have iq: "\<And>l. l\<in>L \<Longrightarrow> idx l\<in>Q" using index_onto by blast
  have ranges: "\<And>l. l\<in>L \<Longrightarrow> obs.canonical_range(idx l)=val_range l"
    using range_representative_independence iq by blast
  have vals: "\<And>u l a. u\<in>U \<Longrightarrow> l\<in>L \<Longrightarrow> a\<in>A u \<Longrightarrow>
    obs.canonical(idx l)(local_state u a)=compare u l(local_obs u l a)"
  proof -
    fix u l a assume h: "u\<in>U" "l\<in>L" "a\<in>A u"
    show "obs.canonical(idx l)(local_state u a)=compare u l(local_obs u l a)"
      by (rule canonical_representative_value[OF h refl refl])
  qed
  show ?thesis using ranges vals iq state_typed
    unfolding observable_specification_def observable_data_def by auto
qed

lemma observable_unique:
  assumes spec: "observable_specification (ob::('q,'b set,'v) law_observable)"
  shows "ob=observable_data"
proof -
  have hr: "\<forall>q\<in>Q. bundle_ranges ob q=obs.canonical_range q"
  proof (intro ballI)
    fix q assume q: "q\<in>Q"
    obtain l where l: "l\<in>L" and eq: "idx l=q" using q index_onto by blast
    have "bundle_ranges ob q=val_range l" using spec l eq unfolding observable_specification_def by blast
    then show "bundle_ranges ob q=obs.canonical_range q"
      using range_representative_independence[OF q l eq] by simp
  qed
  have hv: "\<forall>p\<in>Q\<times>State. bundle_values ob p=obs.canonical(fst p)(snd p)"
    by (rule canonical_unique) (use spec in \<open>auto simp: observable_specification_def\<close>)
  have er: "bundle_ranges ob=bundle_ranges observable_data"
    using spec hr unfolding observable_specification_def observable_data_def
    by (intro extensionalityI[where A=Q]) auto
  have ev: "bundle_values ob=bundle_values observable_data"
    using spec hv unfolding observable_specification_def observable_data_def
    by (intro extensionalityI[where A="Q\<times>State"]) auto
  show ?thesis using er ev by (cases ob; simp add: observable_data_def)
qed

definition law_input where
  "law_input=\<lparr>bundle_quotient=quotient_data,bundle_domain=trajectory_domain,
    bundle_trajectory=restrict canonical_trajectory trajectory_domain,
    bundle_observables=observable_data,bundle_records=record_data\<rparr>"
definition law_input_specification where
  "law_input_specification (x::('c,'b,'d,'q,'v,'win,'fld,'seq) concrete_law_bundle) \<longleftrightarrow>
    bundle_quotient x=quotient_data \<and> bundle_domain x=trajectory_domain \<and>
    bundle_trajectory x\<in>extensional trajectory_domain \<and>
    (\<forall>t\<in>trajectory_domain. \<forall>s. ((t,s)\<in>trajectory_rel \<longleftrightarrow> s=bundle_trajectory x t)) \<and>
    observable_specification(bundle_observables x) \<and> bundle_records x=record_data"

lemma law_input_spec: "law_input_specification law_input"
  using canonical_graph_contract[OF single] observable_spec
  unfolding law_input_specification_def law_input_def by auto

lemma law_input_unique:
  assumes spec: "law_input_specification x"
  shows "x=law_input"
proof -
  have graph: "\<forall>t\<in>trajectory_domain. \<forall>s. ((t,s)\<in>trajectory_rel \<longleftrightarrow> s=bundle_trajectory x t)"
    using spec unfolding law_input_specification_def by blast
  have agree: "\<forall>t\<in>trajectory_domain. bundle_trajectory x t=canonical_trajectory t"
    by (rule mp[OF HOL.spec[OF conjunct2[OF canonical_graph_contract[OF single]]] graph])
  have et: "bundle_trajectory x=restrict canonical_trajectory trajectory_domain"
    using spec agree unfolding law_input_specification_def
    by (intro extensionalityI[where A=trajectory_domain]) auto
  have eo: "bundle_observables x=observable_data"
    by (rule observable_unique) (use spec in \<open>simp add: law_input_specification_def\<close>)
  show ?thesis using spec et eo unfolding law_input_specification_def law_input_def
    by (cases x) auto
qed

lemma law_input_exists_unique: "\<exists>!x. law_input_specification x"
  by (rule ex1I[where a=law_input]) (rule law_input_spec, rule law_input_unique, assumption)

lemma record_pair_typed:
  "p\<in>snd(snd(snd(bundle_records law_input))) \<Longrightarrow>
    fst p\<in>snd(snd(snd(bundle_quotient law_input))) \<and> snd p\<in>fst(bundle_records law_input)"
  using rec.pair_records_typed[of p]
  unfolding law_input_def record_data_def quotient_data_def trajectory_rel_def EC_def EB_def by simp

lemma role_record_projection:
  "(\<forall>t v. (t,v)\<in>fst(fst(snd(snd(bundle_records law_input)))) \<longleftrightarrow>
      (\<exists>s. ((t,s),v)\<in>snd(snd(snd(bundle_records law_input))))) \<and>
   (\<forall>s v. (s,v)\<in>snd(fst(snd(snd(bundle_records law_input)))) \<longleftrightarrow>
      (\<exists>t. ((t,s),v)\<in>snd(snd(snd(bundle_records law_input)))))"
  unfolding law_input_def record_data_def
  using rec.time_projection_exact rec.state_projection_exact by simp

lemma source_relation_exact:
  assumes desc: "trajectory_descent.desc (source_rel C D B R) EC EB"
    and c: "c\<in>C" and b: "b\<in>B"
  shows "(fst(bundle_quotient law_input)c,fst(snd(bundle_quotient law_input))b)
    \<in>snd(snd(snd(bundle_quotient law_input))) \<longleftrightarrow> (\<exists>r\<in>D. (c,r,b)\<in>R)"
proof -
  interpret descent: trajectory_descent C B "source_rel C D B R" EC EB
    unfolding EC_def EB_def by (rule native_trajectory_interface)
  have h: "(Image EC {c},Image EB {b})\<in>trajectory_rel \<longleftrightarrow>
    (c,b)\<in>source_rel C D B R"
    using descent.exact_membership[OF desc c b] unfolding trajectory_rel_def .
  show ?thesis using h c b unfolding law_input_def quotient_data_def source_rel_def by simp
qed

lemma observable_value_typed:
  "q\<in>Q \<Longrightarrow> s\<in>State \<Longrightarrow>
    bundle_values(bundle_observables law_input)(q,s)\<in>bundle_ranges(bundle_observables law_input)q"
  using canonical_value_typed[of q s]
  unfolding law_input_def observable_data_def by simp

lemma observable_change_preserved:
  assumes u: "u\<in>U" and v: "v\<in>U" and l: "l\<in>L" and a: "a\<in>A u"
    and dom: "local_obs u l a\<in>change_domain u v l"
    and commutes: "\<And>u v l a. u\<in>U \<Longrightarrow> v\<in>U \<Longrightarrow> l\<in>L \<Longrightarrow> a\<in>A u \<Longrightarrow>
      local_obs u l a\<in>change_domain u v l \<Longrightarrow>
      compare v l(change u v l(local_obs u l a))=compare u l(local_obs u l a)"
  shows "bundle_values(bundle_observables law_input)(idx l,local_state u a)=
    compare v l(change u v l(local_obs u l a))"
proof -
  have eq: "obs.canonical(idx l)(local_state u a)=compare v l(change u v l(local_obs u l a))"
    by (rule local_change_compatibility[where change_domain=change_domain and change=change,
      OF u v l a dom]) (rule commutes; assumption)
  have iq: "idx l\<in>Q" using index_onto l by blast
  show ?thesis using eq state_typed[OF u a] iq
    unfolding law_input_def observable_data_def by simp
qed
end
ML \<open>
val roots = @{thms native_law_bundle.observable_spec native_law_bundle.observable_unique
 native_law_bundle.law_input_spec native_law_bundle.law_input_unique native_law_bundle.law_input_exists_unique
 native_law_bundle.record_pair_typed native_law_bundle.role_record_projection native_law_bundle.source_relation_exact
 native_law_bundle.observable_value_typed native_law_bundle.observable_change_preserved};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
