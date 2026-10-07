theory Core_Dynamics_Bundle
  imports "LCTR_Core_Law_Input_Bundle.Core_Law_Input_Bundle"
begin
record ('t,'q) generated_time_data =
  td_order :: "('q\<times>'q)set"
  td_projection :: "'t\<Rightarrow>'q"
  td_embedding :: "'q\<Rightarrow>real"
  td_representation :: "'t\<Rightarrow>real"
record ('q,'s,'i,'v) generated_trajectory_data =
  tr_order_domain :: "'q set"
  tr_scalar :: "'q\<Rightarrow>'s"
  tr_real_domain :: "real set"
  tr_order_curve :: "('i\<times>'q)\<Rightarrow>'v"
  tr_real_curve :: "('i\<times>real)\<Rightarrow>'v"

locale native_dynamics_bundle =
  native_law_bundle C D B R Bind source_order U L Q A idx record_map local_values local_obs compare val_range window field sequence +
  observer_real C D B R Bind source_order rho
  for C :: "'c set" and D :: "'d set" and B :: "'b set"
    and R :: "('c\<times>'d\<times>'b)set"
    and Bind :: "(('c\<times>'d\<times>'b)\<times>('c\<times>'d\<times>'b))set"
    and source_order :: "('c\<times>'c)set"
    and U :: "'u set" and L :: "'l set" and Q :: "'i set"
    and A :: "'u\<Rightarrow>'a set" and idx :: "'l\<Rightarrow>'i"
    and record_map :: "'u\<Rightarrow>'a\<Rightarrow>'b"
    and local_values :: "'u\<Rightarrow>'l\<Rightarrow>'w set"
    and local_obs :: "'u\<Rightarrow>'l\<Rightarrow>'a\<Rightarrow>'w"
    and compare :: "'u\<Rightarrow>'l\<Rightarrow>'w\<Rightarrow>'v"
    and val_range :: "'l\<Rightarrow>'v set"
    and window :: "'d\<Rightarrow>'win" and field :: "'d\<Rightarrow>'fld" and sequence :: "'d\<Rightarrow>'seq"
    and rho :: "'c set set\<Rightarrow>real" +
  assumes fiber: fiber_condition
begin
definition time_data where
  "time_data=\<lparr>td_order={(q,r). q\<in>OrderTime \<and> r\<in>OrderTime \<and> order_lt q r},
    td_projection=restrict restricted_projection Time,td_embedding=restrict rho OrderTime,
    td_representation=restrict time_rep Time\<rparr>"
definition time_specification where
  "time_specification(t::('c set,'c set set)generated_time_data) \<longleftrightarrow>
    td_order t={(q,r). q\<in>OrderTime \<and> r\<in>OrderTime \<and> order_lt q r} \<and>
    td_projection t=restrict restricted_projection Time \<and> td_embedding t=restrict rho OrderTime \<and>
    td_representation t\<in>extensional Time \<and>
    (\<forall>x\<in>Time. td_representation t x=td_embedding t(td_projection t x))"
lemma projection_typed:
  "x\<in>Time \<Longrightarrow> restricted_projection x\<in>OrderTime"
  unfolding restricted_projection_def QuSet_def by blast
lemma time_spec: "time_specification time_data"
  using projection_typed unfolding time_specification_def time_data_def time_rep_def restricted_projection_def by auto
lemma time_unique:
  assumes h: "time_specification t"
  shows "t=time_data"
proof -
  have ext: "td_representation t\<in>extensional Time" using h unfolding time_specification_def by blast
  have agree: "\<And>x. x\<in>Time \<Longrightarrow> td_representation t x=time_rep x"
    using h projection_typed unfolding time_specification_def time_rep_def restricted_projection_def by simp
  have rep: "td_representation t=restrict time_rep Time"
    by (rule extensionalityI[OF ext restrict_extensional]) (simp add: agree)
  show ?thesis using h rep unfolding time_specification_def time_data_def by (cases t) auto
qed

definition trajectory_data where
  "trajectory_data=\<lparr>tr_order_domain=order_domain,tr_scalar=restrict scalar_trajectory order_domain,
    tr_real_domain=real_domain,tr_order_curve=restrict (\<lambda>p. order_curve(obs.canonical(fst p))(snd p)) (Q\<times>order_domain),
    tr_real_curve=restrict (\<lambda>p. real_curve(obs.canonical(fst p))(snd p)) (Q\<times>real_domain)\<rparr>"
definition trajectory_specification where
  "trajectory_specification(t::('c set set,'b set,'i,'v)generated_trajectory_data) \<longleftrightarrow>
    tr_order_domain t=order_domain \<and> tr_real_domain t=real_domain \<and>
    tr_scalar t\<in>extensional order_domain \<and>
    tr_order_curve t\<in>extensional(Q\<times>order_domain) \<and>
    tr_real_curve t\<in>extensional(Q\<times>real_domain) \<and>
    (\<forall>x\<in>trajectory_domain. canonical_trajectory x=tr_scalar t(restricted_projection x)) \<and>
    (\<forall>i\<in>Q. \<forall>q\<in>order_domain. tr_order_curve t(i,q)=obs.canonical i(tr_scalar t q)) \<and>
    (\<forall>i\<in>Q. \<forall>q\<in>order_domain. tr_real_curve t(i,rho q)=tr_order_curve t(i,q))"

lemma trajectory_spec: "trajectory_specification trajectory_data"
proof -
  have fac: "\<And>x. x\<in>trajectory_domain \<Longrightarrow> canonical_trajectory x=scalar_trajectory(restricted_projection x)"
    using conjunct1[OF scalar_factor_contract[OF fiber]] by blast
  have proj: "\<And>x. x\<in>trajectory_domain \<Longrightarrow> restricted_projection x\<in>order_domain"
    unfolding order_domain_def by blast
  have img: "\<And>q. q\<in>order_domain \<Longrightarrow> rho q\<in>real_domain"
    unfolding real_domain_def by blast
  show ?thesis using fac proj img
    unfolding trajectory_specification_def trajectory_data_def order_curve_def real_curve_def comp_def
    by (auto simp: real_inverse_left)
qed
lemma trajectory_unique:
  assumes h: "trajectory_specification t"
  shows "t=trajectory_data"
proof -
  have hscalar: "\<forall>x\<in>trajectory_domain. canonical_trajectory x=tr_scalar t(restricted_projection x)"
    using h unfolding trajectory_specification_def by blast
  have es: "\<forall>q\<in>order_domain. tr_scalar t q=scalar_trajectory q"
    by (rule mp[OF HOL.spec[OF conjunct2[OF scalar_factor_contract[OF fiber]]] hscalar])
  have eo: "\<And>i q. i\<in>Q \<Longrightarrow> q\<in>order_domain \<Longrightarrow>
    tr_order_curve t(i,q)=order_curve(obs.canonical i)q"
    using h es unfolding trajectory_specification_def order_curve_def comp_def by simp
  have er: "\<And>i r. i\<in>Q \<Longrightarrow> r\<in>real_domain \<Longrightarrow>
    tr_real_curve t(i,r)=real_curve(obs.canonical i)r"
  proof -
    fix i r assume i: "i\<in>Q" and r: "r\<in>real_domain"
    obtain q where q: "q\<in>order_domain" and rq: "r=rho q" using r unfolding real_domain_def by blast
    have fac: "tr_real_curve t(i,rho q)=tr_order_curve t(i,q)"
      using h i q unfolding trajectory_specification_def by blast
    show "tr_real_curve t(i,r)=real_curve(obs.canonical i)r"
      using fac eo[OF i q] real_inverse_left[OF q] unfolding rq real_curve_def comp_def by simp
  qed
  have scalar: "tr_scalar t=tr_scalar trajectory_data"
    using h es unfolding trajectory_specification_def trajectory_data_def
    by (intro extensionalityI[where A=order_domain]) auto
  have ord: "tr_order_curve t=tr_order_curve trajectory_data"
    using h eo unfolding trajectory_specification_def trajectory_data_def
    by (intro extensionalityI[where A="Q\<times>order_domain"]) auto
  have real: "tr_real_curve t=tr_real_curve trajectory_data"
    using h er unfolding trajectory_specification_def trajectory_data_def
    by (intro extensionalityI[where A="Q\<times>real_domain"]) auto
  show ?thesis using h scalar ord real unfolding trajectory_specification_def trajectory_data_def
    by (cases t) auto
qed

definition description where "description=(law_input,time_data,trajectory_data)"
definition description_specification where
  "description_specification x \<longleftrightarrow>
    law_input_specification(fst x) \<and> time_specification(fst(snd x)) \<and> trajectory_specification(snd(snd x))"
lemma description_spec: "description_specification description"
  unfolding description_specification_def description_def
  using law_input_spec time_spec trajectory_spec by simp
lemma description_unique:
  "description_specification x \<Longrightarrow> x=description"
proof -
  assume h: "description_specification x"
  have a: "fst x=law_input" by (rule law_input_unique) (use h in \<open>simp add: description_specification_def\<close>)
  have b: "fst(snd x)=time_data" by (rule time_unique) (use h in \<open>simp add: description_specification_def\<close>)
  have c: "snd(snd x)=trajectory_data" by (rule trajectory_unique) (use h in \<open>simp add: description_specification_def\<close>)
  show ?thesis using a b c unfolding description_def by (cases x; cases "snd x") auto
qed
lemma description_exists_unique: "\<exists>!x. description_specification x"
  by (rule ex1I[where a=description]) (rule description_spec, rule description_unique, assumption)
definition witness_specification where
  "witness_specification x \<longleftrightarrow>
    law_input_specification(fst x) \<and> description_specification(snd x) \<and> fst x=fst(snd x)"
lemma witness_exists_unique: "\<exists>!x. witness_specification x"
proof (rule ex1I[where a="(law_input,description)"])
  show "witness_specification(law_input,description)"
    using law_input_spec description_spec unfolding witness_specification_def description_def by simp
  fix x assume h: "witness_specification x"
  have a: "fst x=law_input" by (rule law_input_unique) (use h in \<open>auto simp: witness_specification_def\<close>)
  have b: "snd x=description" by (rule description_unique) (use h in \<open>auto simp: witness_specification_def\<close>)
  show "x=(law_input,description)" using a b by (cases x) simp
qed

lemma shared_input_exact:
  assumes i: "i\<in>Q" and x: "x\<in>trajectory_domain"
  shows "bundle_values(bundle_observables(fst description))(i,bundle_trajectory(fst description)x)=
    tr_real_curve(snd(snd description))(i,rho(restricted_projection x))"
proof -
  have s: "canonical_trajectory x\<in>State" using trajectory_map_typed x by blast
  have q: "restricted_projection x\<in>order_domain" using x unfolding order_domain_def by blast
  have r: "rho(restricted_projection x)\<in>real_domain" using q unfolding real_domain_def by blast
  have fac: "obs.canonical i(canonical_trajectory x)=real_curve(obs.canonical i)(rho(restricted_projection x))"
    using bspec[OF conjunct1[OF observable_factorization[OF fiber, of "obs.canonical i"]] x] by simp
  show ?thesis using i x s r fac unfolding description_def law_input_def observable_data_def trajectory_data_def by simp
qed
lemma curve_range_preserved:
  assumes i: "i\<in>Q" and t: "t\<in>real_domain"
  shows "tr_real_curve(snd(snd description))(i,t)\<in>bundle_ranges(bundle_observables(fst description))i"
proof -
  obtain x where x: "x\<in>trajectory_domain" and tx: "t=rho(restricted_projection x)"
    using t unfolding real_domain_def order_domain_def by blast
  have s: "canonical_trajectory x\<in>State" using trajectory_map_typed x by blast
  have fac: "obs.canonical i(canonical_trajectory x)=real_curve(obs.canonical i)t"
    using bspec[OF conjunct1[OF observable_factorization[OF fiber, of "obs.canonical i"]] x] tx by simp
  have typed: "obs.canonical i(canonical_trajectory x)\<in>obs.canonical_range i"
    by (rule canonical_value_typed[OF i s])
  show ?thesis using i t fac typed unfolding description_def law_input_def observable_data_def trajectory_data_def by simp
qed
end
ML \<open>
val roots = @{thms native_dynamics_bundle.time_spec native_dynamics_bundle.time_unique
 native_dynamics_bundle.trajectory_spec native_dynamics_bundle.trajectory_unique
 native_dynamics_bundle.description_spec native_dynamics_bundle.description_unique
 native_dynamics_bundle.description_exists_unique native_dynamics_bundle.witness_exists_unique
 native_dynamics_bundle.shared_input_exact native_dynamics_bundle.curve_range_preserved};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
