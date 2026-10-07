theory Core_Dynamics_Recovery_Data
  imports "LCTR_Core_Dynamics_Interfaces.Core_Dynamics_Interfaces"
begin

definition valid_recovery where
  "valid_recovery arr rec \<longleftrightarrow> (\<forall>r. \<forall>a\<in>actual_images arr r.
    rec r a\<in>arrival_domain (arr r) \<and> arrival_value (arr r) (rec r a)=a)"

lemma recovery_exists: "\<exists>rec. valid_recovery arr rec"
proof -
  let ?rec = "\<lambda>r a. SOME s. s\<in>arrival_domain (arr r) \<and> arrival_value (arr r) s=a"
  have step: "?rec r a\<in>arrival_domain (arr r) \<and> arrival_value (arr r) (?rec r a)=a"
    if "a\<in>actual_images arr r" for r a
  proof -
    have "\<exists>s. s\<in>arrival_domain (arr r) \<and> arrival_value (arr r) s=a"
      using that by (auto simp only: arrival_image_exact)
    then show ?thesis by (rule someI_ex)
  qed
  have "valid_recovery arr ?rec" using step by (simp add: valid_recovery_def)
  then show ?thesis by blast
qed

definition recover where "recover rec a = (\<lambda>r. rec r (a r))"

lemma recovery_domain:
  "valid_recovery arr rec \<Longrightarrow> a\<in>PiE UNIV (actual_images arr) \<Longrightarrow>
    recover rec a r\<in>arrival_domain (arr r)"
  by (auto simp: valid_recovery_def recover_def PiE_def Pi_def)

lemma recovery_right_inverse:
  "valid_recovery arr rec \<Longrightarrow> a\<in>PiE UNIV (actual_images arr) \<Longrightarrow>
    arrival_value (arr r) (recover rec a r)=a r"
  by (auto simp: valid_recovery_def recover_def PiE_def Pi_def)

lemma recovery_injective:
  assumes vr: "valid_recovery arr rec"
    and aa: "a\<in>PiE UNIV (actual_images arr)"
    and bb: "b\<in>PiE UNIV (actual_images arr)"
    and eq: "recover rec a=recover rec b"
  shows "a=b"
proof (rule ext)
  fix r
  have ar: "arrival_value (arr r) (recover rec a r)=a r"
    by (rule recovery_right_inverse[OF vr aa])
  have br: "arrival_value (arr r) (recover rec b r)=b r"
    by (rule recovery_right_inverse[OF vr bb])
  show "a r=b r" using ar br eq by simp
qed

definition local_binding where
  "local_binding x bind a b \<longleftrightarrow> a\<in>local_relation x \<and> b\<in>local_relation x \<and> bind a b"
definition source_binding where
  "source_binding x rec bind s t \<longleftrightarrow>
    s\<in>source_tuple_relation x \<and> t\<in>source_tuple_relation x \<and>
    (\<exists>a b. local_binding x bind a b \<and> recover rec a=s \<and> recover rec b=t)"

lemma local_binding_exact:
  "local_binding x bind a b \<longleftrightarrow> a\<in>local_relation x \<and> b\<in>local_relation x \<and> bind a b"
  by (simp only: local_binding_def)
lemma source_binding_typed:
  "source_binding x rec bind s t \<Longrightarrow> s\<in>source_tuple_relation x \<and> t\<in>source_tuple_relation x"
  by (simp add: source_binding_def)
lemma source_binding_exact:
  "source_binding x rec bind s t \<longleftrightarrow>
    s\<in>source_tuple_relation x \<and> t\<in>source_tuple_relation x \<and>
    (\<exists>a b. local_binding x bind a b \<and> recover rec a=s \<and> recover rec b=t)"
  by (simp only: source_binding_def)

lemma source_binding_pullback:
  assumes valid: "valid_reception S V x" and vr: "valid_recovery (arrival_family x) rec"
    and aa: "a\<in>PiE UNIV (actual_images (arrival_family x))"
    and bb: "b\<in>PiE UNIV (actual_images (arrival_family x))"
  shows "source_binding x rec bind (recover rec a) (recover rec b) \<longleftrightarrow>
    recover rec a\<in>source_tuple_relation x \<and> recover rec b\<in>source_tuple_relation x \<and>
    local_binding x bind a b"
proof
  assume h: "source_binding x rec bind (recover rec a) (recover rec b)"
  then obtain c d where ht: "recover rec a\<in>source_tuple_relation x" "recover rec b\<in>source_tuple_relation x"
    and cd: "local_binding x bind c d" and ca: "recover rec c=recover rec a" and db: "recover rec d=recover rec b"
    by (auto simp only: source_binding_def)
  have cc: "c\<in>PiE UNIV (actual_images (arrival_family x))"
    and dd: "d\<in>PiE UNIV (actual_images (arrival_family x))"
    using valid cd by (auto simp: valid_reception_def local_binding_def)
  have "c=a" by (rule recovery_injective[OF vr cc aa ca])
  moreover have "d=b" by (rule recovery_injective[OF vr dd bb db])
  ultimately show "recover rec a\<in>source_tuple_relation x \<and> recover rec b\<in>source_tuple_relation x \<and> local_binding x bind a b"
    using ht cd by simp
next
  assume "recover rec a\<in>source_tuple_relation x \<and> recover rec b\<in>source_tuple_relation x \<and> local_binding x bind a b"
  then show "source_binding x rec bind (recover rec a) (recover rec b)"
    unfolding source_binding_def by blast
qed

definition generated where
  "generated x rec bind r s t \<longleftrightarrow> (\<exists>a b. source_binding x rec bind a b \<and> a r=s \<and> b r=t)"
lemma generated_exact:
  "generated x rec bind r s t \<longleftrightarrow>
    (\<exists>a\<in>source_tuple_relation x. \<exists>b\<in>source_tuple_relation x.
      source_binding x rec bind a b \<and> a r=s \<and> b r=t)"
  unfolding generated_def using source_binding_typed by blast

lemma generated_endpoint_arrived:
  assumes valid: "valid_reception S V x" and vr: "valid_recovery (arrival_family x) rec"
    and gen: "generated x rec bind r s t"
  shows "s\<in>arrival_domain (arrival_family x r) \<and> t\<in>arrival_domain (arrival_family x r)"
proof -
  obtain c d where cd: "local_binding x bind c d"
    and cs: "recover rec c r=s" and dt: "recover rec d r=t"
    using gen unfolding generated_def source_binding_def by blast
  have cc: "c\<in>PiE UNIV (actual_images (arrival_family x))"
    and dd: "d\<in>PiE UNIV (actual_images (arrival_family x))"
    using valid cd by (auto simp: valid_reception_def local_binding_def)
  have sc: "recover rec c r\<in>arrival_domain (arrival_family x r)" by (rule recovery_domain[OF vr cc])
  have td: "recover rec d r\<in>arrival_domain (arrival_family x r)" by (rule recovery_domain[OF vr dd])
  show ?thesis using sc td cs dt by simp
qed

definition package where
  "package x rec role bind closure =
    (x,rec,local_binding x bind,source_binding x rec bind,\<lambda>q. (generated x rec bind (role q),closure q))"
lemma package_components:
  "fst (package x rec role bind closure)=x \<and>
   fst (snd (package x rec role bind closure))=rec \<and>
   fst (snd (snd (package x rec role bind closure)))=local_binding x bind \<and>
   fst (snd (snd (snd (package x rec role bind closure))))=source_binding x rec bind \<and>
   snd (snd (snd (snd (package x rec role bind closure))))=(\<lambda>q. (generated x rec bind (role q),closure q))"
  by (simp add: package_def)

lemma right_inverse_not_injectivity:
  "(\<forall>a::unit. (\<lambda>_::bool. ()) ((\<lambda>_::unit. False) a)=a) \<and> \<not>inj (\<lambda>_::bool. ())"
  by (auto simp: inj_def)

ML \<open>
val roots = @{thms recovery_exists recovery_domain recovery_right_inverse recovery_injective
  local_binding_exact source_binding_typed source_binding_exact source_binding_pullback
  generated_exact generated_endpoint_arrived package_components right_inverse_not_injectivity};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = List.app (fn th => writeln ("LCTR_ROOT_STATEMENT=" ^ Thm.string_of_thm @{context} th)) roots;
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
