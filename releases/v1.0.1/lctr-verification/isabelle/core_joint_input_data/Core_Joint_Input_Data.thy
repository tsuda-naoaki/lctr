theory Core_Joint_Input_Data
  imports "HOL-Library.FuncSet"
begin

record ('z,'b,'v) source_data =
  source_domain :: "('z \<Rightarrow> 'b) set"
  source_values :: "'v set"
  source_relation :: "(('z \<Rightarrow> 'b) \<times> 'v) set"

definition source_typed where
  "source_typed Z B d \<longleftrightarrow>
    source_domain d \<subseteq> PiE Z (\<lambda>_. B) \<and>
    source_relation d \<subseteq> source_domain d \<times> source_values d"

definition empty_data where
  "empty_data A V = \<lparr>source_domain=A,source_values=V,source_relation={}\<rparr>"

lemma relation_domain:
  "source_typed Z B d \<Longrightarrow> (x,v)\<in>source_relation d \<Longrightarrow> x\<in>source_domain d"
  by (auto simp: source_typed_def)

lemma source_components:
  "fst (source_domain d,source_relation d)=source_domain d \<and>
   snd (source_domain d,source_relation d)=source_relation d"
  by simp

lemma empty_relation_allowed:
  "source_domain (empty_data A V)=A \<and> source_relation (empty_data A V)={}"
  by (simp add: empty_data_def)

definition predicate_data where
  "predicate_data A P = \<lparr>source_domain=A,source_values={()},
    source_relation=(\<lambda>x. (x,())) ` {x. P x}\<rparr>"

lemma predicate_membership:
  "(x,())\<in>source_relation (predicate_data A P) \<longleftrightarrow> P x"
  by (auto simp: predicate_data_def)

lemma predicate_typed:
  assumes dom: "A\<subseteq>PiE Z (\<lambda>_. B)"
    and pred: "\<And>x. P x\<Longrightarrow>x\<in>A"
  shows "source_typed Z B (predicate_data A P)"
proof -
  have rel: "(\<lambda>x. (x,())) ` {x. P x}\<subseteq>A\<times>{()}"
  proof (rule subsetI)
    fix p assume "p\<in>(\<lambda>x. (x,())) ` {x. P x}"
    then obtain x where px: "p=(x,())" and hx: "P x" by blast
    have "x\<in>A" by (rule pred[OF hx])
    then show "p\<in>A\<times>{()}" using px by auto
  qed
  show ?thesis using dom rel
    by (simp only: source_typed_def predicate_data_def source_data.select_convs; rule conjI; assumption)
qed

lemma predicate_value_unique: "(v::unit)=()" by simp

record ('c,'f,'r,'z,'b,'v) joint_data =
  joint_context :: 'c
  joint_roles :: 'f
  joint_indices :: "'r set"
  joint_datum :: "'r \<Rightarrow> ('z,'b,'v) source_data"

definition assemble where
  "assemble ctx roles indices data = \<lparr>joint_context=ctx,joint_roles=roles,
    joint_indices=indices,joint_datum=data\<rparr>"

definition joint_valid where
  "joint_valid Z B Roles d \<longleftrightarrow>
    joint_roles d\<in>Roles (joint_context d) \<and> joint_indices d\<noteq>{} \<and>
    (\<forall>r\<in>joint_indices d. source_typed Z B (joint_datum d r))"

lemma bundle_context: "joint_context (assemble ctx roles indices data)=ctx"
  by (simp add: assemble_def)
lemma bundle_roles: "joint_roles (assemble ctx roles indices data)=roles"
  by (simp add: assemble_def)
lemma bundle_indices: "joint_indices (assemble ctx roles indices data)=indices"
  by (simp add: assemble_def)
lemma bundle_datum: "joint_datum (assemble ctx roles indices data) r=data r"
  by (simp add: assemble_def)

lemma selected_index_exists:
  "joint_valid Z B Roles d \<Longrightarrow> \<exists>r. r\<in>joint_indices d"
  by (auto simp: joint_valid_def)

lemma indexed_relation_domain:
  "joint_valid Z B Roles d \<Longrightarrow> r\<in>joint_indices d \<Longrightarrow>
    (x,v)\<in>source_relation (joint_datum d r) \<Longrightarrow>
    x\<in>source_domain (joint_datum d r)"
  by (auto simp: joint_valid_def source_typed_def)

lemma empty_value_relation:
  "source_typed Z B d \<Longrightarrow> source_values d={} \<Longrightarrow> source_relation d={}"
  by (auto simp: source_typed_def)

lemma relation_not_forced_total:
  "\<exists>d::(unit,unit,unit) source_data.
    source_typed UNIV UNIV d \<and> source_domain d\<noteq>{} \<and> source_relation d={}"
proof -
  let ?d = "empty_data {\<lambda>_::unit. ()} {()}"
  have "source_typed UNIV UNIV ?d \<and> source_domain ?d\<noteq>{} \<and> source_relation ?d={}"
    by (simp add: source_typed_def empty_data_def PiE_def extensional_def)
  then show ?thesis by blast
qed

ML \<open>
val roots = @{thms relation_domain source_components empty_relation_allowed
  predicate_membership predicate_value_unique bundle_context bundle_roles bundle_indices
  bundle_datum selected_index_exists indexed_relation_domain empty_value_relation relation_not_forced_total};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = List.app (fn th => writeln ("LCTR_ROOT_STATEMENT=" ^ Thm.string_of_thm @{context} th)) roots;
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
