theory Core_Configuration_Dynamics
 imports "LCTR_Core_Operational_Configuration.Core_Operational_Configuration" "HOL-Library.FuncSet"
begin
locale configuration_dynamics =
 fixes raw :: "('z,'s,'t,'l,'c,'d,'o,'m,'v,'rc,'rd,'rb)raw_input"
 and src :: "('cs,'dt,'bt,'cl,'dl,'z,'v,'rc,'rd,'rb)source_data" and node :: 'v
 assumes configuration: "valid_configuration(raw,src)"
 and node: "node\<in>reception_nodes raw"
 and unique: "\<And>r. inj_on (arrival_value(selected_arrival src r node))
   (arrival_domain(selected_arrival src r node))"
begin
abbreviation arr where "arr r \<equiv> selected_arrival src r node"
definition domain_tuples where "domain_tuples=PiE UNIV (\<lambda>r. arrival_domain(arr r))"
definition received_tuples where
 "received_tuples=PiE UNIV (\<lambda>r. arrival_value(arr r) ` arrival_domain(arr r))"
definition receive_tuple where "receive_tuple a=(\<lambda>r. arrival_value(arr r)(a r))"
definition recover_tuple where "recover_tuple a=(\<lambda>r. recovered(arr r)(a r))"
lemma unique_at_image:
 "a\<in>arrival_value(arr r) ` arrival_domain(arr r) \<Longrightarrow> unique_recoverable(arr r)a"
 using unique[of r] by (auto simp: unique_recoverable_def inj_on_def)
lemma recovered_at_image:
 "a\<in>arrival_value(arr r) ` arrival_domain(arr r) \<Longrightarrow>
 recovered(arr r)a\<in>arrival_domain(arr r) \<and> arrival_value(arr r)(recovered(arr r)a)=a"
 by (rule recovered_spec) (rule unique_at_image)
lemma receive_typed: "a\<in>domain_tuples \<Longrightarrow> receive_tuple a\<in>received_tuples"
 by (auto simp: domain_tuples_def received_tuples_def receive_tuple_def PiE_def Pi_def extensional_def)
lemma recover_typed: "a\<in>received_tuples \<Longrightarrow> recover_tuple a\<in>domain_tuples"
 using recovered_at_image
 by (auto simp: domain_tuples_def received_tuples_def recover_tuple_def PiE_def Pi_def extensional_def)
lemma receive_recover: "a\<in>received_tuples \<Longrightarrow> receive_tuple(recover_tuple a)=a"
 using recovered_at_image
 by (auto simp: received_tuples_def receive_tuple_def recover_tuple_def PiE_def Pi_def fun_eq_iff)
lemma recover_receive:
 assumes a: "a\<in>domain_tuples"
 shows "recover_tuple(receive_tuple a)=a"
proof (rule ext)
 fix r
 have dom: "a r\<in>arrival_domain(arr r)" using a by (auto simp: domain_tuples_def PiE_def)
 have uniq: "unique_recoverable(arr r)(arrival_value(arr r)(a r))"
  by (rule unique_at_image) (use dom in auto)
 show "recover_tuple(receive_tuple a)r=a r"
  unfolding recover_tuple_def receive_tuple_def by (rule recover_eq_original[OF dom uniq])
qed
lemma recovered_source_injective: "inj_on recover_tuple received_tuples"
 using receive_recover by (auto simp: inj_on_def) metis
lemma received_body_source_position:
 assumes "a\<in>domain_tuples"
 shows "body_position src (case recover_tuple(receive_tuple a) SBody of
 Inr(Inr b) \<Rightarrow> b | _ \<Rightarrow> undefined)=
 body_position src (case a SBody of Inr(Inr b) \<Rightarrow> b | _ \<Rightarrow> undefined)"
 by (simp only: recover_receive[OF assms])
definition exact_descent where
 "exact_descent R L \<longleftrightarrow> L=receive_tuple ` {a\<in>domain_tuples. a\<in>R}"
lemma exact_descent_pullback:
 assumes d: "exact_descent R L" and a: "a\<in>received_tuples"
 shows "a\<in>L \<longleftrightarrow> recover_tuple a\<in>R"
proof
 assume "a\<in>L"
 then obtain p where p: "p\<in>domain_tuples" "p\<in>R" "a=receive_tuple p"
  using d by (auto simp: exact_descent_def)
 show "recover_tuple a\<in>R" using p recover_receive by simp
next
 assume r: "recover_tuple a\<in>R"
 have dom: "recover_tuple a\<in>domain_tuples" by (rule recover_typed[OF a])
 have "receive_tuple(recover_tuple a)\<in>L" using d dom r by (auto simp: exact_descent_def)
 then show "a\<in>L" by (simp only: receive_recover[OF a])
qed
lemma descent_typed: "exact_descent R L \<Longrightarrow> L\<subseteq>received_tuples"
 using receive_typed by (auto simp: exact_descent_def)
definition source_binding where
 "source_binding L bind s t \<longleftrightarrow>
 (\<exists>a\<in>L. \<exists>b\<in>L. bind a b \<and> recover_tuple a=s \<and> recover_tuple b=t)"
lemma source_binding_typed:
 assumes d: "exact_descent R L" and b: "source_binding L bind s t"
 shows "s\<in>R \<and> t\<in>R"
proof -
 obtain a b where h: "a\<in>L" "b\<in>L" "s=recover_tuple a" "t=recover_tuple b"
  using b by (auto simp: source_binding_def)
 have typed_local: "a\<in>received_tuples" "b\<in>received_tuples" using descent_typed[OF d] h by auto
 show ?thesis using exact_descent_pullback[OF d typed_local(1)] exact_descent_pullback[OF d typed_local(2)] h by auto
qed
lemma source_binding_pullback:
 assumes L: "L\<subseteq>received_tuples" and a: "a\<in>received_tuples" and b: "b\<in>received_tuples"
 shows "source_binding L bind (recover_tuple a)(recover_tuple b) \<longleftrightarrow>
 a\<in>L \<and> b\<in>L \<and> bind a b"
 using L a b recovered_source_injective unfolding source_binding_def inj_on_def by blast
definition generated where
 "generated R L bind r s t \<longleftrightarrow>
 (\<exists>a\<in>R. \<exists>b\<in>R. source_binding L bind a b \<and> a r=s \<and> b r=t)"
lemma generated_is_local_binding_image:
 assumes d: "exact_descent R L"
 shows "generated R L bind r s t \<longleftrightarrow>
 (\<exists>a\<in>L. \<exists>b\<in>L. bind a b \<and> recover_tuple a r=s \<and> recover_tuple b r=t)"
proof
 assume "generated R L bind r s t"
 then show "\<exists>a\<in>L. \<exists>b\<in>L. bind a b \<and> recover_tuple a r=s \<and> recover_tuple b r=t"
  by (auto simp: generated_def source_binding_def)
next
 assume "\<exists>a\<in>L. \<exists>b\<in>L. bind a b \<and> recover_tuple a r=s \<and> recover_tuple b r=t"
 then obtain a b where h: "a\<in>L" "b\<in>L" "bind a b" "recover_tuple a r=s" "recover_tuple b r=t" by blast
 have typed_local: "a\<in>received_tuples" "b\<in>received_tuples" using descent_typed[OF d] h by auto
 have inside: "recover_tuple a\<in>R" "recover_tuple b\<in>R"
  using exact_descent_pullback[OF d typed_local(1)] exact_descent_pullback[OF d typed_local(2)] h by auto
 show "generated R L bind r s t" using inside h by (auto simp: generated_def source_binding_def)
qed
lemma generated_endpoint_arrived:
 assumes d: "exact_descent R L" and g: "generated R L bind r s t"
 shows "s\<in>arrival_domain(arr r) \<and> t\<in>arrival_domain(arr r)"
proof -
 obtain a b where h: "a\<in>L" "b\<in>L" "recover_tuple a r=s" "recover_tuple b r=t"
  using generated_is_local_binding_image[OF d] g by blast
 have typed_local: "a\<in>received_tuples" "b\<in>received_tuples" using descent_typed[OF d] h by auto
 show ?thesis using recover_typed[OF typed_local(1)] recover_typed[OF typed_local(2)] h
  by (auto simp: domain_tuples_def PiE_def Pi_def)
qed
end
ML \<open>
val roots = @{thms configuration_dynamics.receive_recover configuration_dynamics.recover_receive
 configuration_dynamics.recovered_source_injective configuration_dynamics.received_body_source_position
 configuration_dynamics.exact_descent_pullback configuration_dynamics.source_binding_typed
 configuration_dynamics.source_binding_pullback configuration_dynamics.generated_is_local_binding_image
 configuration_dynamics.generated_endpoint_arrived};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
