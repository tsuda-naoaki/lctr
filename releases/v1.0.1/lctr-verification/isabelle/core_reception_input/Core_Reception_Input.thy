theory Core_Reception_Input
 imports "LCTR_Core_Operational_Configuration.Core_Operational_Configuration"
begin
fun source_to_base where
 "source_to_base SClock=Clock" | "source_to_base SDetector=Detector" | "source_to_base SBody=Body"
definition comparison_roles where "comparison_roles={SClock,SDetector}"

lemma source_role_exact: "b\<in>range source_to_base \<longleftrightarrow> b\<noteq>Observer"
proof (cases b)
 case Clock
 then show ?thesis by (auto intro: image_eqI[where x=SClock])
next
 case Detector
 then show ?thesis by (auto intro: image_eqI[where x=SDetector])
next
 case Body
 then show ?thesis by (auto intro: image_eqI[where x=SBody])
next
 case Observer
 have absent: "Observer\<notin>range source_to_base"
 proof
  assume "Observer\<in>range source_to_base"
  then obtain r where "Observer=source_to_base r" by auto
  then show False by (cases r) auto
 qed
 with Observer show ?thesis by simp
qed
lemma source_role_injective: "inj source_to_base"
proof (rule injI)
 fix a b
 assume "source_to_base a=source_to_base b"
 then show "a=b" by (cases a; cases b) auto
qed
lemma comparison_role_exact: "r\<in>comparison_roles \<longleftrightarrow> r=SClock \<or> r=SDetector"
 by (simp add: comparison_roles_def)

fun role_space where
 "role_space raw v SClock=Inl ` receive_clock raw v"
| "role_space raw v SDetector=(Inr \<circ> Inl) ` receive_detector raw v"
| "role_space raw v SBody=(Inr \<circ> Inr) ` receive_body raw v"
definition restricted_order where
 "restricted_order raw v r x y \<longleftrightarrow> reception_order raw v x y"
lemma role_space_subset: "role_space raw v r\<subseteq>reception_space raw v"
 by (cases r) (auto simp: reception_space_def)
lemma restriction_exact:
 "restricted_order raw v r x y \<longleftrightarrow> reception_order raw v x y"
 by (rule restricted_order_def)
lemma restriction_partial_order:
 assumes h: "valid_raw raw" and v: "v\<in>reception_nodes raw"
 shows "(\<forall>x\<in>role_space raw v r. restricted_order raw v r x x) \<and>
 (\<forall>x\<in>role_space raw v r. \<forall>y\<in>role_space raw v r. \<forall>z\<in>role_space raw v r.
 restricted_order raw v r x y \<longrightarrow> restricted_order raw v r y z \<longrightarrow> restricted_order raw v r x z) \<and>
 (\<forall>x\<in>role_space raw v r. \<forall>y\<in>role_space raw v r.
 restricted_order raw v r x y \<longrightarrow> restricted_order raw v r y x \<longrightarrow> x=y)"
proof -
 have ambient: "(\<forall>x\<in>reception_space raw v. reception_order raw v x x) \<and>
 (\<forall>x\<in>reception_space raw v. \<forall>y\<in>reception_space raw v. \<forall>z\<in>reception_space raw v.
 reception_order raw v x y \<longrightarrow> reception_order raw v y z \<longrightarrow> reception_order raw v x z) \<and>
 (\<forall>x\<in>reception_space raw v. \<forall>y\<in>reception_space raw v.
 reception_order raw v x y \<longrightarrow> reception_order raw v y x \<longrightarrow> x=y)"
 using h v unfolding valid_raw_def by blast
 show ?thesis using ambient role_space_subset[of raw v r]
   unfolding restricted_order_def by blast
qed
definition total_reception where
 "total_reception raw r={(v,x). v\<in>reception_nodes raw \<and> x\<in>role_space raw v r}"
lemma total_reception_decomposition:
 "z\<in>total_reception raw r \<Longrightarrow> (fst z,snd z)=z"
 by simp
lemma total_reception_distinct_nodes:
 "x\<in>total_reception raw r \<Longrightarrow> y\<in>total_reception raw r \<Longrightarrow> fst x\<noteq>fst y \<Longrightarrow> x\<noteq>y"
 by auto

ML \<open>
val roots = @{thms source_role_exact source_role_injective comparison_role_exact restriction_exact
 restriction_partial_order total_reception_decomposition total_reception_distinct_nodes};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
