theory Core_Local_Jet_Membership_Bridge
  imports LCTR_Core_Native_Differential_Predicates.Core_Native_Differential_Predicates
begin

lemma generated_image_member:
  assumes h2: "native_diff2 N q k" and h3: "native_diff3 N q k Rel"
    and theta: "theta\<in>N"
  shows "F (canonical_pair N q k theta)\<in>F ` Rel"
proof -
  have member: "canonical_pair N q k theta\<in>Rel"
    using diff3_restricts[OF h2] h3 theta by blast
  show ?thesis by (rule imageI[OF member])
qed

ML \<open>
val roots = @{thms generated_image_member};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
