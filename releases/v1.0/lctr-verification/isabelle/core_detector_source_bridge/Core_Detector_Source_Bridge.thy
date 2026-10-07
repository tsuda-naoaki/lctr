theory Core_Detector_Source_Bridge
 imports "LCTR_Core_Operational_Configuration.Core_Operational_Configuration"
begin

definition record_identity where
 "record_identity src \<longleftrightarrow>
  inj_on (\<lambda>t. (detector_display src t,record_sequence src t)) (detector_tokens src)"
definition exact_source where
 "exact_source raw src \<longleftrightarrow> valid_source raw src \<and> record_identity src"
definition content_embedding where
 "content_embedding src t=\<lparr>token_identity=detector_display src t,token_sequence=record_sequence src t\<rparr>"

lemma record_identity_exact:
 assumes h: "record_identity src" and x: "x\<in>detector_tokens src" and y: "y\<in>detector_tokens src"
 shows "x=y \<longleftrightarrow> detector_display src x=detector_display src y \<and> record_sequence src x=record_sequence src y"
 using h x y by (auto simp: record_identity_def inj_on_def)

lemma content_embedding_injective:
 "record_identity src \<Longrightarrow> inj_on (content_embedding src) (detector_tokens src)"
 by (auto simp: record_identity_def inj_on_def content_embedding_def)

lemma content_order_exact:
 assumes h: "record_identity src" and x: "x\<in>detector_tokens src" and y: "y\<in>detector_tokens src"
 shows "detector_le (content_embedding src x) (content_embedding src y) \<longleftrightarrow> detector_order src x y"
 using record_identity_exact[OF h x y]
 by (auto simp: detector_le_def content_embedding_def detector_order_exact)

lemma equal_counter_distinct_content:
 assumes h: "record_identity src" and x: "x\<in>detector_tokens src" and y: "y\<in>detector_tokens src"
  and different: "x\<noteq>y" and same: "record_sequence src x=record_sequence src y"
 shows "detector_display src x\<noteq>detector_display src y"
 using record_identity_exact[OF h x y] different same by blast

lemma recovery_preserves_record_content:
 assumes t: "t\<in>arrival_domain(detector_arrival src v)"
  and u: "unique_recoverable(detector_arrival src v)(arrival_value(detector_arrival src v)t)"
 shows "detector_display src (recovered(detector_arrival src v)(arrival_value(detector_arrival src v)t))=detector_display src t \<and>
  record_sequence src (recovered(detector_arrival src v)(arrival_value(detector_arrival src v)t))=record_sequence src t"
 by (simp only: recover_eq_original[OF t u] reflexive)

lemma pairing_retains_identity:
 "exact_source raw src \<Longrightarrow> fst(make raw src)=raw \<and> snd(make raw src)=src \<and> record_identity(snd(make raw src))"
 by (simp add: exact_source_def make_def)

lemma missing_identity_control:
 "\<exists>content::bool\<Rightarrow>unit. \<exists>seq::bool\<Rightarrow>nat.
   False\<noteq>True \<and> content False=content True \<and> seq False=seq True"
 by (rule exI[where x="\<lambda>_. ()"], rule exI[where x="\<lambda>_. 0"]) simp

ML \<open>
val roots = @{thms record_identity_exact content_embedding_injective content_order_exact
 equal_counter_distinct_content recovery_preserves_record_content pairing_retains_identity missing_identity_control};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
