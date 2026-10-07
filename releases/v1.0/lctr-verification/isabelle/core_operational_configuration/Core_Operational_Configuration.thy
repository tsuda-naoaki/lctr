theory Core_Operational_Configuration
 imports "LCTR_Core_Carrier_Patterns.Core_Carrier_Patterns"
  "LCTR_Core_Source_Recovery.Core_Source_Recovery"
begin
datatype source_role = SClock | SDetector | SBody
record ('z,'s,'t,'l,'c,'d,'o,'m,'v,'rc,'rd,'rb) raw_input =
 raw_abstract :: "('z,'s,'t,'l) carrier_input"
 raw_physical :: "('z,'l,'c,'d,'o,'m) physical_carriers"
 reception_nodes :: "'v set"
 receive_clock :: "'v \<Rightarrow> 'rc set"
 receive_detector :: "'v \<Rightarrow> 'rd set"
 receive_body :: "'v \<Rightarrow> 'rb set"
 reception_carrier :: "'v \<Rightarrow> 'o"
 reception_order :: "'v \<Rightarrow> ('rc + ('rd + 'rb)) \<Rightarrow> ('rc + ('rd + 'rb)) \<Rightarrow> bool"

definition reception_space where
 "reception_space raw v = image Inl(receive_clock raw v) \<union>
  image (Inr \<circ> Inl)(receive_detector raw v) \<union>
  image (Inr \<circ> Inr)(receive_body raw v)"
definition valid_raw where
 "valid_raw raw \<longleftrightarrow> valid_carrier_input(raw_abstract raw) \<and>
  reception_nodes raw\<noteq>{} \<and>
  (\<forall>v\<in>reception_nodes raw.
   reception_carrier raw v \<in> image(realize_observer(raw_physical raw))
     (role_domain(raw_abstract raw) RObserver) \<and>
   (\<forall>x\<in>reception_space raw v. reception_order raw v x x) \<and>
   (\<forall>x\<in>reception_space raw v. \<forall>y\<in>reception_space raw v. \<forall>z\<in>reception_space raw v.
     reception_order raw v x y \<longrightarrow> reception_order raw v y z \<longrightarrow> reception_order raw v x z) \<and>
   (\<forall>x\<in>reception_space raw v. \<forall>y\<in>reception_space raw v.
     reception_order raw v x y \<longrightarrow> reception_order raw v y x \<longrightarrow> x=y))"

record ('cs,'dt,'bt,'cl,'dl,'z,'v,'rc,'rd,'rb) source_data =
 clock_sources :: "'cs set"
 detector_tokens :: "'dt set"
 body_tokens :: "'bt set"
 clock_display :: "'cs clock_token \<Rightarrow> 'cl"
 detector_display :: "'dt \<Rightarrow> 'dl"
 record_sequence :: "'dt \<Rightarrow> nat"
 body_position :: "'bt \<Rightarrow> 'z"
 record_cell :: "'dt \<Rightarrow> 'dt set"
 clock_arrival :: "'v \<Rightarrow> ('cs clock_token,'rc) partial_arrival"
 detector_arrival :: "'v \<Rightarrow> ('dt,'rd) partial_arrival"
 body_arrival :: "'v \<Rightarrow> ('bt,'rb) partial_arrival"
 source_relation :: "('cs clock_token \<times> 'dt) set"
 comparison_relation :: "'v \<Rightarrow> ('rc \<times> 'rd) set"

definition valid_source where
 "valid_source raw src \<longleftrightarrow>
  clock_sources src\<noteq>{} \<and> detector_tokens src\<noteq>{} \<and> body_tokens src\<noteq>{} \<and>
  (\<forall>t\<in>body_tokens src. body_position src t\<in>selected_indices(raw_abstract raw)) \<and>
  (\<forall>t\<in>detector_tokens src.
   finite(record_cell src t) \<and> record_cell src t\<subseteq>detector_tokens src \<and> t\<in>record_cell src t \<and>
   (\<forall>u\<in>detector_tokens src. u\<in>record_cell src t \<longleftrightarrow> record_cell src u=record_cell src t)) \<and>
  source_relation src\<subseteq>(clock_sources src\<times>UNIV)\<times>detector_tokens src \<and>
  (\<forall>v\<in>reception_nodes raw.
   arrival_domain(clock_arrival src v)\<subseteq>clock_sources src\<times>UNIV \<and>
   image(arrival_value(clock_arrival src v))(arrival_domain(clock_arrival src v))\<subseteq>receive_clock raw v \<and>
   arrival_domain(detector_arrival src v)\<subseteq>detector_tokens src \<and>
   image(arrival_value(detector_arrival src v))(arrival_domain(detector_arrival src v))\<subseteq>receive_detector raw v \<and>
   arrival_domain(body_arrival src v)\<subseteq>body_tokens src \<and>
   image(arrival_value(body_arrival src v))(arrival_domain(body_arrival src v))\<subseteq>receive_body raw v \<and>
   comparison_relation src v\<subseteq>receive_clock raw v\<times>receive_detector raw v \<and>
   (\<forall>c\<in>arrival_domain(clock_arrival src v). \<forall>d\<in>arrival_domain(detector_arrival src v).
    (c,d)\<in>source_relation src \<longleftrightarrow>
     (arrival_value(clock_arrival src v)c,arrival_value(detector_arrival src v)d)\<in>comparison_relation src v))"

definition make where "make raw src=(raw,src)"
definition valid_configuration where
 "valid_configuration x \<longleftrightarrow> valid_raw(fst x) \<and> valid_source(fst x)(snd x)"
definition configuration_roles where
 "configuration_roles x i=role_bundle id (component_at(raw_abstract(fst x)))i"
definition configuration_body where
 "configuration_body x i=body_pair(raw_abstract(fst x))i"
definition detector_embedding where
 "detector_embedding src t=\<lparr>token_identity=t,token_sequence=record_sequence src t\<rparr>"
definition detector_order where
 "detector_order src x y \<longleftrightarrow> detector_le(detector_embedding src x)(detector_embedding src y)"
definition clock_order :: "('cs,'dt,'bt,'cl,'dl,'z,'v,'rc,'rd,'rb) source_data \<Rightarrow>
 'cs clock_token \<Rightarrow> 'cs clock_token \<Rightarrow> bool" where
 "clock_order src x y \<longleftrightarrow> family_le x y"

fun selected_arrival where
 "selected_arrival src SClock v =
  \<lparr>arrival_domain=image Inl(arrival_domain(clock_arrival src v)),
   arrival_value=(\<lambda>t. case t of Inl c \<Rightarrow> Inl(arrival_value(clock_arrival src v)c)
    | Inr q \<Rightarrow> undefined)\<rparr>"
| "selected_arrival src SDetector v =
  \<lparr>arrival_domain=image(Inr \<circ> Inl)(arrival_domain(detector_arrival src v)),
   arrival_value=(\<lambda>t. case t of Inl c \<Rightarrow> undefined | Inr q \<Rightarrow>
    (case q of Inl d \<Rightarrow> Inr(Inl(arrival_value(detector_arrival src v)d)) | Inr b \<Rightarrow> undefined))\<rparr>"
| "selected_arrival src SBody v =
  \<lparr>arrival_domain=image(Inr \<circ> Inr)(arrival_domain(body_arrival src v)),
   arrival_value=(\<lambda>t. case t of Inl c \<Rightarrow> undefined | Inr q \<Rightarrow>
    (case q of Inl d \<Rightarrow> undefined | Inr b \<Rightarrow> Inr(Inr(arrival_value(body_arrival src v)b))))\<rparr>"
definition configuration_recovery where
 "configuration_recovery x v r a=recovered(selected_arrival(snd x)r v)a"
definition body_recovery where
 "body_recovery x v a=recovered(body_arrival(snd x)v)a"

lemma detector_order_exact:
 "detector_order src x y \<longleftrightarrow> x=y \<or> record_sequence src x<record_sequence src y"
 by (auto simp: detector_order_def detector_le_def detector_embedding_def)
lemma pairing_preserves_components:
 "fst(make raw src)=raw \<and> snd(make raw src)=src"
 by (simp add: make_def)
lemma pairing_roundtrip: "make(fst x)(snd x)=x"
 by (simp add: make_def)
lemma role_positions_preserved:
 "ri_zeta(bundle_clock(configuration_roles x i))=i \<and>
  ri_zeta(bundle_detector(configuration_roles x i))=i \<and>
  ri_zeta(bundle_body(configuration_roles x i))=i \<and>
  ri_zeta(bundle_observer(configuration_roles x i))=i \<and>
  ri_role(bundle_clock(configuration_roles x i))=Clock \<and>
  ri_role(bundle_detector(configuration_roles x i))=Detector \<and>
  ri_role(bundle_body(configuration_roles x i))=Body \<and>
  ri_role(bundle_observer(configuration_roles x i))=Observer"
 by (simp add: configuration_roles_def role_bundle_def role_instance_def)
lemma receiver_is_realized:
 assumes valid: "valid_configuration x" and v: "v\<in>reception_nodes(fst x)"
 shows "\<exists>i\<in>role_domain(raw_abstract(fst x))RObserver.
   realize_observer(raw_physical(fst x))i=reception_carrier(fst x)v"
proof -
 have raw: "valid_raw(fst x)" using valid by (simp only: valid_configuration_def)
 note all_nodes = conjunct2[OF conjunct2[OF iffD1[OF valid_raw_def raw]]]
 note at_node = bspec[OF all_nodes v]
 have member: "reception_carrier(fst x)v\<in>image(realize_observer(raw_physical(fst x)))
  (role_domain(raw_abstract(fst x))RObserver)" by (rule conjunct1[OF at_node])
 show ?thesis using member by auto
qed
lemma recovery_preserves_arrival:
 assumes "unique_recoverable(selected_arrival(snd x)r v)a"
 shows "configuration_recovery x v r a\<in>arrival_domain(selected_arrival(snd x)r v) \<and>
  arrival_value(selected_arrival(snd x)r v)(configuration_recovery x v r a)=a"
 unfolding configuration_recovery_def by (rule recovered_spec[OF assms])
lemma recovery_returns_original:
 assumes t: "t\<in>arrival_domain(selected_arrival(snd x)r v)"
 and u: "unique_recoverable(selected_arrival(snd x)r v)(arrival_value(selected_arrival(snd x)r v)t)"
 shows "configuration_recovery x v r(arrival_value(selected_arrival(snd x)r v)t)=t"
 unfolding configuration_recovery_def by (rule recover_eq_original[OF t u])
lemma body_recovery_preserves_abstraction_source:
 assumes t: "t\<in>arrival_domain(body_arrival(snd x)v)"
 and u: "unique_recoverable(body_arrival(snd x)v)(arrival_value(body_arrival(snd x)v)t)"
 shows "configuration_body x(body_position(snd x)
  (body_recovery x v(arrival_value(body_arrival(snd x)v)t)))=
  configuration_body x(body_position(snd x)t)"
 unfolding body_recovery_def by (simp only: recover_eq_original[OF t u])
lemma source_comparison_relation_preserved:
 "valid_configuration x \<Longrightarrow> v\<in>reception_nodes(fst x) \<Longrightarrow>
  c\<in>arrival_domain(clock_arrival(snd x)v) \<Longrightarrow>
  d\<in>arrival_domain(detector_arrival(snd x)v) \<Longrightarrow>
  ((c,d)\<in>source_relation(snd x) \<longleftrightarrow>
  (arrival_value(clock_arrival(snd x)v)c,arrival_value(detector_arrival(snd x)v)d)\<in>comparison_relation(snd x)v)"
 by (auto simp: valid_configuration_def valid_source_def)
lemma source_orders_preserved:
 "(\<forall>c d. clock_order(snd x)c d \<longleftrightarrow> fst c=fst d \<and> snd c\<le>snd d) \<and>
  (\<forall>c d. detector_order(snd x)c d \<longleftrightarrow> c=d \<or> record_sequence(snd x)c<record_sequence(snd x)d)"
 by (simp add: clock_order_def family_le_def detector_order_exact)
lemma record_cell_partition_retained:
 assumes valid: "valid_configuration x"
 shows "(\<forall>t\<in>detector_tokens(snd x). finite(record_cell(snd x)t)) \<and>
  (\<forall>t\<in>detector_tokens(snd x). t\<in>record_cell(snd x)t) \<and>
  (\<forall>a\<in>detector_tokens(snd x). \<forall>b\<in>detector_tokens(snd x). \<forall>t.
   t\<in>record_cell(snd x)a \<longrightarrow> t\<in>record_cell(snd x)b \<longrightarrow>
   record_cell(snd x)a=record_cell(snd x)b)"
proof -
 have cells: "\<And>t. t\<in>detector_tokens(snd x) \<Longrightarrow>
  finite(record_cell(snd x)t) \<and> record_cell(snd x)t\<subseteq>detector_tokens(snd x) \<and>
  t\<in>record_cell(snd x)t \<and>
  (\<forall>u\<in>detector_tokens(snd x). u\<in>record_cell(snd x)t \<longleftrightarrow> record_cell(snd x)u=record_cell(snd x)t)"
  using valid unfolding valid_configuration_def valid_source_def by auto
 have equal: "\<And>a b t. a\<in>detector_tokens(snd x) \<Longrightarrow> b\<in>detector_tokens(snd x) \<Longrightarrow>
  t\<in>record_cell(snd x)a \<Longrightarrow> t\<in>record_cell(snd x)b \<Longrightarrow>
  record_cell(snd x)a=record_cell(snd x)b"
 proof -
  fix a b t assume a: "a\<in>detector_tokens(snd x)" and b: "b\<in>detector_tokens(snd x)"
   and ta: "t\<in>record_cell(snd x)a" and tb: "t\<in>record_cell(snd x)b"
  have t: "t\<in>detector_tokens(snd x)" using cells[OF a] ta by auto
  show "record_cell(snd x)a=record_cell(snd x)b" using cells[OF a] cells[OF b] t ta tb by auto
 qed
 show ?thesis using cells equal by blast
qed
lemma equal_display_retains_source_incomparability:
 "fst c\<noteq>fst d \<Longrightarrow> clock_display(snd x)c=clock_display(snd x)d \<Longrightarrow>
  \<not>clock_order(snd x)c d \<and> \<not>clock_order(snd x)d c"
 by (simp add: clock_order_def c_distinct_sources_incomparable)

lemma tagged_body_recovery:
 assumes t: "t\<in>arrival_domain(body_arrival src v)"
 and u: "unique_recoverable(body_arrival src v)(arrival_value(body_arrival src v)t)"
 shows "recovered(selected_arrival src SBody v)
  (Inr(Inr(arrival_value(body_arrival src v)t)))=Inr(Inr t)"
proof -
 have unique: "unique_recoverable(selected_arrival src SBody v)
   (Inr(Inr(arrival_value(body_arrival src v)t)))"
  using t u unfolding unique_recoverable_def by auto
 have dom: "Inr(Inr t)\<in>arrival_domain(selected_arrival src SBody v)" using t by auto
 have arrival_eq: "arrival_value(selected_arrival src SBody v)(Inr(Inr t))=
  Inr(Inr(arrival_value(body_arrival src v)t))" by simp
 have unique_value: "unique_recoverable(selected_arrival src SBody v)
  (arrival_value(selected_arrival src SBody v)(Inr(Inr t)))" using unique by (simp only: arrival_eq)
 show ?thesis using recover_eq_original[OF dom unique_value] by (simp only: arrival_eq)
qed
ML \<open>
val roots = @{thms detector_order_exact pairing_preserves_components pairing_roundtrip role_positions_preserved receiver_is_realized recovery_preserves_arrival recovery_returns_original body_recovery_preserves_abstraction_source source_comparison_relation_preserved source_orders_preserved record_cell_partition_retained equal_display_retains_source_incomparability};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = if null (Thm_Deps.all_oracles @{thms tagged_body_recovery}) then () else error "Unexpected helper oracle dependency";
\<close>
end
