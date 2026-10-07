theory Core_Audit_Tags
  imports "../core_audit_state_transport/Core_Audit_State_Transport"
begin

definition reason_carrier where
  "reason_carrier A = A \<times> {Blocked, Unformed, Indeterminate}"
definition reasons where
  "reasons A s = {p \<in> reason_carrier A. s (fst p) = snd p}"
definition group_reasons where
  "group_reasons A s G = {p \<in> reasons A s. fst p \<in> G}"
definition reason_map where
  "reason_map c = (\<lambda>(a,q). (c a,q))"
definition nonempty_reasons where
  "nonempty_reasons A = {R. R \<subseteq> reason_carrier A \<and> R \<noteq> {}}"
definition tagged_carrier where
  "tagged_carrier Y A = image Inl Y \<union> image Inr (nonempty_reasons A)"
definition tagged where
  "tagged y R = (if R = {} then Inl y else Inr R)"
definition tagged_map where
  "tagged_map v c = case_sum (\<lambda>y. Inl (v y)) (\<lambda>R. Inr (image (reason_map c) R))"

lemma tagged_typed:
  "y \<in> Y \<Longrightarrow> R \<subseteq> reason_carrier A \<Longrightarrow> tagged y R \<in> tagged_carrier Y A"
  by (auto simp: tagged_def tagged_carrier_def nonempty_reasons_def)

lemma tagged_map_typed:
  assumes x: "x \<in> tagged_carrier Y A"
    and val_typed: "\<And>y. y \<in> Y \<Longrightarrow> v y \<in> Z"
    and rea_typed: "\<And>p. p \<in> reason_carrier A \<Longrightarrow> reason_map c p \<in> reason_carrier B"
  shows "tagged_map v c x \<in> tagged_carrier Z B"
proof (cases x)
  case (Inl y)
  have "y \<in> Y" using x Inl by (auto simp: tagged_carrier_def)
  then have "v y \<in> Z" by (rule val_typed)
  then show ?thesis by (simp add: Inl tagged_map_def tagged_carrier_def)
next
  case (Inr R)
  have R: "R \<subseteq> reason_carrier A" "R \<noteq> {}"
    using x Inr by (auto simp: tagged_carrier_def nonempty_reasons_def)
  have sub: "image (reason_map c) R \<subseteq> reason_carrier B"
    using R(1) rea_typed by auto
  have ne: "image (reason_map c) R \<noteq> {}" using R(2) by simp
  have mem: "image (reason_map c) R \<in> nonempty_reasons B"
    using sub ne by (simp add: nonempty_reasons_def)
  have target: "Inr (image (reason_map c) R) \<in> tagged_carrier Z B"
    unfolding tagged_carrier_def by (rule UnI2; rule imageI[OF mem])
  show ?thesis using target by (simp add: Inr tagged_map_def)
qed

locale tag_transport =
  fixes A :: "'a set" and B :: "'b set" and Y :: "'y set" and Z :: "'z set"
    and c :: "'a \<Rightarrow> 'b" and ci :: "'b \<Rightarrow> 'a"
    and v :: "'y \<Rightarrow> 'z" and vi :: "'z \<Rightarrow> 'y"
  assumes c_typed: "\<And>a. a \<in> A \<Longrightarrow> c a \<in> B"
    and ci_typed: "\<And>b. b \<in> B \<Longrightarrow> ci b \<in> A"
    and c_left: "\<And>a. a \<in> A \<Longrightarrow> ci (c a) = a"
    and c_right: "\<And>b. b \<in> B \<Longrightarrow> c (ci b) = b"
    and v_typed: "\<And>y. y \<in> Y \<Longrightarrow> v y \<in> Z"
    and vi_typed: "\<And>z. z \<in> Z \<Longrightarrow> vi z \<in> Y"
    and v_left: "\<And>y. y \<in> Y \<Longrightarrow> vi (v y) = y"
    and v_right: "\<And>z. z \<in> Z \<Longrightarrow> v (vi z) = z"
begin

lemma reason_forward:
  "p \<in> reason_carrier A \<Longrightarrow> reason_map c p \<in> reason_carrier B"
  by (cases p) (auto simp: reason_carrier_def reason_map_def c_typed)
lemma reason_reverse:
  "p \<in> reason_carrier B \<Longrightarrow> reason_map ci p \<in> reason_carrier A"
  by (cases p) (auto simp: reason_carrier_def reason_map_def ci_typed)
lemma reason_left:
  "p \<in> reason_carrier A \<Longrightarrow> reason_map ci (reason_map c p) = p"
  by (cases p) (auto simp: reason_carrier_def reason_map_def c_left)
lemma reason_right:
  "p \<in> reason_carrier B \<Longrightarrow> reason_map c (reason_map ci p) = p"
  by (cases p) (auto simp: reason_carrier_def reason_map_def c_right)
lemma reason_set_left:
  assumes R: "R \<subseteq> reason_carrier A"
  shows "image (reason_map ci) (image (reason_map c) R) = R"
proof -
  have point: "\<And>p. p \<in> R \<Longrightarrow> reason_map ci (reason_map c p) = p"
    using R reason_left by blast
  have "image (\<lambda>p. reason_map ci (reason_map c p)) R = image id R"
    by (rule image_cong) (auto simp: point)
  then show ?thesis by (simp add: image_image)
qed
lemma reason_set_right:
  assumes R: "R \<subseteq> reason_carrier B"
  shows "image (reason_map c) (image (reason_map ci) R) = R"
proof -
  have point: "\<And>p. p \<in> R \<Longrightarrow> reason_map c (reason_map ci p) = p"
    using R reason_right by blast
  have "image (\<lambda>p. reason_map c (reason_map ci p)) R = image id R"
    by (rule image_cong) (auto simp: point)
  then show ?thesis by (simp add: image_image)
qed

lemma tagged_forward:
  assumes x: "x \<in> tagged_carrier Y A"
  shows "tagged_map v c x \<in> tagged_carrier Z B"
  by (rule tagged_map_typed[OF x]; (erule v_typed | erule reason_forward))
lemma tagged_reverse:
  assumes x: "x \<in> tagged_carrier Z B"
  shows "tagged_map vi ci x \<in> tagged_carrier Y A"
  by (rule tagged_map_typed[OF x]; (erule vi_typed | erule reason_reverse))
lemma tagged_left:
  "x \<in> tagged_carrier Y A \<Longrightarrow> tagged_map vi ci (tagged_map v c x) = x"
  unfolding tagged_carrier_def nonempty_reasons_def tagged_map_def
  using v_left reason_set_left by auto
lemma tagged_right:
  "x \<in> tagged_carrier Z B \<Longrightarrow> tagged_map v c (tagged_map vi ci x) = x"
  unfolding tagged_carrier_def nonempty_reasons_def tagged_map_def
  using v_right reason_set_right by auto
lemma tagged_bijection:
  "bij_betw (tagged_map v c) (tagged_carrier Y A) (tagged_carrier Z B)"
proof (unfold bij_betw_def, intro conjI)
  show "inj_on (tagged_map v c) (tagged_carrier Y A)"
    using tagged_left by (metis inj_onI)
  show "image (tagged_map v c) (tagged_carrier Y A) = tagged_carrier Z B"
    using tagged_forward tagged_reverse tagged_right by force
qed

lemma reasons_transport:
  assumes states: "\<And>a. a \<in> A \<Longrightarrow> t (c a) = s a"
  shows "image (reason_map c) (reasons A s) = reasons B t"
proof (rule set_eqI, rule iffI)
  fix p
  assume "p \<in> image (reason_map c) (reasons A s)"
  then obtain a q where aq: "(a,q) \<in> reasons A s" and p: "p = (c a,q)"
    by (auto simp: reason_map_def)
  show "p \<in> reasons B t" using aq c_typed states
    by (auto simp: p reasons_def reason_carrier_def)
next
  fix p
  assume p: "p \<in> reasons B t"
  have rb: "p \<in> reason_carrier B" using p by (simp add: reasons_def)
  have state_inv: "\<And>b. b \<in> B \<Longrightarrow> s (ci b) = t b"
  proof -
    fix b assume b: "b \<in> B"
    have cb: "ci b \<in> A" by (rule ci_typed[OF b])
    have "t (c (ci b)) = s (ci b)" by (rule states[OF cb])
    then show "s (ci b) = t b" by (simp add: c_right[OF b])
  qed
  have src: "reason_map ci p \<in> reasons A s"
    using p ci_typed state_inv
    by (cases p) (auto simp: reasons_def reason_carrier_def reason_map_def)
  have eq: "reason_map c (reason_map ci p) = p" by (rule reason_right[OF rb])
  have mapped: "reason_map c (reason_map ci p) \<in> image (reason_map c) (reasons A s)"
    by (rule imageI[OF src])
  show "p \<in> image (reason_map c) (reasons A s)" using mapped by (simp only: eq)
qed

lemma group_reasons_transport:
  assumes states: "\<And>a. a \<in> A \<Longrightarrow> t (c a) = s a" and G: "G \<subseteq> A"
  shows "image (reason_map c) (group_reasons A s G) = group_reasons B t (image c G)"
proof (rule set_eqI, rule iffI)
  fix p
  assume "p \<in> image (reason_map c) (group_reasons A s G)"
  then obtain a q where aq: "(a,q) \<in> group_reasons A s G" and p: "p = (c a,q)"
    by (auto simp: reason_map_def)
  show "p \<in> group_reasons B t (image c G)" using aq c_typed states
    by (auto simp: p group_reasons_def reasons_def reason_carrier_def)
next
  fix p
  assume p: "p \<in> group_reasons B t (image c G)"
  then obtain a q where a: "a \<in> G" and eq: "p = (c a,q)" and tq: "t (c a) = q"
    and q: "q \<in> {Blocked,Unformed,Indeterminate}"
    by (cases p) (auto simp: group_reasons_def reasons_def reason_carrier_def)
  have aa: "a \<in> A" using a G by blast
  have src: "(a,q) \<in> group_reasons A s G"
    using aa a q tq states[OF aa]
    by (simp add: group_reasons_def reasons_def reason_carrier_def)
  show "p \<in> image (reason_map c) (group_reasons A s G)"
    using src eq by (force simp: reason_map_def)
qed

lemma tagged_transport:
  "tagged_map v c (tagged y R) = tagged (v y) (image (reason_map c) R)"
  by (simp add: tagged_def tagged_map_def)
lemma generated_tagged_transport:
  assumes val_eq: "v y = z" and states: "\<And>a. a \<in> A \<Longrightarrow> t (c a) = s a"
  shows "tagged_map v c (tagged y (reasons A s)) = tagged z (reasons B t)"
proof -
  have rs: "image (reason_map c) (reasons A s) = reasons B t"
    by (rule reasons_transport[where t=t and s=s]; rule states)
  show ?thesis by (simp only: tagged_transport val_eq rs)
qed
end

lemma nonempty_reasons_hide_payload:
  "R \<noteq> {} \<Longrightarrow> tagged y R = tagged z R"
  by (simp add: tagged_def)
lemma empty_reasons_preserve_payload: "tagged y {} = Inl y"
  by (simp add: tagged_def)
lemma no_empty_reason_tag: "R \<in> nonempty_reasons A \<Longrightarrow> R \<noteq> {}"
  by (simp add: nonempty_reasons_def)

ML \<open>
val roots = @{thms tag_transport.reasons_transport tag_transport.group_reasons_transport tag_transport.tagged_transport tag_transport.generated_tagged_transport nonempty_reasons_hide_payload empty_reasons_preserve_payload no_empty_reason_tag};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
