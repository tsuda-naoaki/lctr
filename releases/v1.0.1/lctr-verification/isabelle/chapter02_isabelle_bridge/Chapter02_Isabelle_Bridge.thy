theory Chapter02_Isabelle_Bridge
  imports Main
begin

datatype role = Clock | Detector | Body | Observer

datatype realization_role = RClock | RDetector | RObserver

fun role_of_realization :: "realization_role \<Rightarrow> role" where
  "role_of_realization RClock = Clock"
| "role_of_realization RDetector = Detector"
| "role_of_realization RObserver = Observer"

lemma realization_role_cases:
  "role_of_realization rr = Clock \<or>
   role_of_realization rr = Detector \<or>
   role_of_realization rr = Observer"
  by (cases rr) auto

lemma realization_role_not_body:
  "role_of_realization rr \<noteq> Body"
  by (cases rr) auto

record ('z, 'c) role_instance =
  ri_role :: role
  ri_zeta :: 'z
  ri_component :: 'c

definition role_instance ::
  "('z \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> role \<Rightarrow> 'c) \<Rightarrow> role \<Rightarrow> 'z \<Rightarrow> ('z, 'c) role_instance"
where
  "role_instance assign label r z =
    \<lparr> ri_role = r,
      ri_zeta = z,
      ri_component = label (assign z) r \<rparr>"

lemma role_instance_eq_iff_index_eq:
  "role_instance assign label r z1 = role_instance assign label r z2
   \<longleftrightarrow> z1 = z2"
  by (auto simp: role_instance_def)

record ('z, 'c) role_bundle =
  bundle_clock :: "('z, 'c) role_instance"
  bundle_detector :: "('z, 'c) role_instance"
  bundle_body :: "('z, 'c) role_instance"
  bundle_observer :: "('z, 'c) role_instance"

definition role_bundle ::
  "('z \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> role \<Rightarrow> 'c) \<Rightarrow> 'z \<Rightarrow> ('z, 'c) role_bundle"
where
  "role_bundle assign label z =
    \<lparr> bundle_clock = role_instance assign label Clock z,
      bundle_detector = role_instance assign label Detector z,
      bundle_body = role_instance assign label Body z,
      bundle_observer = role_instance assign label Observer z \<rparr>"

definition ri_family ::
  "('z \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> role \<Rightarrow> 'c) \<Rightarrow> 'z set
   \<Rightarrow> ('z \<times> ('z, 'c) role_bundle) set"
where
  "ri_family assign label Z0 =
    {(z, role_bundle assign label z) | z. z \<in> Z0}"

lemma ri_family_preserves_index_and_role_positions:
  assumes "z \<in> Z0"
  shows
    "(z, role_bundle assign label z) \<in> ri_family assign label Z0 \<and>
     ri_zeta (bundle_clock (role_bundle assign label z)) = z \<and>
     ri_zeta (bundle_detector (role_bundle assign label z)) = z \<and>
     ri_zeta (bundle_body (role_bundle assign label z)) = z \<and>
     ri_zeta (bundle_observer (role_bundle assign label z)) = z \<and>
     ri_role (bundle_clock (role_bundle assign label z)) = Clock \<and>
     ri_role (bundle_detector (role_bundle assign label z)) = Detector \<and>
     ri_role (bundle_body (role_bundle assign label z)) = Body \<and>
     ri_role (bundle_observer (role_bundle assign label z)) = Observer"
  using assms
  by (simp add: ri_family_def role_bundle_def role_instance_def)

lemma body_abstraction_source_preserved:
  assumes "z \<in> Z0"
      and "body_source (assign z) (label (assign z) Body)"
  shows
    "(z, role_bundle assign label z) \<in> ri_family assign label Z0 \<and>
     body_source (assign z) (label (assign z) Body)"
  using assms
  by (simp add: ri_family_def)

definition realization_input ::
  "('z \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> role \<Rightarrow> 'c) \<Rightarrow> 'z set
   \<Rightarrow> ('z, 'c) role_instance set"
where
  "realization_input assign label Z0 =
    {role_instance assign label (role_of_realization rr) z
      | z rr. z \<in> Z0}"

lemma realization_input_excludes_body:
  assumes "ri \<in> realization_input assign label Z0"
  shows "ri_role ri \<noteq> Body"
  using assms realization_role_not_body
  by (auto simp: realization_input_def role_instance_def)

record ('z, 'c, 'p) physical_realization =
  realization_domain :: "('z, 'c) role_instance set"
  realization_payload :: 'p

definition valid_physical_realization ::
  "('z \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> role \<Rightarrow> 'c) \<Rightarrow> 'z set
   \<Rightarrow> ('z, 'c, 'p) physical_realization \<Rightarrow> bool"
where
  "valid_physical_realization assign label Z0 p
   \<longleftrightarrow> realization_domain p = realization_input assign label Z0"

record ('z, 'c, 'p) realized_extension =
  extension_base :: "('z \<times> ('z, 'c) role_bundle) set"
  extension_realization :: "('z, 'c, 'p) physical_realization"

definition attach_realization ::
  "('z \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> role \<Rightarrow> 'c) \<Rightarrow> 'z set
   \<Rightarrow> ('z, 'c, 'p) physical_realization
   \<Rightarrow> ('z, 'c, 'p) realized_extension"
where
  "attach_realization assign label Z0 p =
    \<lparr> extension_base = ri_family assign label Z0,
      extension_realization = p \<rparr>"

lemma realization_is_additional_and_preserves_existing_ri:
  assumes "valid_physical_realization assign label Z0 p"
  shows
    "extension_base (attach_realization assign label Z0 p)
       = ri_family assign label Z0 \<and>
     realization_domain
       (extension_realization (attach_realization assign label Z0 p))
       = realization_input assign label Z0"
  using assms
  by (simp add: attach_realization_def valid_physical_realization_def)

record 'z construction_input =
  admissible_index :: "'z set"

definition synthesize ::
  "('z \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> role \<Rightarrow> 'c) \<Rightarrow> 'z construction_input
   \<Rightarrow> ('z \<times> ('z, 'c) role_bundle) set"
where
  "synthesize assign label input =
    ri_family assign label (admissible_index input)"

lemma section2_synthesis_preserves_positions:
  assumes "z \<in> admissible_index input"
  shows
    "(z, role_bundle assign label z) \<in> synthesize assign label input \<and>
     ri_zeta (bundle_clock (role_bundle assign label z)) = z \<and>
     ri_zeta (bundle_detector (role_bundle assign label z)) = z \<and>
     ri_zeta (bundle_body (role_bundle assign label z)) = z \<and>
     ri_zeta (bundle_observer (role_bundle assign label z)) = z \<and>
     ri_role (bundle_clock (role_bundle assign label z)) = Clock \<and>
     ri_role (bundle_detector (role_bundle assign label z)) = Detector \<and>
     ri_role (bundle_body (role_bundle assign label z)) = Body \<and>
     ri_role (bundle_observer (role_bundle assign label z)) = Observer"
  using assms
  by (simp add: synthesize_def ri_family_def role_bundle_def role_instance_def)

lemma section2_synthesis_body_source:
  assumes "z \<in> admissible_index input"
      and "body_source (assign z) (label (assign z) Body)"
  shows
    "(z, role_bundle assign label z) \<in> synthesize assign label input \<and>
     body_source (assign z) (label (assign z) Body)"
  using assms
  by (simp add: synthesize_def ri_family_def)

lemma section2_synthesis_realization_domain:
  assumes "z \<in> admissible_index input"
  shows
    "role_instance assign label (role_of_realization rr) z
       \<in> realization_input assign label (admissible_index input) \<and>
     ri_role (role_instance assign label (role_of_realization rr) z)
       = role_of_realization rr \<and>
     role_of_realization rr \<noteq> Body"
  using assms realization_role_not_body
  by (auto simp: realization_input_def role_instance_def)

end
