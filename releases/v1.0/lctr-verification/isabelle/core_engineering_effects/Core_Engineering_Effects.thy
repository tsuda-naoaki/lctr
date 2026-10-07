theory Core_Engineering_Effects
  imports "LCTR_Core_Finite_Audit.Core_Finite_Audit"
begin

datatype flag = MissingField | Provenance | RecordCell | ExternalTime | Nonmonotone
  | UncertaintyOverlap | ContractVersion | SolverFailure | DataGap
datatype effect = FormEffect | EvaluationEffect | ExactEvidence | Admissibility | Boundary
datatype boundary_method = Envelope | Partition | MethodUnformed

fun allowed where
  "allowed MissingField e = (e=FormEffect \<or> e=EvaluationEffect)"
| "allowed DataGap e = (e=FormEffect \<or> e=EvaluationEffect)"
| "allowed Provenance e = (e=EvaluationEffect)"
| "allowed UncertaintyOverlap e = (e=EvaluationEffect)"
| "allowed ContractVersion e = (e=EvaluationEffect)"
| "allowed RecordCell e = (e=FormEffect \<or> e=ExactEvidence)"
| "allowed ExternalTime e = (e=Admissibility)"
| "allowed Nonmonotone e = (e=Boundary)"
| "allowed SolverFailure e = (e=EvaluationEffect \<or> e=ExactEvidence)"

record ('r,'e,'b) eng_input =
  formed :: "token \<Rightarrow> bool"
  evaluated :: "token \<Rightarrow> bool"
  condition :: "token \<Rightarrow> bool"
  flags :: "flag set"
  refs :: "flag \<Rightarrow> 'r set"
  evidence_type :: "token \<Rightarrow> 'e set"
  provided :: "token \<Rightarrow> 'e set"
  exact_needed :: "token \<Rightarrow> 'e \<Rightarrow> bool"
  external :: "'r set"
  premise_at :: "'r \<Rightarrow> token \<Rightarrow> bool"
  method :: "'r \<Rightarrow> boundary_method"
  payload_type :: "'r \<Rightarrow> boundary_method \<Rightarrow> 'b set"
  component :: "token \<Rightarrow> 'r \<Rightarrow> boundary_method \<Rightarrow> 'b \<Rightarrow> 'e"
  boundary_needed :: "token \<Rightarrow> 'r \<Rightarrow> bool"

record candidate =
  flag_of :: flag
  effect_of :: effect
  target :: token

definition input_typed where
  "input_typed d \<longleftrightarrow>
    (\<forall>f\<in>flags d. refs d f \<noteq> {}) \<and>
    (\<forall>t\<in>tokens. provided d t \<subseteq> evidence_type d t) \<and>
    (\<forall>t\<in>tokens. \<forall>r m b. b\<in>payload_type d r m \<longrightarrow>
      component d t r m b \<in> evidence_type d t)"

definition candidate_valid where
  "candidate_valid d c \<longleftrightarrow> flag_of c \<in> flags d \<and>
    allowed (flag_of c) (effect_of c) \<and> target c \<in> tokens"

definition effect_meaning where
  "effect_meaning d c \<longleftrightarrow> (case effect_of c of
    FormEffect \<Rightarrow> \<not> formed d (target c)
  | EvaluationEffect \<Rightarrow> \<not> evaluated d (target c)
  | ExactEvidence \<Rightarrow> (\<exists>a\<in>provided d (target c). exact_needed d (target c) a)
  | Admissibility \<Rightarrow> (\<exists>r\<in>refs d (flag_of c).
      r\<in>external d \<and> premise_at d r (target c))
  | Boundary \<Rightarrow> fst (target c)=3 \<and> (\<forall>r\<in>refs d (flag_of c).
      boundary_needed d (target c) r \<and> (case method d r of
        MethodUnformed \<Rightarrow> \<not> evaluated d (target c)
      | Envelope \<Rightarrow> (\<exists>b\<in>payload_type d r Envelope.
          component d (target c) r Envelope b \<in> provided d (target c))
      | Partition \<Rightarrow> (\<exists>b\<in>payload_type d r Partition.
          component d (target c) r Partition b \<in> provided d (target c)))))"

definition verified where
  "verified d coherent supported c \<longleftrightarrow> candidate_valid d c \<and>
    coherent c \<and> supported c \<and> effect_meaning d c"

lemma verified_has_reference:
  "input_typed d \<Longrightarrow> verified d coherent supported c \<Longrightarrow>
    refs d (flag_of c) \<noteq> {} \<and> supported c"
  unfolding input_typed_def verified_def candidate_valid_def by blast

lemma form_effect_actual:
  "verified d coherent supported c \<Longrightarrow> effect_of c=FormEffect \<Longrightarrow>
    \<not> formed d (target c)"
  unfolding verified_def effect_meaning_def by simp

lemma evaluation_effect_actual:
  "verified d coherent supported c \<Longrightarrow> effect_of c=EvaluationEffect \<Longrightarrow>
    \<not> evaluated d (target c)"
  unfolding verified_def effect_meaning_def by simp

lemma exact_requirement_component:
  "verified d coherent supported c \<Longrightarrow> effect_of c=ExactEvidence \<Longrightarrow>
    \<exists>a\<in>provided d (target c). exact_needed d (target c) a"
  unfolding verified_def effect_meaning_def by simp

lemma admissibility_actual_site:
  "verified d coherent supported c \<Longrightarrow> effect_of c=Admissibility \<Longrightarrow>
    \<exists>r\<in>refs d (flag_of c). r\<in>external d \<and> premise_at d r (target c)"
  unfolding verified_def effect_meaning_def by simp

lemma boundary_target_and_need:
  "verified d coherent supported c \<Longrightarrow> effect_of c=Boundary \<Longrightarrow>
    fst (target c)=3 \<and> (\<forall>r\<in>refs d (flag_of c). boundary_needed d (target c) r)"
  unfolding verified_def effect_meaning_def by auto

lemma envelope_component:
  "verified d coherent supported c \<Longrightarrow> effect_of c=Boundary \<Longrightarrow>
    r\<in>refs d (flag_of c) \<Longrightarrow> method d r=Envelope \<Longrightarrow>
    \<exists>b\<in>payload_type d r Envelope.
      component d (target c) r Envelope b \<in> provided d (target c)"
  unfolding verified_def effect_meaning_def by auto

lemma partition_component:
  "verified d coherent supported c \<Longrightarrow> effect_of c=Boundary \<Longrightarrow>
    r\<in>refs d (flag_of c) \<Longrightarrow> method d r=Partition \<Longrightarrow>
    \<exists>b\<in>payload_type d r Partition.
      component d (target c) r Partition b \<in> provided d (target c)"
  unfolding verified_def effect_meaning_def by auto

lemma unformed_boundary_input:
  "verified d coherent supported c \<Longrightarrow> effect_of c=Boundary \<Longrightarrow>
    r\<in>refs d (flag_of c) \<Longrightarrow> method d r=MethodUnformed \<Longrightarrow>
    fst (target c)=3 \<and> \<not> evaluated d (target c)"
  unfolding verified_def effect_meaning_def by auto

definition target_set where
  "target_set d coherent supported = {t. \<exists>c. verified d coherent supported c \<and> target c=t}"

lemma targets_stay_within_six_series:
  "t\<in>target_set d coherent supported \<Longrightarrow>
    t\<in>tokens \<and> (\<exists>!i. i<6 \<and> fst t=i)"
  unfolding target_set_def verified_def candidate_valid_def tokens_def by auto

lemma missing_formation_is_unformed:
  assumes v: "verified d coherent supported c" and e: "effect_of c=FormEffect"
  shows "run (formed d) (evaluated d) (condition d) 40 (target c)=NotFormed"
proof -
  have t: "target c\<in>tokens" using v unfolding verified_def candidate_valid_def by simp
  have eq: "run (formed d) (evaluated d) (condition d) 40 (target c) =
    step (formed d) (evaluated d) (condition d)
      (run (formed d) (evaluated d) (condition d) 40) (target c)"
    using finite_run_solves[of "formed d" "evaluated d" "condition d"] t
    unfolding recurs_def by blast
  show ?thesis using eq form_effect_actual[OF v e]
    unfolding step_def state_def by simp
qed

lemma missing_evaluation_is_not_failed:
  assumes v: "verified d coherent supported c" and e: "effect_of c=EvaluationEffect"
  shows "run (formed d) (evaluated d) (condition d) 40 (target c)\<noteq>Failed"
proof -
  have t: "target c\<in>tokens" using v unfolding verified_def candidate_valid_def by simp
  have eq: "run (formed d) (evaluated d) (condition d) 40 (target c) =
    step (formed d) (evaluated d) (condition d)
      (run (formed d) (evaluated d) (condition d) 40) (target c)"
    using finite_run_solves[of "formed d" "evaluated d" "condition d"] t
    unfolding recurs_def by blast
  show ?thesis using eq evaluation_effect_actual[OF v e]
    unfolding step_def state_def by (auto split: if_splits)
qed

definition example_input :: "(unit,unit,unit) eng_input" where
  "example_input = \<lparr>formed=(\<lambda>_. True), evaluated=(\<lambda>_. True), condition=(\<lambda>_. True),
    flags={SolverFailure}, refs=(\<lambda>_. UNIV), evidence_type=(\<lambda>_. UNIV),
    provided=(\<lambda>_. UNIV), exact_needed=(\<lambda>_ _. True),
    external={}, premise_at=(\<lambda>_ _. False), method=(\<lambda>_. MethodUnformed),
    payload_type=(\<lambda>_ _. UNIV), component=(\<lambda>_ _ _ _. ()),
    boundary_needed=(\<lambda>_ _. False)\<rparr>"
definition example_candidate where
  "example_candidate = \<lparr>flag_of=SolverFailure, effect_of=ExactEvidence, target=(0,1)\<rparr>"

lemma requirement_need_not_fail:
  "input_typed example_input \<and>
    verified example_input (\<lambda>_. True) (\<lambda>_. True) example_candidate \<and>
    (\<forall>t\<in>tokens. run (formed example_input) (evaluated example_input)
      (condition example_input) 40 t=SAT)"
proof -
  have typed: "input_typed example_input"
    by (simp add: input_typed_def example_input_def)
  have ver: "verified example_input (\<lambda>_. True) (\<lambda>_. True) example_candidate"
    by (simp add: verified_def candidate_valid_def effect_meaning_def
      example_candidate_def example_input_def tokens_def count_def)
  have rec: "recurs (formed example_input) (evaluated example_input)
    (condition example_input) (\<lambda>_. SAT)"
    by (simp add: recurs_def step_def state_def predPass_def example_input_def)
  have pass: "run (formed example_input) (evaluated example_input)
    (condition example_input) 40 t=SAT" if "t\<in>tokens" for t
    using finite_run_unique[OF rec that] by simp
  show ?thesis using typed ver pass by blast
qed

ML \<open>
val roots = @{thms verified_has_reference form_effect_actual evaluation_effect_actual
  exact_requirement_component admissibility_actual_site boundary_target_and_need
  envelope_component partition_component unformed_boundary_input targets_stay_within_six_series
  missing_formation_is_unformed missing_evaluation_is_not_failed requirement_need_not_fail};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end

