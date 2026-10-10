theory Core_Communication_Data_Interfaces
  imports "../core_engineering_data_interfaces/Core_Engineering_Data_Interfaces"
begin

record ('v,'e) comm_graph =
  vertices :: "'v set"
  edges :: "'e set"
  src :: "'e \<Rightarrow> 'v"
  tgt :: "'e \<Rightarrow> 'v"
definition graph_typed where
  "graph_typed g = (finite (vertices g) \<and> finite (edges g) \<and>
    (\<forall>e\<in>edges g. src g e\<in>vertices g \<and> tgt g e\<in>vertices g))"
definition walk :: "('v,'e) comm_graph \<Rightarrow> nat \<Rightarrow> (nat\<Rightarrow>'e) \<Rightarrow> bool" where
  "walk g n es = (0<n \<and> (\<forall>i<n. es i\<in>edges g) \<and>
    (\<forall>i. i+1<n \<longrightarrow> tgt g (es i)=src g (es (i+1))))"
definition first where "first g es=src g (es 0)"
definition last where "last g n es=tgt g (es (n-1))"
definition closed where "closed g n es=(walk g n es \<and> first g es=last g n es)"
definition reachable where
  "reachable g v u = (\<exists>n es. walk g n es \<and> first g es=v \<and> last g n es=u)"
definition linked where "linked g v u=(reachable g v u \<or> reachable g u v)"

lemma finite_graph: "graph_typed g \<Longrightarrow> finite (vertices g) \<and> finite (edges g)"
  by (simp add: graph_typed_def)
lemma walk_positive: "walk g n es \<Longrightarrow> 0<n"
  by (simp add: walk_def)
lemma walk_adjacent:
  "walk g n es \<Longrightarrow> i+1<n \<Longrightarrow> tgt g (es i)=src g (es (i+1))"
  by (simp add: walk_def)
lemma walk_endpoints:
  assumes g: "graph_typed g" and w: "walk g n es"
  shows "first g es\<in>vertices g \<and> last g n es\<in>vertices g"
proof -
  have pos: "0<n" using w by (simp add: walk_def)
  have bounds: "n-1<n" using pos by arith
  have endpoints: "es 0\<in>edges g \<and> es (n-1)\<in>edges g"
    using w pos bounds unfolding walk_def by blast
  show ?thesis using g endpoints unfolding graph_typed_def first_def last_def by blast
qed
lemma closed_exact:
  "walk g n es \<Longrightarrow> closed g n es = (first g es=last g n es)"
  by (simp add: closed_def)
lemma linked_exact:
  "linked g v u = (\<exists>n es. walk g n es \<and>
    ((first g es=v \<and> last g n es=u) \<or> (first g es=u \<and> last g n es=v)))"
  unfolding linked_def reachable_def by blast
lemma linked_symmetric: "linked g v u=linked g u v"
  unfolding linked_def by blast
lemma linked_vertices:
  "graph_typed g \<Longrightarrow> linked g v u \<Longrightarrow> v\<in>vertices g \<and> u\<in>vertices g"
  using walk_endpoints unfolding linked_def reachable_def by blast
lemma single_edge_links:
  assumes e: "e\<in>edges g"
  shows "linked g (src g e) (tgt g e)"
proof -
  have w: "walk g 1 (\<lambda>_. e)" using e by (simp add: walk_def)
  have r: "reachable g (src g e) (tgt g e)"
    unfolding reachable_def using w by (auto simp: first_def last_def)
  show ?thesis using r by (simp add: linked_def)
qed
lemma empty_edges_no_links:
  assumes e: "edges g={}"
  shows "\<not>linked g v u"
proof
  assume "linked g v u"
  then obtain n es where w: "walk g n es" unfolding linked_exact by blast
  have "es 0\<in>edges g" using w unfolding walk_def by blast
  with e show False by simp
qed
lemma one_way_is_sufficient:
  "reachable g v u \<Longrightarrow> \<not>reachable g u v \<Longrightarrow>
    linked g v u \<and> \<not>(reachable g v u \<and> reachable g u v)"
  by (simp add: linked_def)

datatype edge_kind = SourceId | Transport
record 'e comm_metric =
  distance :: "'e\<Rightarrow>(ereal\<times>ereal)"
  delay :: "'e\<Rightarrow>(ereal\<times>ereal)"
  loss :: "'e\<Rightarrow>(real\<times>real)"
  bandwidth :: "'e\<Rightarrow>(ereal\<times>ereal)"
  jitter :: "'e\<Rightarrow>(ereal\<times>ereal)"
  integrity :: "'e\<Rightarrow>(real\<times>real)"
definition metric_typed where
  "metric_typed m = (\<forall>e.
    distance m e\<in>closed_intervals {x. 0\<le>x} \<and>
    delay m e\<in>closed_intervals {x. 0\<le>x} \<and>
    loss m e\<in>closed_intervals {x. 0\<le>x \<and> x\<le>1} \<and>
    bandwidth m e\<in>closed_intervals {x. 0\<le>x} \<and>
    jitter m e\<in>closed_intervals {x. 0\<le>x} \<and>
    integrity m e\<in>closed_intervals {x. 0\<le>x \<and> x\<le>1})"
record ('e,'p,'wc,'wd) comm_data =
  carrier :: "'e\<Rightarrow>'p"
  edge_type :: "'e\<Rightarrow>edge_kind"
  wordC :: "(nat\<times>(nat\<Rightarrow>'e))\<Rightarrow>'wc option"
  wordD :: "(nat\<times>(nat\<Rightarrow>'e))\<Rightarrow>'wd option"
  metric :: "'e comm_metric"
definition words_typed where
  "words_typed g d = ((\<forall>n es. \<not>walk g n es \<longrightarrow>
    wordC d (n,es)=None \<and> wordD d (n,es)=None) \<and>
    (\<forall>n es fs. (\<forall>i<n. es i=fs i) \<longrightarrow>
      wordC d (n,es)=wordC d (n,fs) \<and> wordD d (n,es)=wordD d (n,fs)))"
definition word_domain where "word_domain f = {w. \<exists>x. f w=Some x}"
lemma word_domain_exact: "w\<in>word_domain (wordC d) = (\<exists>x. wordC d w=Some x)"
  by (simp add: word_domain_def)
lemma absent_word_allowed: "w\<notin>word_domain (\<lambda>_. None)"
  by (simp add: word_domain_def)
lemma word_single_valued:
  "wordC d w=Some x \<Longrightarrow> wordC d w=Some y \<Longrightarrow> x=y"
  by simp
lemma probability_bounds: "(x::real)\<in>{x. 0\<le>x \<and> x\<le>1} \<Longrightarrow> 0\<le>x \<and> x\<le>1"
  by simp
lemma metric_intervals:
  "metric_typed m \<Longrightarrow>
    fst (distance m e)\<le>snd (distance m e) \<and>
    fst (delay m e)\<le>snd (delay m e) \<and>
    fst (loss m e)\<le>snd (loss m e) \<and>
    fst (bandwidth m e)\<le>snd (bandwidth m e) \<and>
    fst (jitter m e)\<le>snd (jitter m e) \<and>
    fst (integrity m e)\<le>snd (integrity m e)"
  by (auto simp: metric_typed_def closed_intervals_def case_prod_beta)
lemma edge_kind_exhaustive: "edge_type d e=SourceId \<or> edge_type d e=Transport"
  by (cases "edge_type d e") simp_all
definition distributed where
  "distributed input_of operative carrier_at pair =
    (pair_spec input_of operative (pair 0) (pair 1) \<and>
    carrier_at (snd (snd (pair 0)))\<noteq>carrier_at (snd (snd (pair 1))))"
lemma distributed_exact:
  "distributed input_of operative carrier_at pair =
    (pair_spec input_of operative (pair 0) (pair 1) \<and>
    carrier_at (snd (snd (pair 0)))\<noteq>carrier_at (snd (snd (pair 1))))"
  by (simp add: distributed_def)
definition communication_context where
  "communication_context input_of operative carrier_at pair scale g =
    (distributed input_of operative carrier_at pair \<and>
    (\<forall>k::nat<2. carrier_at (snd (snd (pair k)))\<in>vertices g) \<and>
    linked g (carrier_at (snd (snd (pair 0)))) (carrier_at (snd (snd (pair 1)))))"
lemma context_exact:
  "communication_context input_of operative carrier_at pair scale g =
    (distributed input_of operative carrier_at pair \<and>
    (\<forall>k::nat<2. carrier_at (snd (snd (pair k)))\<in>vertices g) \<and>
    linked g (carrier_at (snd (snd (pair 0)))) (carrier_at (snd (snd (pair 1)))))"
  by (simp add: communication_context_def)

ML \<open>
val roots = @{thms finite_graph walk_positive walk_adjacent walk_endpoints closed_exact
  linked_exact linked_symmetric linked_vertices single_edge_links empty_edges_no_links
  one_way_is_sufficient word_domain_exact absent_word_allowed word_single_valued
  probability_bounds metric_intervals edge_kind_exhaustive distributed_exact context_exact};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
