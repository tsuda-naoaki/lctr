theory Core_Frequency_Windows
 imports LCTR_Core_Affine_Realization.Core_Affine_Realization
 LCTR_Core_Affine_Frequency.Core_Affine_Frequency
begin

record ('u,'j) raw_window =
 position :: 'u
 source :: 'j
 k0 :: nat
 k1 :: nat

locale arrival_projection =
 fixes U :: "'u set" and J :: "'j set" and Q :: "'q set"
 and token :: "'j\<Rightarrow>nat\<Rightarrow>'s" and D :: "'u\<Rightarrow>'s set"
 and arrival :: "'u\<Rightarrow>'s\<Rightarrow>'v" and project :: "'u\<Rightarrow>'v\<Rightarrow>'q"
 and r :: "'q\<Rightarrow>'q\<Rightarrow>bool"
 assumes project_maps: "u\<in>U \<Longrightarrow> a\<in>image(arrival u)(D u) \<Longrightarrow> project u a\<in>Q"
begin

definition endpoint where "endpoint u j k=project u (arrival u (token j k))"
definition admissible where
 "admissible w \<longleftrightarrow> position w\<in>U \<and> source w\<in>J \<and> k0 w<k1 w \<and>
 token (source w)(k0 w)\<in>D(position w) \<and> token (source w)(k1 w)\<in>D(position w) \<and>
 r (endpoint (position w)(source w)(k0 w)) (endpoint (position w)(source w)(k1 w))"

theorem endpoint_is_projected_arrival:
 assumes u: "u\<in>U" and j: "j\<in>J" and h: "token j k\<in>D u"
 shows "\<exists>a\<in>image(arrival u)(D u). a=arrival u(token j k) \<and> endpoint u j k=project u a"
 using h by (auto simp: endpoint_def)

theorem admissibility_iff:
 assumes u: "position w\<in>U" and j: "source w\<in>J"
 shows "admissible w \<longleftrightarrow> (\<exists>x\<in>{x. admissible x}. x=w)"
 by simp

definition abstract_window where
 "abstract_window w=\<lparr>count_start=k0 w, count_end=k1 w,
 lower=endpoint (position w)(source w)(k0 w), upper=endpoint (position w)(source w)(k1 w)\<rparr>"

theorem abstract_window_retains_fields:
 assumes "admissible w"
 shows "count_start(abstract_window w)=k0 w \<and> count_end(abstract_window w)=k1 w \<and>
 lower(abstract_window w)=endpoint (position w)(source w)(k0 w) \<and>
 upper(abstract_window w)=endpoint (position w)(source w)(k1 w)"
 by (simp add: abstract_window_def)

lemma endpoint_members:
 assumes h: "admissible w"
 shows "lower(abstract_window w)\<in>Q \<and> upper(abstract_window w)\<in>Q"
 using h project_maps unfolding admissible_def abstract_window_def endpoint_def by auto

definition count_difference :: "('u,'j)raw_window\<Rightarrow>'k::linordered_field" where
 "count_difference w=of_nat(k1 w-k0 w)"

theorem count_difference_positive:
 assumes "admissible w"
 shows "0<(count_difference w::'k::linordered_field)"
 using assms by (simp add: count_difference_def admissible_def)
end

locale native_frequency =
 arrival_projection U J Q token D arrival project r +
 affine_realization P act diff lt
 for U :: "'u set" and J :: "'j set" and Q :: "'q set"
 and token :: "'j\<Rightarrow>nat\<Rightarrow>'s" and D :: "'u\<Rightarrow>'s set"
 and arrival :: "'u\<Rightarrow>'s\<Rightarrow>'v" and project :: "'u\<Rightarrow>'v\<Rightarrow>'q"
 and r :: "'q\<Rightarrow>'q\<Rightarrow>bool"
 and P :: "'p set" and act :: "'p\<Rightarrow>'k::linordered_field\<Rightarrow>'p"
 and diff :: "'p\<Rightarrow>'p\<Rightarrow>'k" and lt :: "'p\<Rightarrow>'p\<Rightarrow>bool" +
 fixes repr :: "'q\<Rightarrow>'p"
 assumes repr_maps: "image repr Q\<subseteq>P"
begin

definition window_difference where
 "window_difference w=diff(repr(upper(abstract_window w)))(repr(lower(abstract_window w)))"
definition frequency where "frequency w=count_difference w / window_difference w"
definition period where "period w=inverse(frequency w)"

theorem coordinate_difference_positive:
 assumes h: "admissible w"
 and strict: "\<And>a b. a\<in>Q \<Longrightarrow> b\<in>Q \<Longrightarrow> (r a b \<longleftrightarrow> lt(repr a)(repr b))"
 shows "0<window_difference w"
proof -
 have lo: "lower(abstract_window w)\<in>Q" and hi: "upper(abstract_window w)\<in>Q"
  using endpoint_members[OF h] by blast+
 have plo: "repr(lower(abstract_window w))\<in>P" and phi: "repr(upper(abstract_window w))\<in>P"
  using repr_maps lo hi by blast+
 have ord: "r (lower(abstract_window w)) (upper(abstract_window w))"
  using h by (simp add: admissible_def abstract_window_def)
 show ?thesis using ord strict[OF lo hi] strict_sign[OF plo phi]
  unfolding window_difference_def by simp
qed

theorem frequency_positive:
 assumes h: "admissible w"
 and strict: "\<And>a b. a\<in>Q \<Longrightarrow> b\<in>Q \<Longrightarrow> (r a b \<longleftrightarrow> lt(repr a)(repr b))"
 shows "0<frequency w"
 unfolding frequency_def
 by (rule divide_pos_pos[OF count_difference_positive[OF h] coordinate_difference_positive[OF h strict]])

theorem period_positive_and_product:
 assumes h: "admissible w"
 and strict: "\<And>a b. a\<in>Q \<Longrightarrow> b\<in>Q \<Longrightarrow> (r a b \<longleftrightarrow> lt(repr a)(repr b))"
 shows "0<period w \<and> frequency w*period w=1"
 using frequency_positive[OF h strict] by (simp add: period_def)

theorem period_invariance:
 assumes "admissible x" "admissible y" "frequency x=frequency y"
 shows "period x=period y"
 using assms(3) by (simp add: period_def)

definition source_family where
 "source_family j W \<longleftrightarrow> W\<noteq>{} \<and>
  (\<forall>x\<in>W. admissible x \<and> source x=j) \<and>
  (\<forall>x\<in>W. \<forall>y\<in>W. frequency x=frequency y) \<and>
  (\<forall>x\<in>W. \<forall>y\<in>W. period x=period y)"

theorem source_values_unique:
 assumes h: "source_family j W"
 shows "\<exists>!values. \<forall>x\<in>W. source x=j \<and> values=(frequency x,period x)"
proof -
 obtain x where x: "x\<in>W" using h unfolding source_family_def by blast
 show ?thesis
 proof (rule ex1I[of _ "(frequency x,period x)"])
  show "\<forall>y\<in>W. source y=j \<and> (frequency x,period x)=(frequency y,period y)"
   using h x unfolding source_family_def by blast
  fix vals assume "\<forall>y\<in>W. source y=j \<and> vals=(frequency y,period y)"
  then show "vals=(frequency x,period x)" using x by blast
 qed
qed
end

ML \<open>
val roots = @{thms arrival_projection.endpoint_is_projected_arrival
 arrival_projection.admissibility_iff arrival_projection.abstract_window_retains_fields
 arrival_projection.count_difference_positive native_frequency.coordinate_difference_positive
 native_frequency.frequency_positive native_frequency.period_positive_and_product
 native_frequency.period_invariance native_frequency.source_values_unique};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
