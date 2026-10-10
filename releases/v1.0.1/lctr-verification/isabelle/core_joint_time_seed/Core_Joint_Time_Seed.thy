theory Core_Joint_Time_Seed
  imports "LCTR_Core_Observer_Time.Core_Observer_Time"
begin

locale common_seed_time =
  old: observer_seed C D B R0 Bind0 order0 +
  newer: observer_seed C D B R1 Bind1 order1
  for C :: "'c set" and D :: "'d set" and B :: "'b set"
    and R0 :: "('c\<times>'d\<times>'b)set" and R1 :: "('c\<times>'d\<times>'b)set"
    and Bind0 :: "(('c\<times>'d\<times>'b)\<times>('c\<times>'d\<times>'b))set"
    and Bind1 :: "(('c\<times>'d\<times>'b)\<times>('c\<times>'d\<times>'b))set"
    and order0 :: "('c\<times>'c)set" and order1 :: "('c\<times>'c)set" +
  assumes generated_equiv: "old.EC=newer.EC"
    and same_source: "order0=order1"
begin
definition time_map where "time_map(q::'c set)=q"
lemma time_setoids_equal: "old.EC=newer.EC" by (rule generated_equiv)
lemma time_quotient_types_equal: "old.Time=newer.Time"
  by (simp add: old.Time_def newer.Time_def generated_equiv)
lemma time_projection_agrees: "time_map(old.time_projection x)=newer.time_projection x"
  by (simp add: time_map_def old.time_projection_def newer.time_projection_def generated_equiv)
lemma time_maps_inverse: "time_map(time_map q)=q"
  by (simp add: time_map_def)
lemma generated_order_equal: "old.generated_order=newer.generated_order"
  using generated_equiv same_source time_quotient_types_equal
  unfolding old.generated_order_def newer.generated_order_def old.time_edges_def newer.time_edges_def by simp
lemma time_order_forward:
  "(x,y)\<in>old.generated_order \<Longrightarrow> (time_map x,time_map y)\<in>newer.generated_order"
  by (simp add: time_map_def generated_order_equal)
lemma time_order_agrees:
  "(time_map x,time_map y)\<in>newer.generated_order \<longleftrightarrow> (x,y)\<in>old.generated_order"
  by (simp add: time_map_def generated_order_equal)
end

ML \<open>
val roots = @{thms common_seed_time.time_setoids_equal common_seed_time.time_quotient_types_equal
  common_seed_time.time_projection_agrees common_seed_time.time_maps_inverse
  common_seed_time.time_order_forward common_seed_time.time_order_agrees};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = List.app (fn th => writeln ("LCTR_ROOT_STATEMENT=" ^ Thm.string_of_thm @{context} th)) roots;
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
