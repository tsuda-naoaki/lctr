theory Core_Finite_Report_Components
  imports Main
begin

definition fiber where "fiber xs s q = filter (\<lambda>a. s a = q) xs"
definition reasons where
  "reasons xs s is_undefined = map (\<lambda>a. (a,s a)) (filter (\<lambda>a. is_undefined (s a)) xs)"
definition local_reasons where
  "local_reasons xs s is_undefined G = filter (\<lambda>p. fst p \<in> set G) (reasons xs s is_undefined)"
definition burden where "burden single F = concat (map single F)"
definition tagged where "tagged y R = (if R = [] then Inl y else Inr R)"
definition set_tagged where "set_tagged y R = (if R = {} then Inl y else Inr R)"

lemma fiber_exact:
  "set (fiber xs s q) = {a \<in> set xs. s a = q}"
  by (auto simp: fiber_def)

lemma reasons_exact:
  "set (reasons xs s is_undefined) = {p. fst p \<in> set xs \<and> s (fst p) = snd p \<and> is_undefined (snd p)}"
  by (auto simp: reasons_def)

lemma local_reasons_exact:
  "set (local_reasons xs s is_undefined G) =
    {p. fst p \<in> set xs \<and> fst p \<in> set G \<and> s (fst p) = snd p \<and> is_undefined (snd p)}"
  by (auto simp: local_reasons_def reasons_exact)

lemma burden_exact:
  "set (burden single F) = {x. \<exists>a \<in> set F. x \<in> set (single a)}"
  by (auto simp: burden_def)

lemma burden_from_singleton_images:
  assumes hs: "\<And>a. set (single a) = m ` {b. R a b}"
  shows "set (burden single F) = {x. \<exists>a \<in> set F. \<exists>b. R a b \<and> m b = x}"
  by (auto simp: burden_exact hs)

lemma tagged_exact:
  "map_sum id set (tagged y R) = set_tagged y (set R)"
  by (cases R) (simp_all add: tagged_def set_tagged_def)

lemma tagged_has_nonempty_reason:
  "tagged y R = Inr T \<Longrightarrow> set T \<noteq> {}"
  by (auto simp: tagged_def split: if_splits)

ML \<open>
val roots = @{thms fiber_exact reasons_exact local_reasons_exact burden_exact
  burden_from_singleton_images tagged_exact tagged_has_nonempty_reason};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
