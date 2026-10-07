theory Core_Indexed_Deletion
 imports Main
begin

fun final_node where
 "final_node i []=i" |
 "final_node i ((j,k)#es)=final_node j es"
fun valid_edges where
 "valid_edges adm i [] j = (i=j)" |
 "valid_edges adm i ((a,k)#es) j = (adm k i a \<and> valid_edges adm a es j)"
definition interval where "interval es a b=take (b-a) (drop a es)"
definition erase where "erase es a b=take a es @ drop b es"
definition source_only where "source_only src es=(\<forall>e\<in>set es. snd e=src)"
definition node where "node i es r=final_node i (take r es)"

lemma terminal_append: "final_node i (p@q)=final_node (final_node i p) q"
 by (induction p arbitrary: i) (auto split: prod.splits)
lemma valid_append:
 "valid_edges adm i (p@q) j =
  (valid_edges adm i p (final_node i p) \<and> valid_edges adm (final_node i p) q j)"
 by (induction p arbitrary: i) (auto split: prod.splits)

lemma cut_decomposition:
 "a\<le>b \<Longrightarrow> (take a es @ interval es a b) @ drop b es=es"
 by (simp add: interval_def take_add[symmetric])

lemma cut_lengths:
 assumes ab: "a\<le>b" and bound: "b\<le>length es"
 shows "length(take a es)=a \<and> length(interval es a b)=b-a \<and>
  length(erase es a b)=length es-(b-a)"
 using ab bound by (auto simp: interval_def erase_def min_def)

lemma erased_display:
 "i#map fst (erase es a b) = i#(take a (map fst es) @ drop b (map fst es)) \<and>
  map snd (erase es a b)=take a (map snd es) @ drop b (map snd es)"
 by (simp add: erase_def take_map drop_map)

lemma node_display:
 "r\<le>length es \<Longrightarrow> node i es r=(i#map fst es)!r"
proof (induction es arbitrary: i r)
 case Nil
 then show ?case by (simp add: node_def)
next
 case (Cons e es)
 then show ?case by (cases e; cases r) (auto simp: node_def)
qed

lemma slice_source_iff:
 assumes ab: "a\<le>b" and bound: "b\<le>length es"
 shows "source_only src (interval es a b) = (\<forall>n. a\<le>n \<longrightarrow> n<b \<longrightarrow> snd(es!n)=src)"
proof
 assume h: "source_only src (interval es a b)"
 show "\<forall>n. a\<le>n \<longrightarrow> n<b \<longrightarrow> snd(es!n)=src"
 proof (intro allI impI)
  fix n assume an: "a\<le>n" and nb: "n<b"
  have ix: "n-a<length(interval es a b)" using cut_lengths[OF ab bound] an nb by arith
  have member: "interval es a b ! (n-a) \<in> set(interval es a b)" by (rule nth_mem[OF ix])
  have val: "interval es a b ! (n-a)=es!n"
   using an nb ab bound by (simp add: interval_def nth_take nth_drop)
  have all_members: "\<forall>e\<in>set(interval es a b). snd e=src"
   using h by (simp only: source_only_def)
  have at_index: "snd(interval es a b ! (n-a))=src" by (rule bspec[OF all_members member])
  show "snd(es!n)=src" using at_index by (simp only: val)
 qed
next
 assume h: "\<forall>n. a\<le>n \<longrightarrow> n<b \<longrightarrow> snd(es!n)=src"
 show "source_only src (interval es a b)"
 proof (unfold source_only_def, intro ballI)
  fix e assume e: "e\<in>set(interval es a b)"
  then obtain n where ix: "n<length(interval es a b)" and ev: "interval es a b!n=e"
   by (auto simp: in_set_conv_nth)
  have nb: "a+n<b" using cut_lengths[OF ab bound] ix by arith
  have val: "interval es a b!n=es!(a+n)"
   using ix ab bound by (simp add: interval_def nth_take nth_drop)
  show "snd e=src" using h nb ev val by auto
 qed
qed

definition indexed_delete where
 "indexed_delete src i es fs = (\<exists>a b. a<b \<and> b\<le>length es \<and> node i es a=node i es b \<and>
  source_only src (interval es a b) \<and> fs=erase es a b)"
definition segment_delete where
 "segment_delete src i es fs = (\<exists>p mid q. es=(p@mid)@q \<and> fs=p@q \<and> mid\<noteq>[] \<and>
  source_only src mid \<and> final_node i p=final_node i (p@mid))"

lemma indexed_to_segment:
 "indexed_delete src i es fs \<Longrightarrow> segment_delete src i es fs"
proof -
 assume h: "indexed_delete src i es fs"
 then obtain a b where ab: "a<b" and bound: "b\<le>length es" and closed: "node i es a=node i es b"
  and only_src: "source_only src (interval es a b)" and out: "fs=erase es a b"
  unfolding indexed_delete_def by blast
 have le: "a\<le>b" using ab by simp
 have nz: "interval es a b\<noteq>[]" using cut_lengths[OF le bound] ab by auto
 have cut: "es=(take a es @ interval es a b)@drop b es" by (rule sym[OF cut_decomposition[OF le]])
 have close: "final_node i (take a es)=final_node i (take a es@interval es a b)"
  using closed le by (simp add: node_def interval_def take_add[symmetric])
 show ?thesis unfolding segment_delete_def
  by (intro exI[of _ "take a es"] exI[of _ "interval es a b"] exI[of _ "drop b es"])
   (use cut out nz only_src close in \<open>simp add: erase_def\<close>)
qed

lemma segment_to_indexed:
 "segment_delete src i es fs \<Longrightarrow> indexed_delete src i es fs"
proof -
 assume h: "segment_delete src i es fs"
 then obtain p mid q where es: "es=(p@mid)@q" and fs: "fs=p@q" and nz: "mid\<noteq>[]"
  and only_src: "source_only src mid" and closed: "final_node i p=final_node i (p@mid)"
  unfolding segment_delete_def by blast
 have pref: "take (length p) es=p" using es by simp
 have upto: "take (length p+length mid) es=p@mid" using es by simp
 have suff: "drop (length p+length mid) es=q" using es by simp
 have middle: "interval es (length p) (length p+length mid)=mid"
  using es by (simp add: interval_def)
 show ?thesis unfolding indexed_delete_def
  by (intro exI[of _ "length p"] exI[of _ "length p+length mid"])
   (use nz only_src closed es fs pref upto suff middle in \<open>simp add: node_def erase_def\<close>)
qed

lemma indexed_iff_segment:
 "indexed_delete src i es fs = segment_delete src i es fs"
 by (rule iffI, erule indexed_to_segment, erule segment_to_indexed)

lemma deletion_preserves_typing:
 assumes v: "valid_edges adm i es j" and d: "indexed_delete src i es fs"
 shows "valid_edges adm i fs j"
proof -
 obtain p mid q where es: "es=(p@mid)@q" and fs: "fs=p@q"
  and close: "final_node i p=final_node i (p@mid)"
  using indexed_to_segment[OF d] unfolding segment_delete_def by blast
 have outer: "valid_edges adm i (p@mid) (final_node i (p@mid)) \<and>
  valid_edges adm (final_node i (p@mid)) q j" using v by (simp only: es valid_append)
 have inner: "valid_edges adm i p (final_node i p)"
  using outer by (auto simp only: valid_append)
 have tail: "valid_edges adm (final_node i (p@mid)) q j" by (rule conjunct2[OF outer])
 have tail_at_base: "valid_edges adm (final_node i p) q j" using tail by (simp only: close)
 show ?thesis using inner tail_at_base by (simp only: fs valid_append)
qed

lemma no_deletion_equivalence:
 "(\<not>(\<exists>fs. indexed_delete src i es fs)) = (\<not>(\<exists>fs. segment_delete src i es fs))"
 by (simp only: indexed_iff_segment)

ML \<open>
val roots = @{thms terminal_append valid_append cut_decomposition cut_lengths erased_display
 node_display slice_source_iff indexed_iff_segment deletion_preserves_typing no_deletion_equivalence};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
