theory Core_Local_Loop_Specification
 imports Main
begin

definition step where "step adm sign i j = (if sign then adm i j else adm j i)"
lemma directed_step:
 "step adm sign i j = ((sign=True \<and> adm i j) \<or> (sign=False \<and> adm j i))"
 by (cases sign) (simp_all add: step_def)

fun path where
 "path adm i [] j = (i=j)" |
 "path adm i ((j,s)#es) k = (step adm s i j \<and> path adm j es k)"

definition valid_spec where
 "valid_spec adm carrier b s = (path adm b (fst s) b \<and> fst s\<noteq>[] \<and> snd s\<subseteq>carrier b)"
definition display where
 "display b s = ((length(fst s),b#map fst (fst s),map snd (fst s)),snd s)"

lemma specification_shape:
 "valid_spec adm carrier b s \<Longrightarrow>
  0<length(fst s) \<and> length(b#map fst(fst s))=length(fst s)+1 \<and>
  length(map snd(fst s))=length(fst s) \<and> snd s\<subseteq>carrier b"
 by (simp add: valid_spec_def)

lemma zip_projections: "zip (map fst es) (map snd es) = es"
 by (induction es) (auto split: prod.splits)

lemma display_injective: "display b s=display b t \<Longrightarrow> s=t"
proof -
 assume h: "display b s=display b t"
 have p: "map fst(fst s)=map fst(fst t)" and k: "map snd(fst s)=map snd(fst t)"
  and d: "snd s=snd t" using h unfolding display_def by auto
 have "zip (map fst(fst s)) (map snd(fst s))=zip (map fst(fst t)) (map snd(fst t))"
  by (simp only: p k)
 then have "fst s=fst t" by (simp only: zip_projections)
 then show "s=t" using d by (cases s; cases t; simp)
qed

lemma tuple_reconstruction:
 "(path adm b es b \<and> es\<noteq>[] \<and> D\<subseteq>carrier b) =
  (\<exists>!s. valid_spec adm carrier b s \<and> fst s=es \<and> snd s=D)"
 by (auto simp: valid_spec_def intro!: ex1I[of _ "(es,D)"])

lemma separate_lists_reconstruction:
 assumes len: "length ps=length signs" and v: "path adm b (zip ps signs) b"
  and pos: "ps\<noteq>[]" and typed_domain: "D\<subseteq>carrier b"
 shows "\<exists>!s. valid_spec adm carrier b s \<and> display b s=((length ps,b#ps,signs),D)"
proof -
 let ?s = "(zip ps signs,D)"
 have nz: "zip ps signs\<noteq>[]" using len pos by (metis length_0_conv length_zip min.idem)
 have valid: "valid_spec adm carrier b ?s" using v nz typed_domain by (simp add: valid_spec_def)
 have p: "map fst(zip ps signs)=ps" using len by simp
 have k: "map snd(zip ps signs)=signs" using len by simp
 have ds: "display b ?s=((length ps,b#ps,signs),D)"
  by (simp only: display_def fst_conv snd_conv p k length_zip len min.idem)
 show ?thesis
 proof (rule ex1I[of _ ?s])
  show "valid_spec adm carrier b ?s \<and> display b ?s=((length ps,b#ps,signs),D)"
   by (rule conjI[OF valid ds])
  fix t assume "valid_spec adm carrier b t \<and> display b t=((length ps,b#ps,signs),D)"
  then have "display b t=display b ?s" using ds by simp
  then show "t=?s" by (rule display_injective)
 qed
qed

lemma zero_length_excluded: "valid_spec adm carrier b s \<Longrightarrow> length(fst s)\<noteq>0"
 by (simp add: valid_spec_def)

definition restrict where "restrict s D=(fst s,D)"
lemma domain_replacement_retains_word:
 "valid_spec adm carrier b s \<Longrightarrow> D\<subseteq>carrier b \<Longrightarrow>
  valid_spec adm carrier b (restrict s D) \<and> fst(restrict s D)=fst s \<and> snd(restrict s D)=D"
 by (simp add: restrict_def valid_spec_def)

lemma empty_domain_allowed:
 "valid_spec adm carrier b s \<Longrightarrow>
  \<exists>t. valid_spec adm carrier b t \<and> fst t=fst s \<and> snd t={}"
 by (rule exI[of _ "restrict s {}"], simp add: restrict_def valid_spec_def)

definition tagged_domain where "tagged_domain b s={(v,x). v=b \<and> x\<in>snd s}"
lemma tagged_domain_exact:
 "valid_spec adm carrier b s \<Longrightarrow>
  tagged_domain b s={b}\<times>snd s \<and> tagged_domain b s\<subseteq>{b}\<times>carrier b"
 by (auto simp: tagged_domain_def valid_spec_def)

ML \<open>
val roots = @{thms directed_step specification_shape display_injective tuple_reconstruction
 separate_lists_reconstruction zero_length_excluded domain_replacement_retains_word
 empty_domain_allowed tagged_domain_exact};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
