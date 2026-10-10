theory Core_Finite_Tuple_Data
  imports Main
begin

definition concatenate where "concatenate xs ys = xs @ ys"
definition split_tuple where "split_tuple n zs = (take n zs,drop n zs)"

lemma concatenate_empty_left: "concatenate [] ys=ys"
  by (simp add: concatenate_def)
lemma concatenate_cons: "concatenate (x#xs) ys=x#concatenate xs ys"
  by (simp add: concatenate_def)
lemma concatenated_length: "length (concatenate xs ys)=length xs+length ys"
  by (simp add: concatenate_def)
lemma split_concatenate: "split_tuple (length xs) (concatenate xs ys)=(xs,ys)"
  by (simp add: concatenate_def split_tuple_def)
lemma concatenate_split:
  "concatenate (fst (split_tuple n zs)) (snd (split_tuple n zs))=zs"
  by (simp add: concatenate_def split_tuple_def)
lemma concatenate_injective:
  "length xs=length xs' \<Longrightarrow> concatenate xs ys=concatenate xs' ys' \<Longrightarrow>
    xs=xs' \<and> ys=ys'"
  unfolding concatenate_def by (simp add: append_eq_append_conv)
lemma seven_components:
  "concatenate (concatenate [a,b,c] [d,e]) [f,g]=[a,b,c,d,e,f,g]"
  by (simp add: concatenate_def)

definition typed_tuple where
  "typed_tuple carriers xs \<longleftrightarrow> list_all2 (\<lambda>S x. x\<in>S) carriers xs"
lemma typed_tuple_concat:
  "typed_tuple (A@B) (concatenate xs ys) \<longleftrightarrow>
    typed_tuple A xs \<and> typed_tuple B ys"
  if "length xs=length A"
  using that by (simp add: typed_tuple_def concatenate_def list_all2_append)

ML \<open>
val roots = @{thms concatenate_empty_left concatenate_cons concatenated_length
  split_concatenate concatenate_split concatenate_injective seven_components};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = List.app (fn th => writeln ("LCTR_ROOT_STATEMENT=" ^ Thm.string_of_thm @{context} th)) roots;
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
