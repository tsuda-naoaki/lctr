theory Nested_Quotient_Order_Alignment
  imports "LCTR_Order_Embedding_Isabelle.Order_Embedding_Isabelle"
begin

lemmas nested_quotient_order_embedding = Order_Embedding_Isabelle.nested_quotient_order_embedding

ML \<open>
val roots = @{thms nested_quotient_order_embedding};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
