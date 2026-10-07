theory Empty_Carrier_Cases
  imports Order_Embedding_Isabelle
begin

lemma empty_image_carrier:
  "image (f::'a \<Rightarrow> 'b) {} = {}"
  by simp

lemma empty_inj_on:
  "inj_on (f::'a \<Rightarrow> 'b) {}"
  by simp

lemma empty_quotient_carrier:
  "QuSet {} r = {}"
  unfolding QuSet_def by simp

lemma empty_quotient_is_strict_linear:
  "strict_linear_on (QuSet {} r) (qlt {} r)"
  unfolding QuSet_def strict_linear_on_def strict_on_def by simp

lemma empty_inverse_contract_vacuous:
  fixes rho :: "'a \<Rightarrow> 'b"
  shows
    "(\<forall>x\<in>{}. inv_into {} rho (rho x) = x) \<and>
     (\<forall>t\<in>image rho {}. rho (inv_into {} rho t) = t)"
  by simp

lemma empty_nested_carriers_admit_factor:
  fixes piA :: "'s \<Rightarrow> 'qa"
    and piS :: "'s \<Rightarrow> 'qs"
    and ltA :: "'qa \<Rightarrow> 'qa \<Rightarrow> bool"
    and ltS :: "'qs \<Rightarrow> 'qs \<Rightarrow> bool"
  shows
    "\<exists>iota::'qa \<Rightarrow> 'qs.
      image iota {} \<subseteq> {} \<and>
      inj_on iota {} \<and>
      (\<forall>x\<in>{}. iota (piA x) = piS x) \<and>
      (\<forall>q\<in>{}. \<forall>q'\<in>{}.
        (ltA q q' \<longleftrightarrow> ltS (iota q) (iota q')))"
  by simp

end
