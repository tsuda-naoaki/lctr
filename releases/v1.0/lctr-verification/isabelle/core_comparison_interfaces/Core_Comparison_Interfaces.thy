theory Core_Comparison_Interfaces
 imports Main
begin

definition evaluate where "evaluate f input=f(fst input)(snd input)"
theorem common_evaluation: "evaluate f (x,j)=f x j"
 by (simp add: evaluate_def)

definition pack_one :: "bool\<times>'u\<Rightarrow>bool\<times>(unit\<Rightarrow>'u)" where
 "pack_one p=(fst p,\<lambda>_. snd p)"
definition pack_two :: "bool\<times>'u\<times>'u\<Rightarrow>bool\<times>(bool\<Rightarrow>'u)" where
 "pack_two p=(fst p,\<lambda>b. if b then snd(snd p) else fst(snd p))"

theorem index_one_unique:
 fixes x :: "bool\<times>(unit\<Rightarrow>'u)"
 assumes typed: "range(snd x)\<subseteq>U"
 shows "\<exists>!p. snd p\<in>U \<and> pack_one p=x"
proof (rule ex1I[where a="(fst x,snd x ())"])
 have mem: "snd x ()\<in>U" using typed by blast
 have eq: "pack_one(fst x,snd x ())=x"
  by (cases x) (simp add: pack_one_def fun_eq_iff)
 show "snd(fst x,snd x ())\<in>U \<and> pack_one(fst x,snd x ())=x" using mem eq by simp
 fix p assume h: "snd p\<in>U \<and> pack_one p=x"
 have eq: "pack_one p=x" using h by blast
 have one: "fst p=fst x" using arg_cong[OF eq, where f=fst] by (simp add: pack_one_def)
 have two: "snd p=snd x ()" using arg_cong[OF eq, where f="\<lambda>z. snd z ()"] by (simp add: pack_one_def)
 show "p=(fst x,snd x ())" using one two by (cases p) auto
qed

theorem index_two_unique:
 fixes x :: "bool\<times>(bool\<Rightarrow>'u)"
 assumes typed: "range(snd x)\<subseteq>U"
 shows "\<exists>!p. fst(snd p)\<in>U \<and> snd(snd p)\<in>U \<and> pack_two p=x"
proof (rule ex1I[where a="(fst x,snd x False,snd x True)"])
 have mem: "snd x False\<in>U" "snd x True\<in>U" using typed by blast+
 have eq: "pack_two(fst x,snd x False,snd x True)=x"
  by (cases x) (auto simp: pack_two_def fun_eq_iff)
 show "fst(snd(fst x,snd x False,snd x True))\<in>U \<and>
  snd(snd(fst x,snd x False,snd x True))\<in>U \<and> pack_two(fst x,snd x False,snd x True)=x"
  using mem eq by simp
 fix p assume h: "fst(snd p)\<in>U \<and> snd(snd p)\<in>U \<and> pack_two p=x"
 have eq: "pack_two p=x" using h by blast
 have one: "fst p=fst x" using arg_cong[OF eq, where f=fst] by (simp add: pack_two_def)
 have two: "fst(snd p)=snd x False" using arg_cong[OF eq, where f="\<lambda>z. snd z False"] by (simp add: pack_two_def)
 have three: "snd(snd p)=snd x True" using arg_cong[OF eq, where f="\<lambda>z. snd z True"] by (simp add: pack_two_def)
 show "p=(fst x,snd x False,snd x True)" using one two three by (cases p) auto
qed

definition argument :: "'x\<Rightarrow>'j\<Rightarrow>nat\<Rightarrow>'x+('x\<times>'j)" where
 "argument x j i=(if i=0 then Inl x else Inr(x,j))"
theorem first_argument: "argument x j 0=Inl x" by (simp add: argument_def)
theorem later_argument:
 "i<7 \<Longrightarrow> i\<noteq>0 \<Longrightarrow> argument x j i=Inr(x,j)"
 by (simp add: argument_def)

definition evaluate_argument where
 "evaluate_argument first later i input=(case input of Inl x\<Rightarrow>first x | Inr pair\<Rightarrow>later i pair)"
theorem evaluation_dispatch:
 "i<7 \<Longrightarrow> evaluate_argument first later i (argument x j i) \<longleftrightarrow>
  (if i=0 then first x else later i (x,j))"
 by (simp add: argument_def evaluate_argument_def)

definition before :: "(nat\<Rightarrow>bool)\<Rightarrow>nat\<Rightarrow>bool" where
 "before c i \<longleftrightarrow> (\<forall>j<7. j<i \<longrightarrow> c j)"
definition through :: "(nat\<Rightarrow>bool)\<Rightarrow>nat\<Rightarrow>bool" where
 "through c i \<longleftrightarrow> (\<forall>j<7. j\<le>i \<longrightarrow> c j)"
theorem first_preceding: "before c 0 \<longleftrightarrow> True"
 by (simp add: before_def)
theorem preceding_successor:
 "i<6 \<Longrightarrow> before c (Suc i) \<longleftrightarrow> through c i"
 by (simp add: before_def through_def less_Suc_eq_le)
theorem established_step:
 "i<7 \<Longrightarrow> through c i \<longleftrightarrow> before c i \<and> c i"
 by (auto simp: before_def through_def le_less)
theorem seven_conditions: "through c 6 \<longleftrightarrow> (\<forall>i<7. c i)"
 by (auto simp: through_def)

ML \<open>
val roots = @{thms common_evaluation index_one_unique index_two_unique first_argument
 later_argument evaluation_dispatch first_preceding preceding_successor established_step seven_conditions};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
