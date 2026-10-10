theory Core_Generated_Law_Identity
 imports "LCTR_Core_Law_Transport_Identity.Core_Law_Transport_Identity"
begin

locale generated_law_change =
 base: carrier_bijection Q T r0 s0 + newer: carrier_bijection Q U r1 s1
 for Q::"'q set" and T::"'t set" and U::"'u set"
 and r0::"'q\<Rightarrow>'t" and s0::"'t\<Rightarrow>'q"
 and r1::"'q\<Rightarrow>'u" and s1::"'u\<Rightarrow>'q"
begin
definition change where "change=r1 \<circ> s0"
definition change_inverse where "change_inverse=r0 \<circ> s1"

lemma coordinate_change_bijection: "carrier_bijection T U change change_inverse"
proof
 show "change ` T\<subseteq>U"
  using base.inverse_typed newer.forward_typed by (auto simp: change_def; blast)
 show "change_inverse ` U\<subseteq>T"
  using newer.inverse_typed base.forward_typed by (auto simp: change_inverse_def; blast)
 show "\<And>t. t\<in>T \<Longrightarrow> change_inverse(change t)=t"
 proof -
  fix t assume t: "t\<in>T"
  have s: "s0 t\<in>Q" using base.inverse_typed t by blast
  show "change_inverse(change t)=t"
   by (simp add: change_def change_inverse_def newer.left_inverse[OF s] base.right_inverse[OF t])
 qed
 show "\<And>u. u\<in>U \<Longrightarrow> change(change_inverse u)=u"
 proof -
  fix u assume u: "u\<in>U"
  have s: "s1 u\<in>Q" using newer.inverse_typed u by blast
  show "change(change_inverse u)=u"
   by (simp add: change_def change_inverse_def base.left_inverse[OF s] newer.right_inverse[OF u])
 qed
qed

lemma coordinate_change_on_source: "q\<in>Q \<Longrightarrow> change(r0 q)=r1 q"
 by (simp add: change_def base.left_inverse)

lemma coordinate_change_unique:
 assumes commutes: "\<And>q. q\<in>Q \<Longrightarrow> h(r0 q)=r1 q"
 shows "\<forall>t\<in>T. h t=change t"
proof (intro ballI)
 fix t assume t: "t\<in>T"
 have s: "s0 t\<in>Q" using base.inverse_typed t by blast
 show "h t=change t"
  using commutes[OF s] by (simp add: base.right_inverse[OF t] change_def)
qed
end

context carrier_bijection
begin
lemma base_coordinate_identity:
 "\<forall>t\<in>U. (f \<circ> g)t=t"
 using right_inverse by simp

lemma base_family_identity:
 assumes time: "time_carrier d=U" and wf: "well_typed_family d"
 shows "same_family_content d (law_transport.target U U (f \<circ> g) (f \<circ> g) d)"
proof -
 have same: "\<And>u. u\<in>U \<Longrightarrow> (f \<circ> g)u=u" using right_inverse by simp
 interpret ident: identity_law_transport U "f \<circ> g" "f \<circ> g" d
 proof
  show "(f \<circ> g) ` U\<subseteq>U" using same by auto
  show "\<And>t. t\<in>U \<Longrightarrow> (f \<circ> g)((f \<circ> g)t)=t" using same by simp
  show "time_carrier d=U" by (rule time)
  show "well_typed_family d" by (rule wf)
  show "\<And>t. t\<in>U \<Longrightarrow> (f \<circ> g)t=t" by (rule same)
 qed
 show ?thesis by (rule ident.family_identity_from_values)
qed
end

ML \<open>
val roots = @{thms generated_law_change.coordinate_change_bijection
 generated_law_change.coordinate_change_on_source generated_law_change.coordinate_change_unique
 carrier_bijection.base_coordinate_identity carrier_bijection.base_family_identity};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
