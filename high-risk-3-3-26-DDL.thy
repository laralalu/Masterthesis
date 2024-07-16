theory "high-risk-3-3-26-DDL"
  imports 
  DDL_agents_clean
begin
  
(*CTD structure*)
consts 
  l::aiSys
  system_in_conformity::"aiSys\<Rightarrow>\<sigma>"
  not_on_market::"aiSys\<Rightarrow>\<sigma>"


axiomatization where
A0: "\<lfloor>high_risk l\<rfloor>\<^sub>l" and
A1a: "\<lfloor>\<^bold>\<forall>x. (high_risk x) \<^bold>\<rightarrow> \<^bold>\<circle>b<stit b (system_in_conformity x)>\<rfloor>" and 
A8a: "\<lfloor>\<^bold>\<forall>x. \<^bold>\<not> (system_in_conformity x) \<^bold>\<and> (high_risk x) \<^bold>\<rightarrow> \<^bold>\<circle>b<(stit b (not_on_market x))>\<rfloor>" and
(*implicit: If the system is in conformity, the importer is obligated to not see to it that the system is not placed
on the market*)
AXa: "\<lfloor>\<^bold>\<forall>x. \<^bold>\<circle>b<(stit b (system_in_conformity x)) \<^bold>\<rightarrow> (\<^bold>\<not>(stit b (not_on_market x)))>\<rfloor>" and
Situationb: "\<lfloor>\<^bold>\<not> (system_in_conformity l)\<rfloor>\<^sub>l"

(***Some Experiments***) 
lemma True nitpick [satisfy, user_axioms, show_all] oops (*Consistency-check: Nitpick finds a model.*)

lemma "\<lfloor>\<^bold>\<circle>b<(stit b (not_on_market l))>\<rfloor>\<^sub>l" using A0 A8a Situationb by auto
lemma "\<lfloor>\<^bold>\<circle>b<\<^bold>\<not> (stit b (not_on_market l))>\<rfloor>\<^sub>l" nitpick [user_axioms] oops (*counterexample found*)

end
