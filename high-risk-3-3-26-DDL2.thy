theory "high-risk-3-3-26-DDL2"
  imports 
    DDL_agents_mod
begin

consts
  system_in_conformity::"aiSys\<Rightarrow>\<sigma>"
  not_on_market::"aiSys\<Rightarrow>\<sigma>"  
  l::aiSys
  b::ag
  importer_of::"ag\<Rightarrow>aiSys\<Rightarrow>\<sigma>"

axiomatization where
A1a: "\<lfloor>\<^bold>\<forall>x i. (high_risk x \<^bold>\<and> importer i \<^bold>\<and> importer_of i x) \<^bold>\<rightarrow> \<^bold>\<circle>i<stit i (system_in_conformity x)>\<rfloor>" and 
A8a: "\<lfloor>\<^bold>\<forall>x i. (\<^bold>\<not> (system_in_conformity x) \<^bold>\<and> (high_risk x \<^bold>\<and> importer i \<^bold>\<and> importer_of i x)) \<^bold>\<rightarrow> \<^bold>\<circle>i<(stit i (not_on_market x))>\<rfloor>" and
(*implicit: If the system is in conformity, the importer is obligated to not see to it that the system is not placed
on the market*)
AXa: "\<lfloor>\<^bold>\<forall>x i. (high_risk x \<^bold>\<and> importer i \<^bold>\<and> importer_of i x) \<^bold>\<rightarrow> (\<^bold>\<circle>i<stit i (system_in_conformity x) \<^bold>\<rightarrow> (\<^bold>\<not> (stit i (not_on_market x)))>)\<rfloor>" and

F0: "\<lfloor>high_risk l\<rfloor>\<^sub>l" and F1: "\<lfloor>importer b\<rfloor>\<^sub>l" and F2: "\<lfloor>importer_of b l\<rfloor>\<^sub>l" and
Situationb: "\<lfloor>\<^bold>\<not> (system_in_conformity l)\<rfloor>\<^sub>l"

(***Some Experiments***) 
lemma True nitpick [satisfy, user_axioms, card i=1] oops (*Consistency-check: Nitpick ran out of time*)

lemma "\<lfloor>\<^bold>\<circle>b<(stit b (not_on_market l))>\<rfloor>\<^sub>l" using A8a F0 F1 F2 Situationb by blast
lemma "\<lfloor>\<^bold>\<circle>b<\<^bold>\<not> (stit b (not_on_market l))>\<rfloor>\<^sub>l" nitpick [user_axioms] oops (*Nitpick ran out of time*)

end

