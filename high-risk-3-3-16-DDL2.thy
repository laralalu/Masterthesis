theory "high-risk-3-3-16-DDL2"
  imports types
  DDL_agents_mod
begin


(*-------------------------------------------------------------------*)
(*CTD example extended DDL2:*)
consts 
  d::ag (*type for provider*)
  ms::ag
  compliance_req_chap2::"aiSys\<Rightarrow>\<sigma>"
  competent_auth_member_state::"ag\<Rightarrow>ag"
  is_provider_of::"aiSys\<Rightarrow>ag\<Rightarrow>\<sigma>"
  inform::"aiSys\<Rightarrow>ag\<Rightarrow>\<sigma>" 
  l::aiSys
  provider_of::"aiSys\<Rightarrow>ag\<Rightarrow>\<sigma>" 

(*interesting part: CTD; Trying to create the typical structure*)
axiomatization where
F1: "\<lfloor>(high_risk l) \<^bold>\<and> (is_provider_of l d)\<rfloor>" and 
A1: "\<lfloor>\<^bold>\<forall>x p. (high_risk x) \<^bold>\<and> (is_provider_of l p) \<^bold>\<rightarrow> \<^bold>\<circle>p<stit p (compliance_req_chap2 x)>\<rfloor>" and
A8: "\<lfloor>\<^bold>\<forall>x p. \<^bold>\<not>(compliance_req_chap2 x) \<^bold>\<and> (high_risk x) \<^bold>\<rightarrow> \<^bold>\<circle>p<(stit p (inform x (competent_auth_member_state ms)))>\<rfloor>" and
(*implicit: If the compliance with the requirements is a given, the provider is obligated to not inform authorities 
of non-compliance (since that would make no sense*)
AX: "\<lfloor>\<^bold>\<forall>x p. \<^bold>\<circle>p<(compliance_req_chap2 x \<^bold>\<and> high_risk x) \<^bold>\<rightarrow> \<^bold>\<not> stit p (inform x (competent_auth_member_state ms))>\<rfloor>"and
Situation: "\<lfloor>\<^bold>\<not> (compliance_req_chap2 l)\<rfloor>\<^sub>l"

(***Some Experiments***) 
lemma True nitpick [satisfy, user_axioms, show_all] oops (*ran out of time*)

lemma "\<lfloor>\<^bold>\<circle>d<stit d (inform l (competent_auth_member_state ms))>\<rfloor>\<^sub>l" using A8 F1 Situation by auto
lemma "\<lfloor>\<^bold>\<circle>d<\<^bold>\<not>(stit d (inform l (competent_auth_member_state ms)))>\<rfloor>\<^sub>l" nitpick [user_axioms, show_all] oops (*ran out of time*)


end
