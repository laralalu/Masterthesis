theory extendedDDLtests
  imports 
  DDL_agents_clean
begin

consts 
  l::aiSys
  compliance_req_chap2::"aiSys\<Rightarrow>\<sigma>"

abbreviation "Example \<equiv> \<lfloor>stit d (compliance_req_chap2 l)\<rfloor>"

lemma assumes
stit1: "\<forall> F w. ((stit a F) w) \<longrightarrow> F w"
Example
shows "\<lfloor>compliance_req_chap2 l\<rfloor>" using DDL_agents_clean.stit1 local.stit1(2) by auto

end 