theory extendedDDLtests
  imports types
  DDL_agents
begin

consts 
  l::aiSys
  compliance_req_chap2::"aiSys\<Rightarrow>\<sigma>"

abbreviation "Example \<equiv> \<lfloor>stit d (compliance_req_chap2 l)\<rfloor>"

lemma assumes
stit1: "\<forall> F w. ((stit a F) w) \<longrightarrow> F w"
Example
shows "\<lfloor>compliance_req_chap2 l\<rfloor>" try oops


(*
axiomatization where
Ex: "\<lfloor>stit d (compliance_req_chap2 l)\<rfloor>\<^sub>l"

lemma T1: "\<lfloor>(compliance_req_chap2 l)\<rfloor>\<^sub>l" using Ex stit1 by auto


consts
  m::aiSys 
  conf_ass_proc_done::"aiSys\<Rightarrow>\<sigma>"
  
axiomatization where
Ex1: "\<lfloor>stit b (stit d (conf_ass_proc_done m))\<rfloor>\<^sub>l"

lemma T2:  "\<lfloor>stit d (conf_ass_proc_done m)\<rfloor>\<^sub>l" using Ex1 stit1 by auto
*)
end