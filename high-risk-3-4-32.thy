theory "high-risk-3-4-32"
  imports 
  types
  SDL_agents
begin

(*agent e = notified/conformity assessment body*) 
(*agent f = notifying authority*) 

consts
  body_meets_req_Art33::"ag\<Rightarrow>\<sigma>" 
  notify_body::"ag\<Rightarrow>ag\<Rightarrow>\<sigma>"
  notified::"ag\<Rightarrow>\<sigma>"
  notify_comm_ms_via_tool::"ag\<Rightarrow>\<sigma>"  
  notif_contains_details_mod_tech::\<sigma>
  objections_raised_comm_ms::\<sigma>
  notification_for_body_changes::"ag\<Rightarrow>\<sigma>"
  update_comm_ms_on::"ag\<Rightarrow>\<sigma>"  
  
(*only bodies that meet requirements may be notified*)
abbreviation "A1 \<equiv> \<lfloor>(body_meets_req_Art33 e) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<circle>f<(\<^bold>\<not> (stit f (notify_body f e)))>)\<rfloor>"
abbreviation "A2 \<equiv> \<lfloor>(notify_body f e) \<^bold>\<rightarrow> (\<^bold>\<circle>f<(\<^bold>\<not> (stit f (notify_comm_ms_via_tool f)))>)\<rfloor>"
abbreviation "A3 \<equiv> \<lfloor>(stit f (notify_comm_ms_via_tool f) \<^bold>\<rightarrow>
  \<^bold>\<circle>f<stit f (notif_contains_details_mod_tech)>)\<rfloor>"
(*can't express 'within one month'*)
abbreviation "A4 \<equiv> \<lfloor>(notified e) \<^bold>\<leftrightarrow> ((stit f (notify_body f e) \<^bold>\<and> \<^bold>\<not> (objections_raised_comm_ms)))\<rfloor>"
abbreviation "A5 \<equiv> \<lfloor>(notification_for_body_changes g ) \<^bold>\<rightarrow> \<^bold>\<circle>f<(stit f (update_comm_ms_on g))>\<rfloor>"

(*Notes:
- expressing interaction between agents is difficult! 
- eu commission is a single agent, however, there are several notified bodies, notifying authorities etc.
- can't express time, e.g. 'within one month'
- can't express that a conformity assessment body becomes a notified body once it has been notified by a notifying authority*)
end
