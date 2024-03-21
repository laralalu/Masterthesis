theory "high-risk-3-4-31"
  imports 
  types
  SDL_agents
begin

consts
  conf_body_wants_notic::"ag\<Rightarrow>\<sigma>"
  apply_notifying_auth::"ag\<Rightarrow>\<sigma>"
  accr_cert_exists_Art33::"ag\<Rightarrow>\<sigma>"
  has_descrip::"appl_nb\<Rightarrow>\<sigma>"
  has_accr_cert_Art33::"appl_nb\<Rightarrow>\<sigma>"
  has_rel_doc::"appl_nb\<Rightarrow>\<sigma>"
  has_evidence_comp_Art33::"appl_nb\<Rightarrow>\<sigma>"
  designated_other_Union_harm_leg::"ag\<Rightarrow>\<sigma>" 
  use_docs_linked_to_other_designations::"ag\<Rightarrow>appl_nb\<Rightarrow>\<sigma>"

abbreviation "A1 \<equiv> \<lfloor>(conf_body_wants_notic e) \<^bold>\<rightarrow> \<^bold>\<circle>e<stit e (apply_notifying_auth e)>\<rfloor>"
abbreviation "A2 \<equiv> \<lfloor>\<^bold>\<forall>appl. \<^bold>\<circle>e<stit e (has_descrip appl)>\<rfloor>"
abbreviation "A3 \<equiv> \<lfloor>\<^bold>\<forall>appl. \<^bold>\<circle>e<stit e (has_rel_doc appl)>\<rfloor>"
(*two cases:*)
abbreviation "A4 \<equiv> \<lfloor>\<^bold>\<forall>appl. ((apply_notifying_auth e) \<^bold>\<and> (accr_cert_exists_Art33 e)) \<^bold>\<rightarrow> \<^bold>\<circle>e<stit e (has_accr_cert_Art33 appl)>\<rfloor>"
abbreviation "A5 \<equiv> \<lfloor>\<^bold>\<forall>appl. (apply_notifying_auth e) \<^bold>\<and> (\<^bold>\<not> accr_cert_exists_Art33 e) \<^bold>\<rightarrow> \<^bold>\<circle>e<stit e (has_evidence_comp_Art33 appl)>\<rfloor>"
(*not obligated to not do something \<rightarrow> may*)
abbreviation "A6 \<equiv> \<lfloor>\<^bold>\<forall>appl. (designated_other_Union_harm_leg g) \<^bold>\<rightarrow>
   \<^bold>\<not>\<^bold>\<circle>g<\<^bold>\<not> (stit g (use_docs_linked_to_other_designations g appl))>\<rfloor>"
abbreviation "theory \<equiv> A1 \<and> A2 \<and> A3 \<and> A4 \<and> A5 \<and> A6"

consts x::appl_nb

(*Facts*) 
abbreviation "F1 w \<equiv> (conf_body_wants_notic e)  w"
abbreviation "F2 w \<equiv> (accr_cert_exists_Art33 e)  w"
abbreviation "F3 w \<equiv> (designated_other_Union_harm_leg g) w"
abbreviation "F4 w \<equiv> (apply_notifying_auth e) w"
abbreviation "facts \<equiv> F1 \<^bold>\<and> F2 \<^bold>\<and> F3 \<^bold>\<and> F4"

theorem Result1a: "theory \<longrightarrow> \<lfloor>facts \<^bold>\<rightarrow> (\<^bold>\<circle>e<stit e (has_accr_cert_Art33 x)>)\<rfloor>"  
  by auto

theorem Result1b: "theory \<longrightarrow> \<lfloor>facts \<^bold>\<rightarrow> (\<^bold>\<circle>e<stit e (has_evidence_comp_Art33 x)>)\<rfloor>"  
  nitpick [user_axioms] (*counterexample found*) oops

theorem Result2a: "theory \<longrightarrow> \<lfloor>facts \<^bold>\<rightarrow> (\<^bold>\<not>\<^bold>\<circle>g< \<^bold>\<not> (stit g (use_docs_linked_to_other_designations g x))>)\<rfloor>"  
  by simp

theorem Result2b: "theory \<longrightarrow> \<lfloor>facts \<^bold>\<rightarrow> (\<^bold>\<not>\<^bold>\<circle>e<\<^bold>\<not> (stit e (use_docs_linked_to_other_designations e x))>)\<rfloor>"  
  nitpick [user_axioms] (*counterexample found*) oops

(*Notes:
- conformity assessment bodies become notified bodies once they are notified. This is difficult to represent, since an
instance can only be of one type. Here, we hence define obligations for conformity assessment bodies and notified bodies,
but there is no way to show that a conformity assessment body has been notified.
*)
end