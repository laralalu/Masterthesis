theory "multAgTests_mod"
  imports 
    DDL_agents_mod (*DDL_agents*)
begin

(*Article 32 ModExtDDL (agents_2)*)
consts
  f::ag
  h::ag
  e::ag
  notify::"ag\<Rightarrow>ag\<Rightarrow>\<sigma>" (*Notifying authorities notify conformity assessment body*)
  satisfies_req_Art33::"ag\<Rightarrow>\<sigma>" (*Conformity assessment body satisfies requirements Article 33*)
  notification_changes::"notification\<Rightarrow>\<sigma>" (*Notification for a conformity assessment body changes*)
  inform::"ag\<Rightarrow>ag\<Rightarrow>(\<sigma>)\<Rightarrow>\<sigma>" (*Notifying authority informs another agent of the notification change*)
  use_elec_not_tool::"ag\<Rightarrow>\<sigma>" (*Notifying authority uses electronic notification tool*)
  includes_details_conf_ass_activities::"notification\<Rightarrow>\<sigma>" (*notification includes details on conformity assessment activities*)
  includes_details_conf_ass_modules::"notification\<Rightarrow>\<sigma>" (*notification includes details on conformity assessment modules*)
  includes_details_ai_used::"notification\<Rightarrow>\<sigma>" (*notification includes details on AI technology used*)
  act_as_notified_body::"ag\<Rightarrow>\<sigma>" (*conformity assessment body acts as notified body*)
  objection_raised_within_1m::"ag\<Rightarrow>(\<sigma>)\<Rightarrow>\<sigma>" (*objection raised by other agent on conformity assessment body acting as notified body*)
  notification_for::"ag\<Rightarrow>notification"

axiomatization where
  (*rules from Article 32*)
  A32_1: "\<lfloor>\<^bold>\<forall>a b. (notif_authority a) \<^bold>\<and> (conf_ass_body b) \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>\<circle>a<\<^bold>\<not> (stit a (notify a b))> \<^bold>\<leftrightarrow> (satisfies_req_Art33 b)\<rfloor>" and 
  A32_2: "\<lfloor>\<^bold>\<forall>a b. (notif_authority a) \<^bold>\<and> (member_state b) \<^bold>\<rightarrow> 
  (stit a (notify a b) \<^bold>\<or> stit a (notify a eu_comm)) \<^bold>\<rightarrow> \<^bold>\<circle>a<stit a (use_elec_not_tool a)>\<rfloor>" and 
  A32_3: "\<lfloor>\<^bold>\<forall>a b. (notif_authority a) \<^bold>\<and> (conf_ass_body b) \<^bold>\<rightarrow> (stit f (notify a b) \<^bold>\<rightarrow> 
   \<^bold>\<circle>a<stit a ((includes_details_conf_ass_activities (notification_for b)) \<^bold>\<and> 
   (includes_details_conf_ass_modules (notification_for b)) \<^bold>\<and> (includes_details_ai_used (notification_for b)))>)\<rfloor>" and
  A32_4: "\<lfloor>\<^bold>\<forall>a b. (conf_ass_body a) \<^bold>\<and> (member_state b) \<^bold>\<rightarrow> 
    \<^bold>\<not>\<^bold>\<circle>a<\<^bold>\<not> stit a (act_as_notified_body a)> \<^bold>\<leftrightarrow> 
    \<^bold>\<not>(objection_raised_within_1m b (act_as_notified_body a) \<^bold>\<and> (objection_raised_within_1m c (act_as_notified_body a)))\<rfloor>" and
  A32_5: "\<lfloor>\<^bold>\<forall>a b d. ((conf_ass_body a) \<^bold>\<and> (notif_authority b) \<^bold>\<and> (member_state h))
   \<^bold>\<rightarrow> (notification_changes (notification_for a)) \<^bold>\<rightarrow> \<^bold>\<circle>b<stit b ((inform b eu_comm (notification_changes (notification_for a))) \<^bold>\<and> 
   (inform b d (notification_changes (notification_for a))))>\<rfloor>" and

  (*facts for tests of the rules*)
  F1a: "\<lfloor>(notif_authority f)\<rfloor>\<^sub>l" and F1b: "\<lfloor>\<^bold>\<not>(member_state f)\<rfloor>\<^sub>l" and F1c: "\<lfloor>\<^bold>\<not>(conf_ass_body f)\<rfloor>\<^sub>l"  and 
  F2a: "\<lfloor>(member_state h)\<rfloor>\<^sub>l" and F2b:"\<lfloor>\<^bold>\<not>(notif_authority h)\<rfloor>\<^sub>l" and F2c: "\<lfloor>\<^bold>\<not>(conf_ass_body h)\<rfloor>\<^sub>l"  and 
  F3a: "\<lfloor>(conf_ass_body e)\<rfloor>\<^sub>l" and F3b:"\<lfloor>\<^bold>\<not>(notif_authority e)\<rfloor>\<^sub>l" and F3c: "\<lfloor>\<^bold>\<not>(member_state e)\<rfloor>\<^sub>l" and 
  F4: "\<lfloor>satisfies_req_Art33 e\<rfloor>\<^sub>l" and
  F5: "\<lfloor>(stit f (notify f h))\<rfloor>\<^sub>l" and
  F6: "\<lfloor>stit f (notify f e)\<rfloor>\<^sub>l" and
  F7: "\<lfloor>\<^bold>\<not>(objection_raised_within_1m h (act_as_notified_body e) \<^bold>\<and> (objection_raised_within_1m eu_comm (act_as_notified_body e)))\<rfloor>\<^sub>l" and
  F8: "\<lfloor>notification_changes (notification_for e)\<rfloor>\<^sub>l" 

lemma T1: "\<lfloor>\<^bold>\<not>\<^bold>\<circle>f<\<^bold>\<not> (stit f (notify f e))>\<rfloor>\<^sub>l" using A32_1 F1a F3a F4 by blast
lemma T2: "\<lfloor>\<^bold>\<circle>f<stit f (use_elec_not_tool f)>\<rfloor>\<^sub>l" using A32_2 F1a F2a F5 by presburger
lemma T3: "\<lfloor>\<^bold>\<circle>f<stit f ((includes_details_conf_ass_activities (notification_for e)) \<^bold>\<and> (includes_details_conf_ass_modules (notification_for e)) \<^bold>\<and> 
  (includes_details_ai_used (notification_for e)))>\<rfloor>\<^sub>l" using A32_3 F1a F3a F6 by blast
lemma T4: "\<lfloor>\<^bold>\<not>\<^bold>\<circle>e<\<^bold>\<not> stit e (act_as_notified_body e)>\<rfloor>\<^sub>l" using A32_4 F2a F3a F7 by force
lemma T5: "\<lfloor>\<^bold>\<circle>f<stit f ((inform f eu_comm (notification_changes (notification_for e))) \<^bold>\<and>
   (inform f h (notification_changes (notification_for e))))>\<rfloor>\<^sub>l" using A32_5 F1a F2a F3a F8 by blast

lemma True nitpick [satisfy, user_axioms, show_all, card ag=4, card i=1] (*Consistency-check: Nitpick finds a model, but if i is higher than 1, Nitpick runs out of time.*)


