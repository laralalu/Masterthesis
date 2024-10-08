theory "multAgTests"
  imports 
    DDL_agents_4
begin

(*Article 32 ExtDDL (agents)*)
consts
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
  A32_1: "\<lfloor>\<^bold>\<not>\<^bold>\<circle>f<\<^bold>\<not> (stit f (notify f e))> \<^bold>\<leftrightarrow> (satisfies_req_Art33 e)\<rfloor>" and 
  A32_2: "\<lfloor>(stit f (notify f h) \<^bold>\<or> stit f (notify f c)) \<^bold>\<rightarrow> \<^bold>\<circle>f<stit f (use_elec_not_tool f)>\<rfloor>" and 
  A32_3: "\<lfloor>(stit f (notify f e) \<^bold>\<rightarrow>
   \<^bold>\<circle>f<stit f ((includes_details_conf_ass_activities (notification_for e)) \<^bold>\<and> (includes_details_conf_ass_modules (notification_for e)) \<^bold>\<and> 
  (includes_details_ai_used (notification_for e)))>)\<rfloor>" and
  A32_4: "\<lfloor>\<^bold>\<not>\<^bold>\<circle>f<\<^bold>\<not> stit f (act_as_notified_body e)>  \<^bold>\<leftrightarrow> 
    \<^bold>\<not>(objection_raised_within_1m h (act_as_notified_body e) \<^bold>\<and> (objection_raised_within_1m c (act_as_notified_body e)))\<rfloor>" and
  A32_5: "\<lfloor>(notification_changes (notification_for e)) \<^bold>\<rightarrow> \<^bold>\<circle>f<stit f (inform f c (notification_changes (notification_for e)) \<^bold>\<and> 
  (inform f h (notification_changes (notification_for e))))>\<rfloor>" and

  (*facts for tests of the rules*)
  F1: "\<lfloor>satisfies_req_Art33 e\<rfloor>\<^sub>l" and
  F2: "\<lfloor>(stit f (notify f h))\<rfloor>\<^sub>l" and
  F3: "\<lfloor>stit f (notify f e)\<rfloor>\<^sub>l" and
  F4: "\<lfloor>\<^bold>\<not>(objection_raised_within_1m h (act_as_notified_body e) \<^bold>\<and> (objection_raised_within_1m c (act_as_notified_body e)))\<rfloor>\<^sub>l" and
  F5: "\<lfloor>notification_changes (notification_for e)\<rfloor>\<^sub>l" 

lemma T1: "\<lfloor>\<^bold>\<not>\<^bold>\<circle>f<\<^bold>\<not> (stit f (notify f e))>\<rfloor>\<^sub>l" using A32_1 F1 by auto
lemma T2: "\<lfloor>\<^bold>\<circle>f<stit f (use_elec_not_tool f)>\<rfloor>\<^sub>l" using A32_2 F2 by auto
lemma T3: "\<lfloor>\<^bold>\<circle>f<stit f ((includes_details_conf_ass_activities (notification_for e)) \<^bold>\<and>
   (includes_details_conf_ass_modules (notification_for e))  \<^bold>\<and> (includes_details_ai_used (notification_for e)))>\<rfloor>\<^sub>l" using A32_3 F3 by auto
lemma T4: "\<lfloor>\<^bold>\<not>\<^bold>\<circle>f<\<^bold>\<not> stit f (act_as_notified_body e)>\<rfloor>\<^sub>l" using A32_4 F4 by auto
lemma T5: "\<lfloor>\<^bold>\<circle>f<stit f ((inform f c (notification_changes (notification_for e))) \<^bold>\<and> (inform f h (notification_changes (notification_for e))))>\<rfloor>\<^sub>l" 
   using A32_5 F5 by auto

lemma True nitpick [satisfy, user_axioms, show_all, card i=2]  (*Consistency-check: Nitpick finds a model.*)
