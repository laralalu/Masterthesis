theory "high-risk-3-3-27_DDL"
  imports 
  types
  DDL_agents
begin

consts
  comply_with_req_chap_2::"aiSys\<Rightarrow>\<sigma>" 
  available_on_market::"aiSys\<Rightarrow>\<sigma>" 
  bears_CE_marking::"aiSys\<Rightarrow>\<sigma>" 
  has_docu::"aiSys\<Rightarrow>\<sigma>" 
  has_instructions_use::"aiSys\<Rightarrow>\<sigma>" 
  complies_reg::"ag\<Rightarrow>aiSys\<Rightarrow>\<sigma>"
  prior_av_on_market::"(i\<Rightarrow>bool)\<Rightarrow>\<sigma>" (*prior to making a system available on the market*)
  presents_risk_art65_1::"aiSys\<Rightarrow>\<sigma>" 
  informed::"ag\<Rightarrow>aiSys\<Rightarrow>\<sigma>" 
  details_provided::"ag\<Rightarrow>aiSys\<Rightarrow>\<sigma>" 
  in_control_of_distri::"aiSys\<Rightarrow>\<sigma>"
  stor_tra_sys::"aiSys\<Rightarrow>stor_tra_conditions"
  violate_compl_req_chap_2::"stor_tra_conditions\<Rightarrow>aiSys\<Rightarrow>\<sigma>"
  demo_requested::"ag\<Rightarrow>aiSys\<Rightarrow>\<sigma>" 
  conformance_art_2_demonstrated::"aiSys\<Rightarrow>\<sigma>"
  cooperation_on_sys::"ag\<Rightarrow>ag\<Rightarrow>aiSys\<Rightarrow>\<sigma>"
  fulfills_crit_1::"aiSys\<Rightarrow>\<sigma>" 
  corrective_action_taken::"aiSys\<Rightarrow>\<sigma>"
  corrective_action_taken_by_resp_agent::"aiSys\<Rightarrow>\<sigma>"

(*AI Act article 27*)
(*d = providers, l = distributors, b = importers*)
(*If system is high risk and l sees to it that it is available on the market, l is obligated to see to it that (...)
Originally, the text says l shall do sth prior to making the system available, and not do sth until, but we can't express this.*)
(*d = providers, l = distributors*)
abbreviation "H1 \<equiv> \<lfloor>\<^bold>\<forall>x. (stit l (fulfills_crit_1 x)) \<^bold>\<leftrightarrow> (stit l (bears_CE_marking x)) \<^bold>\<and> 
  (stit l (has_docu x)) \<^bold>\<and> (stit l (has_instructions_use x)) \<^bold>\<and> (stit l (complies_reg d x)) \<^bold>\<and> (stit l (complies_reg b x))\<rfloor>"
abbreviation "B1 \<equiv> \<lfloor>\<^bold>\<forall>x. (high_risk x) \<^bold>\<rightarrow> (\<^bold>\<circle>l<(stit l (available_on_market x)) \<^bold>\<leftrightarrow> (stit l (fulfills_crit_1 x))>)\<rfloor>"
abbreviation "B2 \<equiv> \<lfloor>\<^bold>\<forall>x. (high_risk x) \<^bold>\<and> (\<^bold>\<not> (comply_with_req_chap_2 x)) \<^bold>\<rightarrow> (\<^bold>\<circle>l<(\<^bold>\<not> (stit l (available_on_market x)))>)\<rfloor>"
abbreviation "B2a \<equiv> \<lfloor>\<^bold>\<forall>x. (high_risk x) \<^bold>\<and> (\<^bold>\<not> (comply_with_req_chap_2 x)) \<^bold>\<rightarrow> (\<^bold>\<circle>l<(stit l (corrective_action_taken x)) \<^bold>\<or> 
(stit l (corrective_action_taken_by_resp_agent x))>)\<rfloor>"
abbreviation "B3 \<equiv> \<lfloor>\<^bold>\<forall>x. (high_risk x) \<^bold>\<rightarrow> (\<^bold>\<circle>l<(stit l (available_on_market x)) \<^bold>\<leftrightarrow> (comply_with_req_chap_2 x)>)\<rfloor>"
abbreviation "B4 \<equiv> \<lfloor>\<^bold>\<forall>x. (high_risk x) \<^bold>\<and> (presents_risk_art65_1 x) \<^bold>\<rightarrow> (\<^bold>\<circle>l<(stit l (informed d x)) \<^bold>\<or> (stit l (informed b x))>)\<rfloor>"
abbreviation "B5 \<equiv> \<lfloor>\<^bold>\<forall>x. (high_risk x) \<^bold>\<and> (in_control_of_distri x) \<^bold>\<rightarrow> (\<^bold>\<circle>l<(stit l (\<^bold>\<not> (violate_compl_req_chap_2 (stor_tra_sys x) x)))>)\<rfloor>"
abbreviation "B6 \<equiv> \<lfloor>\<^bold>\<forall>x. (high_risk x) \<^bold>\<and> (presents_risk_art65_1 x) \<^bold>\<rightarrow> (\<^bold>\<circle>l<(stit l (informed j x)) \<^bold>\<and>  (stit l (details_provided j x))>)\<rfloor>"
abbreviation "B7 \<equiv> \<lfloor>\<^bold>\<forall>x. (demo_requested j x) \<^bold>\<rightarrow> (\<^bold>\<circle>l<(stit l (conformance_art_2_demonstrated x))>)\<rfloor>"
abbreviation "B8 \<equiv> \<lfloor>\<^bold>\<forall>x. \<^bold>\<circle>l<(stit l (cooperation_on_sys j l x))>\<rfloor>"

(*-------------------------------------------------------------------*)
(*CTD example DDL:*)
consts 
  x::aiSys

(*interesting part: CTD; Trying to create the typical structure*)
(*stita still has no semantics*)
axiomatization where
F1: "\<lfloor>(high_risk x)\<rfloor>" and
A1: "\<lfloor>\<^bold>\<forall>x. (high_risk x) \<^bold>\<rightarrow> (\<^bold>\<circle>l<stit l (comply_with_req_chap_2 x)>)\<rfloor>" and
A8: "\<lfloor>\<^bold>\<forall>x. (high_risk x) \<^bold>\<and> (\<^bold>\<not> (comply_with_req_chap_2 x)) \<^bold>\<rightarrow> (\<^bold>\<circle>l<(stit l (corrective_action_taken x)) \<^bold>\<or> 
(stit l (corrective_action_taken_by_resp_agent x))>)\<rfloor>" and
(*implicit*)
AX: "\<lfloor>\<^bold>\<forall>x. \<^bold>\<circle>l<(stit l (comply_with_req_chap_2 x)) \<^bold>\<rightarrow> \<^bold>\<not> ((stit l (corrective_action_taken x)) \<^bold>\<or> 
(stit l (corrective_action_taken_by_resp_agent x)))>\<rfloor>" and
Situation: "\<lfloor>\<^bold>\<not> (comply_with_req_chap_2 x)\<rfloor>\<^sub>l"

(***Some Experiments***) 
lemma True nitpick [satisfy, user_axioms] oops (*Consistency-check: Nitpick finds a model.*)
(*In DDL, only one conclusion can be proven!*)
lemma "\<lfloor>\<^bold>\<circle>l<(stit l (corrective_action_taken x)) \<^bold>\<or> (stit l (corrective_action_taken_by_resp_agent x))>\<rfloor>\<^sub>l" using A8 F1 Situation by auto
lemma "\<lfloor>\<^bold>\<circle>l<\<^bold>\<not>((stit l (corrective_action_taken x)) \<^bold>\<or> (stit l (corrective_action_taken_by_resp_agent x)))>\<rfloor>\<^sub>l" nitpick [user_axioms] (*counterexample found*) oops

end

(*Notes: 
- timely dimension: prior, until *)