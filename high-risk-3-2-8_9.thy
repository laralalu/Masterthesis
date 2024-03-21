theory "high-risk-3-2-8_9"
  imports 
  types
  SDL_agents
begin

consts
  comply_with_req_chap_2::"aiSys\<Rightarrow>\<sigma>"
  taken_into_account::"(aiSys\<Rightarrow>purpose)\<Rightarrow>aiSys\<Rightarrow>\<sigma>" (*take into account purpose of a system*)
  taken_into_account'::"(aiSys\<Rightarrow>rms)\<Rightarrow>aiSys\<Rightarrow>\<sigma>" (*take into account rms of a system*)
  taken_into_account''::"(aiSys\<Rightarrow>soa)\<Rightarrow>aiSys\<Rightarrow>\<sigma>" (*take into account state of art of similar systems*)
  taken_into_account'''::"(aiSys\<Rightarrow>consequence)\<Rightarrow>aiSys\<Rightarrow>\<sigma>" (*take into account consequences, effects, interactions of the system*)
  taken_into_account''''::"(aiSys\<Rightarrow>ag)\<Rightarrow>aiSys\<Rightarrow>\<sigma>" (*take into account background, knowledge, environment of users*)
  soa_sys::"(aiSys\<Rightarrow>soa)" (*state of art relating to aiSys*)
  rms_sys::"(aiSys\<Rightarrow>rms)"
  purpose_sys::"(aiSys\<Rightarrow>purpose)" 
  consequence_sys::"(aiSys\<Rightarrow>consequence)"
  users_sys::"aiSys\<Rightarrow>ag"
  rms_of_sys::"(aiSys\<Rightarrow>rms)"
  rms_established::"aiSys\<Rightarrow>\<sigma>" 
  rms_iterative_process::"(aiSys\<Rightarrow>rms)\<Rightarrow>aiSys\<Rightarrow>\<sigma>" (*risk management system of AI-system consists of iterative process*)
  rms_regular_updates::"(aiSys\<Rightarrow>rms)\<Rightarrow>aiSys\<Rightarrow>\<sigma>" (*risk management system of AI-system does regular updates*)
  (*shall be contained in the process of the risk management system*)
  rms_con_ident_and_analysis::"(aiSys\<Rightarrow>rms)\<Rightarrow>aiSys\<Rightarrow>\<sigma>"
  rms_con_est_and_eval::"(aiSys\<Rightarrow>rms)\<Rightarrow>aiSys\<Rightarrow>\<sigma>" 
  rms_con_eval_poss_risks::"(aiSys\<Rightarrow>rms)\<Rightarrow>aiSys\<Rightarrow>\<sigma>" 
  rms_con_adapt_man_measures::"(aiSys\<Rightarrow>rms)\<Rightarrow>aiSys\<Rightarrow>\<sigma>" 
  risk_measures_establ_2d::"(aiSys\<Rightarrow>rms)\<Rightarrow>aiSys\<Rightarrow>\<sigma>"
  used_in_acc_wi_purpose::"(aiSys\<Rightarrow>purpose)\<Rightarrow>aiSys\<Rightarrow>\<sigma>"
  used_foreseeable_misuse::"aiSys\<Rightarrow>\<sigma>"
  residual_risks::"(aiSys\<Rightarrow>risk)"
  risks::"(aiSys\<Rightarrow>risk)" 
  residual_risk_acceptable::"((aiSys\<Rightarrow>rms)\<Rightarrow>aiSys\<Rightarrow>\<sigma>)\<Rightarrow>(aiSys\<Rightarrow>risk)\<Rightarrow>aiSys\<Rightarrow>\<sigma>"
  communicate_to_user::"(aiSys\<Rightarrow>risk)\<Rightarrow>aiSys\<Rightarrow>\<sigma>"
  ensure_elem_reduction_risks::"(aiSys\<Rightarrow>risk)\<Rightarrow>aiSys\<Rightarrow>\<sigma>"
  ensure_mitigation_res_risks::"(aiSys\<Rightarrow>risk)\<Rightarrow>aiSys\<Rightarrow>\<sigma>"
  provide_info_and_training_users::"aiSys\<Rightarrow>\<sigma>"
  test_for_risk_man_meas::"aiSys\<Rightarrow>\<sigma>"
  testing_ensures_compliance_performance::"aiSys\<Rightarrow>\<sigma>"
  testing_appropriate_purpose::"(aiSys\<Rightarrow>purpose)\<Rightarrow>aiSys\<Rightarrow>\<sigma>"
  testing_beyond_necessary_purpose::"(aiSys\<Rightarrow>purpose)\<Rightarrow>aiSys\<Rightarrow>\<sigma>"
  testing_during_devprocess_as_appropriate::"aiSys\<Rightarrow>\<sigma>"
  testing_prior_to_release::"aiSys\<Rightarrow>\<sigma>"
  testing_against_defined_metrics_appropriate_purpose::"(aiSys\<Rightarrow>purpose)\<Rightarrow>aiSys\<Rightarrow>\<sigma>"
  consider_impact_children::"(aiSys\<Rightarrow>consequence)\<Rightarrow>aiSys\<Rightarrow>\<sigma>"
  credit_institut_reg_dir_2013_36_EU_add_part1_8_to_prod::\<sigma>

(*Ai Act article 8 + 9*)
(*d = providers, as said in chapter 3, art 16, all these requirements are meant to be ensured by providers*)
abbreviation "A1 \<equiv> \<lfloor>\<^bold>\<forall>x. \<^bold>\<circle>d<(stit d (comply_with_req_chap_2 x))>\<rfloor>"
abbreviation "A2 \<equiv> \<lfloor>\<^bold>\<forall>x. \<^bold>\<circle>d<(stit d (taken_into_account purpose_sys x))>\<rfloor>"
abbreviation "A3 \<equiv> \<lfloor>\<^bold>\<forall>x. \<^bold>\<circle>d<(stit d (taken_into_account' rms_sys x))>\<rfloor>"
abbreviation "A4 \<equiv> \<lfloor>\<^bold>\<forall>x. \<^bold>\<circle>d<(stit d (rms_established x))>\<rfloor>"
abbreviation "A5 \<equiv> \<lfloor>\<^bold>\<forall>x. \<^bold>\<circle>d<(stit d (rms_iterative_process rms_of_sys x)) \<^bold>\<and> (stit d (rms_regular_updates rms_of_sys x))>\<rfloor>"
abbreviation "A6 \<equiv> \<lfloor>\<^bold>\<forall>x. \<^bold>\<circle>d<(stit d (rms_con_ident_and_analysis rms_of_sys x)) \<^bold>\<and> (stit d (rms_con_est_and_eval rms_of_sys x))
  \<^bold>\<and> (stit d (rms_con_eval_poss_risks rms_of_sys x)) \<^bold>\<and> (stit d (rms_con_adapt_man_measures rms_of_sys x))>\<rfloor>"
abbreviation "A7 \<equiv> \<lfloor>\<^bold>\<forall>x. \<^bold>\<circle>d<(stit d (taken_into_account''' consequence_sys x)) \<^bold>\<and> (stit d (taken_into_account'' soa_sys x))>\<rfloor>"
abbreviation "A8 \<equiv> \<lfloor>\<^bold>\<forall>x. (used_in_acc_wi_purpose purpose_sys x) \<^bold>\<or> (used_foreseeable_misuse x) \<^bold>\<rightarrow>
  \<^bold>\<circle>d<stit d (residual_risk_acceptable risk_measures_establ_2d residual_risks x)>\<rfloor>"
abbreviation "A9 \<equiv>  \<lfloor>\<^bold>\<forall>x. \<^bold>\<circle>d<(stit d (communicate_to_user residual_risks x))>\<rfloor>"
abbreviation "A10 \<equiv>  \<lfloor>\<^bold>\<forall>x. \<^bold>\<circle>d<(stit d (ensure_elem_reduction_risks risks x)) \<^bold>\<and> (stit d (ensure_mitigation_res_risks residual_risks x)) \<^bold>\<and> 
  (stit d (provide_info_and_training_users x)) \<^bold>\<and> (stit d (taken_into_account'''' users_sys x))>\<rfloor>" 
abbreviation "A11 \<equiv>  \<lfloor>\<^bold>\<forall>x. \<^bold>\<circle>d<(stit d (test_for_risk_man_meas x)) \<^bold>\<and> (stit d (testing_ensures_compliance_performance x))>\<rfloor>"
abbreviation "A12 \<equiv> \<lfloor>\<^bold>\<forall>x. \<^bold>\<circle>d<(stit d (testing_appropriate_purpose purpose_sys x))> \<^bold>\<and> 
  (\<^bold>\<not> \<^bold>\<circle>d<(\<^bold>\<not> stit d (testing_beyond_necessary_purpose purpose_sys x))>)\<rfloor>"
abbreviation "A13 \<equiv> \<lfloor>\<^bold>\<forall>x. \<^bold>\<circle>d<(stit d (testing_during_devprocess_as_appropriate x)) \<^bold>\<and> (stit d (testing_prior_to_release x)) \<^bold>\<and>
  (stit d (testing_against_defined_metrics_appropriate_purpose purpose_sys x))>\<rfloor>"
abbreviation "A14 \<equiv> \<lfloor>\<^bold>\<forall>x. (stit d (rms_established x)) \<^bold>\<rightarrow> \<^bold>\<circle>d<(stit d (consider_impact_children consequence_sys x))>\<rfloor>"
abbreviation "A15 \<equiv> \<lfloor>\<^bold>\<circle>d<(stit d (credit_institut_reg_dir_2013_36_EU_add_part1_8_to_prod))>\<rfloor>"

(*Notes: 
- In A14, temporal dimension is lost
- Notion "as appropriate" or "as appropriate to" can't be captured perfectly*)

end