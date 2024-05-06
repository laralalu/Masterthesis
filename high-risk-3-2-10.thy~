theory "high-risk-3-2-10"
  imports 
  types
  SDL_agents
begin

consts
  uses_techniques_training_w_data::"aiSys\<Rightarrow>\<sigma>"
  use_techniques_model_training_to_ensure_compliance::"aiSys\<Rightarrow>\<sigma>"
  developed_with::"aiSys\<Rightarrow>tvt_dsets"
  high_quality::"tvt_dsets\<Rightarrow>\<sigma>"
  employed::"tvt_dsets\<Rightarrow>gov_and_man_practices"
  appropriate::"gov_and_man_practices\<Rightarrow>\<sigma>"
  concerns_design::"gov_and_man_practices\<Rightarrow>\<sigma>"
  concerns_datacoll::"gov_and_man_practices\<Rightarrow>\<sigma>"
  concerns_dataprep::"gov_and_man_practices\<Rightarrow>\<sigma>"
  concerns_form_assumptions::"gov_and_man_practices\<Rightarrow>\<sigma>"
  concerns_prior_assessment::"gov_and_man_practices\<Rightarrow>\<sigma>"
  concerns_examin_biases::"gov_and_man_practices\<Rightarrow>\<sigma>"
  concerns_ident_datagapy::"gov_and_man_practices\<Rightarrow>\<sigma>"
  characteristics_met::"tvt_dsets\<Rightarrow>\<sigma>"
  met_ind_level::"(tvt_dsets\<Rightarrow>\<sigma>)\<Rightarrow>tvt_dsets\<Rightarrow>\<sigma>" 
  met_combination::"(tvt_dsets\<Rightarrow>\<sigma>)\<Rightarrow>tvt_dsets\<Rightarrow>\<sigma>" 
  rel_repr_errfree_compl::"tvt_dsets\<Rightarrow>\<sigma>" 
  have_appr_stat_prop_user_group::"tvt_dsets\<Rightarrow>\<sigma>" (*have statistical properties, where applicable, with regard to the 
  group of persons on which the system is intended to be used*)
  particularities_sys::"aiSys\<Rightarrow>particularities"
  take_into_account::"tvt_dsets\<Rightarrow>(aiSys\<Rightarrow>particularities)\<Rightarrow>aiSys\<Rightarrow>\<sigma>"
  strictly_necessary_bias_monitoring::"aiSys\<Rightarrow>\<sigma>"
  process_personal_data::"aiSys\<Rightarrow>\<sigma>" (*provider may process special data in relation to AI system*)
  devprocess::"aiSys\<Rightarrow>devproc" 
  devprocess_data::"devproc\<Rightarrow>data"
  employed'::"data\<Rightarrow>gov_and_man_practices" 

(*AI Act article 10, point 1-3*)
(*d = providers, as said in chapter 3, art 16, all these requirements are meant to be ensured by providers*)
abbreviation "A1 \<equiv> \<lfloor>\<^bold>\<forall>x. (high_risk x) \<^bold>\<and> (uses_techniques_training_w_data x) \<^bold>\<rightarrow> (\<^bold>\<circle>d<stit d (appropriate (employed (developed_with x)))>)\<rfloor>"
abbreviation "A2 \<equiv> \<lfloor>\<^bold>\<forall>p. (appropriate p) \<^bold>\<leftrightarrow> ((concerns_design p) \<^bold>\<and> (concerns_datacoll p) \<^bold>\<and> (concerns_dataprep p) \<^bold>\<and> 
  (concerns_form_assumptions p) \<^bold>\<and> (concerns_prior_assessment p) \<^bold>\<and> (concerns_examin_biases p) \<^bold>\<and> (concerns_ident_datagapy p))\<rfloor>"
abbreviation "A3 \<equiv> \<lfloor>\<^bold>\<forall>x. (high_risk x) \<^bold>\<and> (uses_techniques_training_w_data x) \<^bold>\<rightarrow> \<^bold>\<circle>d<stit d (rel_repr_errfree_compl (developed_with x))>\<rfloor>"
abbreviation "A4 \<equiv> \<lfloor>\<^bold>\<forall>x. (high_risk x) \<^bold>\<and> (uses_techniques_training_w_data x) \<^bold>\<rightarrow> 
  \<^bold>\<circle>d<stit d (have_appr_stat_prop_user_group (developed_with x))>\<rfloor>"
abbreviation "A5 \<equiv> \<lfloor>\<^bold>\<forall>t. (characteristics_met t) \<^bold>\<leftrightarrow> ((met_ind_level rel_repr_errfree_compl t) \<^bold>\<or> (met_combination rel_repr_errfree_compl t)) \<^bold>\<and> 
  ((met_ind_level have_appr_stat_prop_user_group t) \<^bold>\<or> (met_combination have_appr_stat_prop_user_group t))\<rfloor>"
abbreviation "A6 \<equiv> \<lfloor>\<^bold>\<forall>x. (high_risk x) \<^bold>\<and> (uses_techniques_training_w_data x) \<^bold>\<rightarrow> 
  \<^bold>\<circle>d<stit d (characteristics_met (developed_with x))>\<rfloor>"
abbreviation "theory1to3 \<equiv> A1 \<and> A2 \<and> A3 \<and> A4 \<and> A5 \<and> A6"

consts x::aiSys

(*Facts*)
abbreviation "F0 w \<equiv> (high_risk x) w"
abbreviation "F1 w \<equiv> (appropriate (employed (developed_with x))) w"
abbreviation "F2 w \<equiv> (uses_techniques_training_w_data x) w"
abbreviation "F3 w \<equiv> (\<^bold>\<not> (use_techniques_model_training_to_ensure_compliance x)) w"
abbreviation "F4 w \<equiv> (met_ind_level rel_repr_errfree_compl (developed_with x)) w"
abbreviation "F5 w \<equiv> (met_combination have_appr_stat_prop_user_group (developed_with x)) w"

theorem Result1: "theory1to3 \<longrightarrow> \<lfloor>(F0 \<^bold>\<and> F1 \<^bold>\<and> F2 \<^bold>\<and> F3) \<^bold>\<rightarrow> ((concerns_design (employed (developed_with x))) \<^bold>\<and> (concerns_datacoll (employed (developed_with x))) \<^bold>\<and> 
  (concerns_dataprep (employed (developed_with x))) \<^bold>\<and> (concerns_form_assumptions (employed (developed_with x))) \<^bold>\<and> (concerns_prior_assessment (employed (developed_with x))) \<^bold>\<and> 
  (concerns_examin_biases (employed (developed_with x))) \<^bold>\<and> (concerns_ident_datagapy (employed (developed_with x))))\<rfloor>"  
  by simp

theorem Result2: "theory1to3 \<longrightarrow> \<lfloor>(F4 \<^bold>\<and> F5) \<^bold>\<rightarrow> (characteristics_met (developed_with x))\<rfloor>"  
  by simp

theorem Result3: "theory1to3 \<longrightarrow> \<lfloor>(F0 \<^bold>\<and> F2 \<^bold>\<and> F1 \<^bold>\<and> F3) \<^bold>\<rightarrow> \<^bold>\<circle>d<(stit d (characteristics_met (developed_with x)))>\<rfloor>"  
  by auto

(*AI Act article 10, point 4-6*)
(*"to the extent required by purpose" is difficult to express*)
abbreviation "A7 \<equiv> \<lfloor>\<^bold>\<forall>x. (high_risk x) \<^bold>\<and> (uses_techniques_training_w_data x) \<^bold>\<rightarrow> 
  \<^bold>\<circle>d<stit d (take_into_account (developed_with x) particularities_sys x)>\<rfloor>"
(*point 5, hard to represent in detail, not complete*)
abbreviation "A8 \<equiv> \<lfloor>\<^bold>\<forall>x. (high_risk x) \<^bold>\<and> (uses_techniques_training_w_data x) \<^bold>\<and> 
  (strictly_necessary_bias_monitoring x) \<^bold>\<rightarrow>  \<^bold>\<not>\<^bold>\<circle>d<\<^bold>\<not> (stit d (process_personal_data x))>\<rfloor>"
abbreviation "A9 \<equiv> \<lfloor>\<^bold>\<forall>x. ((high_risk x) \<^bold>\<and> (uses_techniques_training_w_data x) \<^bold>\<and> (use_techniques_model_training_to_ensure_compliance x)) \<^bold>\<rightarrow> 
  \<^bold>\<not>(\<^bold>\<circle>d<(stit d (appropriate (employed' (devprocess_data (devprocess x)))))>)\<rfloor>"
abbreviation "A10 \<equiv> \<lfloor>\<^bold>\<forall>x. ((high_risk x) \<^bold>\<and> (uses_techniques_training_w_data x) \<^bold>\<and> (\<^bold>\<not>(use_techniques_model_training_to_ensure_compliance x))) \<^bold>\<rightarrow> 
  (\<^bold>\<circle>d<(stit d (appropriate (employed' (devprocess_data (devprocess x)))))>)\<rfloor>"
abbreviation "theory4to6 \<equiv> A7 \<and> A8 \<and> A9 \<and> A10"

consts pr::devproc

(*Facts*)
abbreviation "F6 w \<equiv> (strictly_necessary_bias_monitoring x) w"
abbreviation "F7 w \<equiv> (use_techniques_model_training_to_ensure_compliance x) w"
abbreviation "F8 w \<equiv> (\<^bold>\<not> (use_techniques_model_training_to_ensure_compliance x)) w"

theorem Result4: "(theory1to3 \<and> theory4to6) \<longrightarrow> \<lfloor>(F0 \<^bold>\<and> F2 \<^bold>\<and> F6) \<^bold>\<rightarrow> \<^bold>\<not> \<^bold>\<circle>d<(stit d (process_personal_data x))>\<rfloor>"  
  nitpick [user_axioms] (*counterexample found*) oops

theorem Result5: "(theory1to3 \<and> theory4to6) \<longrightarrow> \<lfloor>(F0 \<^bold>\<and> F2 \<^bold>\<and> F6) \<^bold>\<rightarrow> \<^bold>\<not> \<^bold>\<circle>d<(\<^bold>\<not> (stit d (process_personal_data x)))>\<rfloor>"  
  by simp

theorem Result6: "(theory1to3 \<and> theory4to6) \<longrightarrow> \<lfloor>(F0 \<^bold>\<and> F2 \<^bold>\<and> F1 \<^bold>\<and> F7) \<^bold>\<rightarrow> 
  \<^bold>\<not>(\<^bold>\<circle>d<(stit d (appropriate (employed' (devprocess_data (devprocess x)))))>)\<rfloor>" 
  by blast

theorem Result7: "(theory1to3 \<and> theory4to6) \<longrightarrow> \<lfloor>(F0 \<^bold>\<and> F1 \<^bold>\<and> F2 \<^bold>\<and> F8) \<^bold>\<rightarrow> 
  \<^bold>\<not>(\<^bold>\<circle>d<(stit d (appropriate (employed' (devprocess_data (devprocess x)))))>)\<rfloor>" 
  nitpick [user_axioms] (*counterexample found*) oops

(***Some Experiments***) 
lemma True nitpick [satisfy, user_axioms] oops (*Consistency-check: Nitpick finds a model.*)

end
