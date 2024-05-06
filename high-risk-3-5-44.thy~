theory "high-risk-3-5-44"
  imports 
  types
  DDL_agents
begin

consts
  certVII::certificate (*certificate in accordance with Annex VII*)
  draw_up_cert_in_official_lang::"certificate\<Rightarrow>aiSys\<Rightarrow>\<sigma>" 
  valid_as_indicated::"certificate\<Rightarrow>aiSys\<Rightarrow>\<sigma>" 
  valid_max_five_years::"certificate\<Rightarrow>aiSys\<Rightarrow>\<sigma>" 
  ext_request_by_provider::"certificate\<Rightarrow>aiSys\<Rightarrow>\<sigma>" 
  re_assessment::"certificate\<Rightarrow>aiSys\<Rightarrow>\<sigma>" 
  extend_period_under_five_years::"certificate\<Rightarrow>aiSys\<Rightarrow>\<sigma>"
  suspend_or_withdraw_certificate_prop::"certificate\<Rightarrow>aiSys\<Rightarrow>\<sigma>"
  impose_restrictions::"aiSys\<Rightarrow>\<sigma>"
  deadline_corr_ac_given_provider::"aiSys\<Rightarrow>\<sigma>"
  deadline_given::"aiSys\<Rightarrow>\<sigma>"
  deadline_over::"aiSys\<Rightarrow>\<sigma>"
  give_reasons_dec_on::"aiSys\<Rightarrow>\<sigma>"

  (*needed from other chapters*)
  meets_requirements_chap2::"aiSys\<Rightarrow>\<sigma>"
  certificate_provided::"aiSys\<Rightarrow>\<sigma>"

(*agent g: notified body*)
(*notified body is obligated to see to it that the certificate is given for a system only if the system meets 
the requirements*)
abbreviation "A0 \<equiv> \<lfloor>\<^bold>\<forall>x. \<^bold>\<circle>g<stit g (certificate_provided x)> \<^bold>\<leftrightarrow> (meets_requirements_chap2 x)\<rfloor>"
abbreviation "A1 \<equiv> \<lfloor>\<^bold>\<forall>x. \<^bold>\<circle>g<(stit g (draw_up_cert_in_official_lang certVII x))>\<rfloor>"
abbreviation "A2 \<equiv> \<lfloor>\<^bold>\<forall>x. \<^bold>\<circle><(valid_as_indicated certVII x)> \<^bold>\<and> \<^bold>\<circle><(valid_max_five_years certVII x)>\<rfloor>"
abbreviation "A3 \<equiv> \<lfloor>\<^bold>\<forall>x. (ext_request_by_provider certVII x) \<^bold>\<and> (re_assessment certVII x)\<^bold>\<rightarrow>
  \<^bold>\<not>(\<^bold>\<circle>g<\<^bold>\<not> stit g (extend_period_under_five_years certVII x)>)\<rfloor>"
abbreviation "A4 \<equiv> \<lfloor>\<^bold>\<forall>x. \<^bold>\<not>(meets_requirements_chap2 x) \<^bold>\<and> (certificate_provided x)  \<^bold>\<rightarrow> 
  \<^bold>\<circle>g<(stit g (deadline_corr_ac_given_provider x))>\<rfloor>"
abbreviation "A5 \<equiv> \<lfloor>\<^bold>\<forall>x. (stit g (deadline_corr_ac_given_provider x)) \<^bold>\<rightarrow> (deadline_given x)\<rfloor>"
abbreviation "A6 \<equiv> \<lfloor>\<^bold>\<forall>x. (deadline_given x) \<^bold>\<and> (deadline_over x)  \<^bold>\<rightarrow> 
  \<^bold>\<circle>g<(stit g (suspend_or_withdraw_certificate_prop certVII x))>\<rfloor>"
abbreviation "A7 \<equiv> \<lfloor>\<^bold>\<forall>x. stit g (suspend_or_withdraw_certificate_prop certVII x) \<^bold>\<rightarrow> 
\<^bold>\<circle>g<(stit g (give_reasons_dec_on x))>\<rfloor>"