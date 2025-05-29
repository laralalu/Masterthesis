theory Prova_AIACT imports Main
begin
declare[[syntax_ambiguity_warning=false]]
declare[[show_types]]

typedecl i (*Type for possible worlds.*) 
type_synonym \<sigma> = "(i\<Rightarrow>bool)"
type_synonym \<gamma> = "\<sigma>\<Rightarrow>\<sigma>" 
type_synonym \<rho> = "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"

(*SDL_agents/ Dstit_Deontic types*)
typedecl ag (*Type for agents*)
type_synonym \<tau> = "(i\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" 
type_synonym \<kappa> = "(ag\<Rightarrow>i\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" 

type_synonym \<nu> = "(\<sigma>\<Rightarrow>(\<sigma>\<Rightarrow>bool))\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"
type_synonym \<mu> = "(\<sigma>\<Rightarrow>(\<sigma>\<Rightarrow>bool))\<Rightarrow>(i\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"
type_synonym \<zeta> = "(i\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"

type_synonym \<delta> = "i\<Rightarrow>i\<Rightarrow>bool" (* type of accessibility relations between worlds Dstit_Deontic*)

type_synonym \<chi> = "ag\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"
type_synonym \<eta> = "ag\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" 

(*prohibited*)
typedecl aiSys (*Type for AI-systems*)
datatype quality_person = age | physical_disability | mental_disability (*quality of a person*)
datatype consequence = harm | harm_physical | harm_psychological | detri_treatment_unrelated_context | 
detri_treatment_unjustified_disprop | affect_personal_rights | affect_personal_freedom (*type for consequences caused by AI-systems*)
datatype purpose = distort_behavior | exploit_groups | eval_trustworthiness_over_time | targeted_search | 
prevention | detection (*type for purposes of AI-systems*)

consts
   prohibited::"aiSys\<Rightarrow>\<sigma>" (*system is declared prohibited*)
   high_risk::"aiSys\<Rightarrow>\<sigma>" (*system is declared a high-risk system*)

typedecl national_law  (*national law of member states*) 

(*high-risk-3-1-6-7*)
(*degree of a quality, strength*)
datatype degree = low | medium | high

(*high-risk-3-2-8-9*)
typedecl rms (*risk-management-system*)
typedecl soa (*state of art*)
datatype risk = data_leak | incorrect_info | discrimination (*risks posed by an AI system*)
(*high-risk-3-2-10*)
typedecl tvt_dsets (*training, validation, testing data sets*)
typedecl data (*generic data*)
typedecl gov_and_man_practices (*appropriate governance and management practices*)
typedecl particularities (*specific geographical, behavioural or functional setting within which the 
high-risk AI system is intended to be used*)
typedecl devproc (*development process Art10, point 6*)

(*high-risk-3-3-27*)
typedecl stor_tra_conditions (*storage or transport conditions*)

(*high-risk-3-4-31*)
typedecl appl_nb (*application for notification*)

(*high-risk-3-5-44*)
typedecl certificate (*certificate by notified body*)

(*chapter3_17*)
typedecl qualManSys (*quality management system*)
datatype standard = harm_stand_art_40 (*standards that must be considered*)
datatype size = small | medium | large (*size of provider's organisation*)


consts
    (*identify agents:*)
    eu_comm::ag
    provider::"ag\<Rightarrow>\<sigma>"
    importer::"ag\<Rightarrow>\<sigma>"
    notif_authority::"ag\<Rightarrow>\<sigma>" 
    member_state::"ag\<Rightarrow>\<sigma>"  
    conf_ass_body::"ag\<Rightarrow>\<sigma>" 

(*Article 32: mult_AgTests_2*)
typedecl notification (*notification of a conformity assessment body*)

consts
 cw::i (*current world*)
 av::"i\<Rightarrow>\<sigma>" pv::"i\<Rightarrow>\<sigma>" ob::"\<sigma>\<Rightarrow>(\<sigma>\<Rightarrow>bool)" (*general accessibility relations, resp. for actual version of the world (av), 
potential version (pv), and obligation*)

 av_g::"ag\<Rightarrow>i\<Rightarrow>\<sigma>" pv_g::"ag\<Rightarrow>i\<Rightarrow>\<sigma>" ob_g::"ag\<Rightarrow>(\<sigma>\<Rightarrow>(\<sigma>\<Rightarrow>bool))" (*agent-dependent accessibility relations*)
  
 (*stit operator*) 
 stit::"ag\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (*ag sees to it that*)


axiomatization where
 ax_3a: "\<forall>w.\<exists>x. av(w)(x)" and ax_4a: "\<forall>w x. av(w)(x) \<longrightarrow> pv(w)(x)" and ax_4b: "\<forall>w. pv(w)(w)" and
 ax_5a: "\<forall>X.\<not>ob(X)(\<lambda>x. False)" and
 ax_5b: "\<forall>X Y Z. (\<forall>w. ((Y(w) \<and> X(w)) \<longleftrightarrow> (Z(w) \<and> X(w)))) \<longrightarrow> (ob(X)(Y) \<longleftrightarrow> ob(X)(Z))" and
 ax_5c: "\<forall>X Y Z. (((\<exists>w. (X(w) \<and> Y(w) \<and> Z(w))) \<and>  ob(X)(Y)  \<and>  ob(X)(Z))  \<longrightarrow>  ob(X)(\<lambda>w. Y(w) \<and> Z(w)))" and
 ax_5ca: "\<forall>X \<beta>. ((\<forall>Z. \<beta>(Z) \<longrightarrow> ob(X)(Z)) \<and> (\<exists>Z. \<beta>(Z))) \<longrightarrow> 
      (((\<exists>y. ((\<lambda>w. \<forall>Z. (\<beta> Z) \<longrightarrow> (Z w))(y) \<and> X(y))) \<longrightarrow> ob(X)(\<lambda>w. \<forall>Z. (\<beta> Z) \<longrightarrow> (Z w))))" and
 ax_5d: "\<forall>X Y Z. ((\<forall>w. Y(w) \<longrightarrow> X(w)) \<and> ob(X)(Y) \<and> (\<forall>w. X(w) \<longrightarrow> Z(w)))
                   \<longrightarrow> ob(Z)(\<lambda>w. (Z(w) \<and> \<not>X(w)) \<or> Y(w))" (*Upward propagation of dutes*) and
 ax_5e: "\<forall>X Y Z. ((\<forall>w. Y(w) \<longrightarrow> X(w)) \<and> ob(X)(Z) \<and> (\<exists>w. Y(w) \<and> Z(w))) \<longrightarrow> ob(Y)(Z)" 
(*monotonicity: adding further conditions (that don’t conflict with the obligation) cannot negate the obligation*) and 

(*Instead of the agent variants of the DDL axioms, we introduce the following bridging axioms:*)

bridgingAE: "\<forall>X Y. \<exists> a. (ob(X)(Y)) \<longrightarrow> ob_g a (X)(Y)" and

(*bridgingAA: "\<forall>X Y a. (ob(X)(Y)) \<longrightarrow> ob_g a (X)(Y)" and*) 

 stit1: "\<forall>a F w. ((stit a F) w) \<longrightarrow> F w"

text \<open>The AA version of the bridging axiom is excluded because might be too strict because typically, 
an obligation is assigned to a specific role (e.g. “the provider shall ensure ...”), not literally to every agent. 
Imposing an AA bridging could over-constrain the models by forcing even irrelevant agents to carry each obligation, 
potentially trivializing the case by making ob and ob_g indistinguishable\<close>

 (* Consistency *) 
 lemma True nitpick [satisfy,user_axioms,show_all,card i=2, card ag = 10] oops (*But no model for card i > 2*)


 abbreviation ddlneg::\<gamma> ("\<^bold>\<not>_"[52]53) where "\<^bold>\<not>A \<equiv> \<lambda>w. \<not>A(w)" 
 abbreviation ddland::\<rho> (infixr"\<^bold>\<and>"51) where "A\<^bold>\<and>B \<equiv> \<lambda>w. A(w)\<and>B(w)"   
 abbreviation ddlor::\<rho> (infixr"\<^bold>\<or>"50) where "A\<^bold>\<or>B \<equiv> \<lambda>w. A(w)\<or>B(w)"   
 abbreviation ddlimp::\<rho> (infixr"\<^bold>\<rightarrow>"49) where "A\<^bold>\<rightarrow>B \<equiv> \<lambda>w. A(w)\<longrightarrow>B(w)"  
 abbreviation ddlequiv::\<rho> (infixr"\<^bold>\<leftrightarrow>"48) where "A\<^bold>\<leftrightarrow>B \<equiv> \<lambda>w. A(w)\<longleftrightarrow>B(w)"  
 abbreviation ddlbox::\<gamma> ("\<^bold>\<box>") where "\<^bold>\<box>A \<equiv> \<lambda>w.\<forall>v. A(v)" 
 abbreviation ddldia::\<gamma>  ("\<^bold>\<diamond>") where "\<^bold>\<diamond> A \<equiv> \<^bold>\<not>\<^bold>\<box>(\<^bold>\<not>A)"

 (*Necessity/possibility for agents*)
 abbreviation ddlboxa_g::\<eta> ("\<^bold>\<box>\<^sub>a") where "\<^bold>\<box>\<^sub>a i A \<equiv> \<lambda>w. (\<forall>x. av_g i (w)(x) \<longrightarrow> A(x))"  (*in all actual worlds*)
 abbreviation ddlboxp_g::\<eta> ("\<^bold>\<box>\<^sub>p") where "\<^bold>\<box>\<^sub>p i A \<equiv> \<lambda>w. (\<forall>x. pv_g i (w)(x) \<longrightarrow> A(x))" (*in all potential worlds*)
 abbreviation ddldiaa_g::\<eta> ("\<^bold>\<diamond>\<^sub>a") where "\<^bold>\<diamond>\<^sub>a i A \<equiv> \<^bold>\<not>\<^bold>\<box>\<^sub>a i (\<^bold>\<not>A)"
 abbreviation ddldiap_g::\<eta> ("\<^bold>\<diamond>\<^sub>p") where "\<^bold>\<diamond>\<^sub>p i A \<equiv> \<^bold>\<not>\<^bold>\<box>\<^sub>p i (\<^bold>\<not>A)"
 (*generalised operators with agents as a parameter*)
 abbreviation ddlo_g::\<chi> ("\<^bold>O _ \<^bold>\<langle>_\<^bold>|_\<^bold>\<rangle>") where "\<^bold>O i \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<equiv> \<lambda>w. ob_g i A B"  (*Agent i ought to A, given B *)
abbreviation ddloa_g::\<eta>  ("\<^bold>O\<^sub>a _ ") where "\<^bold>O\<^sub>a i A \<equiv> \<lambda>w. ob_g i (av_g i (w))(A) \<and> (\<exists>x. av_g i (w)(x) \<and> \<not>A(x))" 
(*actual obligation*)
abbreviation ddlop_g::\<eta>  ("\<^bold>O\<^sub>p _") where "\<^bold>O\<^sub>p i A \<equiv> \<lambda>w. ob_g i (pv_g i (w))(A) \<and> (\<exists>x. pv_g i (w)(x) \<and> \<not>A(x))"  
(*primary obligation*)

 (*non-agentive necessity, possibility and obligation operators*)
 abbreviation ddlboxa::\<gamma> ("\<^bold>\<box>\<^sub>a") where "\<^bold>\<box>\<^sub>aA \<equiv> \<lambda>w. (\<forall>x. av(w)(x) \<longrightarrow> A(x))"  (*in all actual worlds*)
 abbreviation ddlboxp::\<gamma> ("\<^bold>\<box>\<^sub>p") where "\<^bold>\<box>\<^sub>pA \<equiv> \<lambda>w. (\<forall>x. pv(w)(x) \<longrightarrow> A(x))" (*in all potential worlds*)
 abbreviation ddldiaa::\<gamma> ("\<^bold>\<diamond>\<^sub>a") where "\<^bold>\<diamond>\<^sub>aA \<equiv> \<^bold>\<not>\<^bold>\<box>\<^sub>a(\<^bold>\<not>A)"
 abbreviation ddldiap::\<gamma> ("\<^bold>\<diamond>\<^sub>p") where "\<^bold>\<diamond>\<^sub>pA \<equiv> \<^bold>\<not>\<^bold>\<box>\<^sub>p(\<^bold>\<not>A)" 
 abbreviation ddlo::\<rho> ("\<^bold>O\<^bold>\<langle>_\<^bold>|_\<^bold>\<rangle>"[52]53) where "\<^bold>O\<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<equiv> \<lambda>w. ob(A)(B)"  (*it ought to be \<psi>, given \<phi> *)
 abbreviation ddloa::\<gamma>  ("\<^bold>O\<^sub>a") where "\<^bold>O\<^sub>aA \<equiv> \<lambda>w. ob(av(w))(A) \<and> (\<exists>x. av(w)(x) \<and> \<not>A(x))" (*actual obligation*)
 abbreviation ddlop::\<gamma>  ("\<^bold>O\<^sub>p") where "\<^bold>O\<^sub>pA \<equiv> \<lambda>w. ob(pv(w))(A) \<and> (\<exists>x. pv(w)(x) \<and> \<not>A(x))"  (*primary obligation*)

 abbreviation ddltop::\<sigma> ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<lambda>w. True"
 abbreviation ddlbot::\<sigma> ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"

 (*New syntax *)
 abbreviation ddlobl::\<gamma> ("\<^bold>\<circle><_>") where "\<^bold>\<circle><A> \<equiv>  \<^bold>O\<^bold>\<langle>A\<^bold>|\<^bold>\<top>\<^bold>\<rangle>" 
 abbreviation ddlobl_g::\<eta> ("\<^bold>\<circle>_<_>") where "\<^bold>\<circle> i <A> \<equiv>  \<^bold>O i \<^bold>\<langle>A\<^bold>|\<^bold>\<top>\<^bold>\<rangle>"


(*Possibilist Quantification.*)
 abbreviation ddlforall ("\<^bold>\<forall>") where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>w.\<forall>x. (\<Phi> x w)"
 abbreviation ddlforallB (binder"\<^bold>\<forall>"[8]9) where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"  
 abbreviation ddlexists ("\<^bold>\<exists>") where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>w.\<exists>x. (\<Phi> x w)"   
 abbreviation ddlexistsB (binder"\<^bold>\<exists>"[8]9) where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>" 

 abbreviation ddlvalid::"\<sigma> \<Rightarrow> bool" ("\<lfloor>_\<rfloor>"[7]105) where "\<lfloor>A\<rfloor> \<equiv> \<forall>w. A w"   (*Global validity*)
 abbreviation ddlvalidcw::"\<sigma> \<Rightarrow> bool" ("\<lfloor>_\<rfloor>\<^sub>l"[7]105) where "\<lfloor>A\<rfloor>\<^sub>l \<equiv> A cw" (*Local validity (in cw)*)



(*CTD example extended DDL2:*)
consts 
  d::ag 
  l::aiSys
  provider_of::"ag\<Rightarrow>aiSys\<Rightarrow>\<sigma>"
  compliance_req_chap2::"aiSys\<Rightarrow>\<sigma>"
  inform_authorities::"aiSys\<Rightarrow>\<sigma>" 

axiomatization where
(*rules, e.g. CTD*)
A1: "\<lfloor>\<^bold>\<forall>x p. (high_risk x \<^bold>\<and> provider p \<^bold>\<and> provider_of p x) \<^bold>\<rightarrow> \<^bold>\<circle>p<stit p (compliance_req_chap2 x)>\<rfloor>" and
A8: "\<lfloor>\<^bold>\<forall>x p. (high_risk x \<^bold>\<and> provider p \<^bold>\<and> provider_of p x) \<^bold>\<rightarrow> (\<^bold>\<not> (compliance_req_chap2 x)
 \<^bold>\<rightarrow> \<^bold>\<circle>p<(stit p (inform_authorities x))>)\<rfloor>" and
(*implicit: If the compliance with the requirements is a given, the provider is obligated to not inform authorities 
of non-compliance (since that would make no sense*)
AX: "\<lfloor>\<^bold>\<forall>x p. (high_risk x \<^bold>\<and> provider p \<^bold>\<and> provider_of p x) \<^bold>\<rightarrow> (\<^bold>\<circle>p<(compliance_req_chap2 x)
 \<^bold>\<rightarrow> \<^bold>\<not> stit p (inform_authorities x)>)\<rfloor>" and

(*facts*)
F1: "\<lfloor>(high_risk l)\<rfloor>\<^sub>l" and 
F2: "\<lfloor>(provider d)\<rfloor>\<^sub>l" and  
F3: "\<lfloor>(provider_of d l)\<rfloor>\<^sub>l" and
Situation: "\<lfloor>\<^bold>\<not> (compliance_req_chap2 l)\<rfloor>\<^sub>l"

(***Some Experiments***) 
lemma True nitpick [satisfy, user_axioms, show_all, card i=2, card ag=10]  oops

lemma "\<lfloor>\<^bold>\<circle>d<stit d (inform_authorities l)>\<rfloor>\<^sub>l" using A8 F1 F2 F3 Situation by blast
lemma "\<lfloor>\<^bold>\<circle>d<\<^bold>\<not> stit d (inform_authorities l)>\<rfloor>\<^sub>l" nitpick
  [ user_axioms = true, show_all, expect = genuine, card i= 2,card ag= 2, card aiSys= 1,timeout = 120 ] oops (*ctm*)

end