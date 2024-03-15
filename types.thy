theory types     
  imports Main 
begin

typedecl aiSys (*Type for AI-Systems*)
typedecl member_state (*Type for EU member states*)
typedecl juridicial_authority (*Type for the juridicial authority deciding within a member state*)
datatype size = small | medium | large (*size of provider's organisation*)
typedecl qualManSys (*quality management system*)
typedecl national_competent_authority
datatype standard = harm_stand_art_40 

(*Type for purposes of AI-Systems*)
datatype purpose = distort_behavior | exploit_groups | eval_trustworthiness_over_time | targeted_search | 
prevention | detection

(*Type for consequences caused by AI-Systems*)
datatype consequence = harm | harm_physical | harm_psychological | detri_treatment_unrelated_context | 
detri_treatment_unjustified_disprop | affect_personal_rights | affect_personal_freedom

(*quality of a person*)
datatype quality_person = age | physcial_disability | mental_disability

(*Type for situation in which AI-System is used*)
datatype situation = private_place | public 
datatype authority =  judicial_authority | independent_admin_authority

(*datatype safety_guidelines = bioid_rules*)
type_synonym safety_rules = "aiSys \<Rightarrow> bool" 

datatype agent = eu_comm | juridicial_auth | admin_auth | provider | nat_comp_auth
datatype degree = low | medium | high

(*type_synonym safety_guidelines = "safety_rules \<Rightarrow> bool"*)
consts 
   bioid_rules::safety_rules (*necessary and proportionate safeguards and conditions in relation to the use, in particular
   as regards the temporal, geographic and personal limitations*)
   national_rules_authorisation::safety_rules

end