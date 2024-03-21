theory types     
  imports Main 
begin

typedecl i (*Type for possible worlds.*) 
typedecl ag
type_synonym \<sigma> = "(i\<Rightarrow>bool)"
type_synonym \<gamma> = "\<sigma>\<Rightarrow>\<sigma>" 
type_synonym \<rho> = "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"
type_synonym \<tau> = "(i\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" 
type_synonym \<kappa> = "(ag\<Rightarrow>i\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" 
type_synonym \<mu> = "(\<sigma>\<Rightarrow>(\<sigma>\<Rightarrow>bool))\<Rightarrow>(i\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"
type_synonym \<nu> = "(\<sigma>\<Rightarrow>(\<sigma>\<Rightarrow>bool))\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"

(*Recurring types needed for AI-systems*)
typedecl aiSys (*Type for AI-systems*)
typedecl qualManSys (*quality management system*)
typedecl rms (*risk-management-system*)
typedecl certificate (*certificate by notified body*)
typedecl bioid_rules (*specified rules for real time bio identification systems*)
typedecl national_law  (*national law of member states*) 
typedecl soa (*state of art*)
typedecl appl_nb (*application for notification*)

(*standards that must be considered*)
datatype standard = harm_stand_art_40 
(*size of provider's organisation*)
datatype size = small | medium | large 
(*Type for purposes of AI-systems*)
datatype purpose = distort_behavior | exploit_groups | eval_trustworthiness_over_time | targeted_search | 
prevention | detection
(*Type for risks caused by AI-sytems*)
datatype risk = data_leak | incorrect_info | discrimination
(*Type for consequences caused by AI-systems*)
datatype consequence = harm | harm_physical | harm_psychological | detri_treatment_unrelated_context | 
detri_treatment_unjustified_disprop | affect_personal_rights | affect_personal_freedom
(*quality of a person*)
datatype quality_person = age | physcial_disability | mental_disability
(*Type for situation in which AI-System is used*)
datatype situation = private_place | public 
datatype authority =  judicial_authority | independent_admin_authority
(*degree of a quality, strength*)
datatype degree = low | medium | high

consts 
   prohibited :: "aiSys \<Rightarrow> \<sigma>" (*system is prohibited*)
   high_risk :: "aiSys \<Rightarrow> \<sigma>" (*system is a high-risk system*)


(*identify agents:*)
  a::ag (*a*)
  b::ag (*b*)   
  c::ag (*c*)
  d::ag (*d*)
  e::ag (*e*)
  f::ag (*f*)
  g::ag (*g*)
  h::ag (*h*)
  j::ag (*j*)
  
(*
   a (*Agent type for judicial authorities or independent administrative authorities*)
   b (*Agent type for importer*)
   c (*Agent type for the EU commission*)
   d (*Agent type for providers*)
   e (*Agent type for conformity assessment bodies*)
   f (*Agent type for notifying authorities*)
   g (*Agent type for notified bodies*)
   h (*Agent type for members state*)
   j (*Agent type for national competent authority*)
*)
end