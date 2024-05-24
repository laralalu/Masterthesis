theory prohibited
  imports 
   DDL_agents
   types
begin

consts (*Predicates*)
  authorised::"aiSys\<Rightarrow>\<sigma>" (*system is authorised*)
  subliminal_technique::"aiSys\<Rightarrow>\<sigma>" (*deploys a subliminal technique beyond a person's consciousness*)
  has_consequence::"aiSys\<Rightarrow>consequence\<Rightarrow>\<sigma>" (*system has or may have a consequence*)
  real_time_bioid::"aiSys\<Rightarrow>\<sigma>" (*system is a real time bio identification system*)
  used_public_spaces::"aiSys\<Rightarrow>\<sigma>" (*system is planned to be used in public spaces*)
  used_law_enforcement::"aiSys\<Rightarrow>\<sigma>" (*system is planned to be used for law enforcement*)
  has_purpose::"aiSys\<Rightarrow>purpose\<Rightarrow>\<sigma>" (*system has a purpose*)
  strictly_necessary_for::"aiSys\<Rightarrow>purpose\<Rightarrow>\<sigma>" (*use of system is strictly necessary for a purpose*)
  consider_context::"aiSys\<Rightarrow>\<sigma>" (*context in which the system is used is considered*)
  consider_consequence::"aiSys\<Rightarrow>consequence\<Rightarrow>\<sigma>" (*specific consequence of the use of a system are considered*)
  consider_consequence_no_use::"aiSys\<Rightarrow>consequence\<Rightarrow>\<sigma>" (*specific consequence of not using the system are considered*)
  exploits_vulnerabilities_group::"aiSys\<Rightarrow>quality_person\<Rightarrow>\<sigma>" (*exploits a certain vulnerable quality of a group*)
  exploits_vulnerable_group::"aiSys\<Rightarrow>\<sigma>" (*exploits any of the vulnerabilities of a specific group due to a certain quality*)
  employed_by_pauthorities::"aiSys\<Rightarrow>\<sigma>" (*employed by public authorities or on their behalf*)
  complies_with_bio_id_rules::"aiSys\<Rightarrow>\<sigma>" (*system complies with specific safety rules*)
  authorised_prior::"aiSys\<Rightarrow>\<sigma>" (*systems is authorised before use*)
  authorised_during_after::"aiSys\<Rightarrow>\<sigma>" (*systems is authorised during or after use*)
  use_urgent::"aiSys\<Rightarrow>\<sigma>" (*use of system is urgent*)
  evidence_indications_necessary_proportionate::"aiSys\<Rightarrow>\<sigma>" (*evidence and indications are necessary and proportionate*)
  authorised_use_specified::"national_law\<Rightarrow>\<sigma>" (*national_law specifies the rules for the request, issuance, ad exercise of
  the authorisation for some real time bio id systems*)
  nl::national_law (*national law*)

(*AI1 Act Article 5, 1 + 2*)
(*helper: If x has consequence harm_psychological or harm_physical, we can generalize to harm*)
abbreviation "H1 \<equiv> \<lfloor>\<^bold>\<forall>x. ((has_consequence x harm_physical) \<^bold>\<or> 
(has_consequence x harm_psychological)) \<^bold>\<leftrightarrow> has_consequence x harm\<rfloor>"

(*helper: If either of the vulnerable qualities of a group is exploited by an ai system, then the system exploits a vulnerable group*)
abbreviation "H2 \<equiv> \<lfloor>\<^bold>\<forall>x. ((exploits_vulnerabilities_group x age) \<^bold>\<or> (exploits_vulnerabilities_group x physcial_disability)
\<^bold>\<or> (exploits_vulnerabilities_group x mental_disability)) \<^bold>\<leftrightarrow> exploits_vulnerable_group x\<rfloor>" 

abbreviation "A1 \<equiv> \<lfloor>\<^bold>\<forall>x. subliminal_technique x  \<^bold>\<and>  has_consequence x harm \<^bold>\<and> 
has_purpose x distort_behavior \<^bold>\<rightarrow> \<^bold>\<circle><prohibited x>\<rfloor>"

abbreviation "B1 \<equiv> \<lfloor>\<^bold>\<forall>x. exploits_vulnerable_group x \<^bold>\<and> has_purpose x distort_behavior \<^bold>\<and> 
has_consequence x harm \<^bold>\<rightarrow> \<^bold>\<circle><prohibited x>\<rfloor>" 

abbreviation "C1 \<equiv> \<lfloor>\<^bold>\<forall>x::aiSys. employed_by_pauthorities x \<^bold>\<and> has_purpose x eval_trustworthiness_over_time \<^bold>\<and> 
(has_consequence x detri_treatment_unrelated_context \<^bold>\<or> has_consequence x detri_treatment_unjustified_disprop)
\<^bold>\<rightarrow> \<^bold>\<circle><prohibited x>\<rfloor>"

abbreviation "D1a \<equiv> \<lfloor>\<^bold>\<forall>x. real_time_bioid x \<^bold>\<and> used_public_spaces x \<^bold>\<and> used_law_enforcement x \<^bold>\<and> 
(((has_purpose x targeted_search) \<^bold>\<and> (\<^bold>\<not>(strictly_necessary_for x targeted_search))) \<^bold>\<or>
((has_purpose x detection) \<^bold>\<and> (\<^bold>\<not>(strictly_necessary_for x detection))) \<^bold>\<or> ((has_purpose x prevention) \<^bold>\<and> 
(\<^bold>\<not>(strictly_necessary_for x prevention)))) \<^bold>\<rightarrow> \<^bold>\<circle><prohibited x>\<rfloor>"

(*implicit: not prohibited*)
abbreviation "D1b \<equiv> \<lfloor>\<^bold>\<forall>x. real_time_bioid x \<^bold>\<and> used_public_spaces x \<^bold>\<and> used_law_enforcement x \<^bold>\<and> 
(((has_purpose x targeted_search) \<^bold>\<and> (strictly_necessary_for x targeted_search)) \<^bold>\<or>
((has_purpose x detection) \<^bold>\<and> (strictly_necessary_for x detection)) \<^bold>\<or> ((has_purpose x prevention) \<^bold>\<and> 
(strictly_necessary_for x prevention))) \<^bold>\<rightarrow> (\<^bold>\<not>(\<^bold>\<circle><prohibited x>) \<^bold>\<and> (\<^bold>\<circle><high_risk x>))\<rfloor>"

abbreviation "A2a \<equiv> \<lfloor>\<^bold>\<forall>x. real_time_bioid x \<^bold>\<and> used_public_spaces x \<^bold>\<and> used_law_enforcement x \<^bold>\<and> 
(((has_purpose x targeted_search) \<^bold>\<and> (strictly_necessary_for x targeted_search)) \<^bold>\<or>
((has_purpose x detection) \<^bold>\<and> (strictly_necessary_for x detection)) \<^bold>\<or> ((has_purpose x prevention) \<^bold>\<and> 
(strictly_necessary_for x prevention))) \<^bold>\<rightarrow> \<^bold>\<circle><consider_consequence_no_use x harm_psychological> \<^bold>\<and>
 \<^bold>\<circle><consider_consequence_no_use x harm_physical>\<rfloor>"

abbreviation "A2b \<equiv> \<lfloor>\<^bold>\<forall>x. real_time_bioid x \<^bold>\<and> used_public_spaces x \<^bold>\<and> used_law_enforcement x \<^bold>\<and>
(((has_purpose x targeted_search) \<^bold>\<and> (strictly_necessary_for x targeted_search)) \<^bold>\<or> (((has_purpose x prevention) \<^bold>\<and> 
(strictly_necessary_for x prevention))) \<^bold>\<or> (((has_purpose x detection) \<^bold>\<and> (strictly_necessary_for x detection))))
\<^bold>\<rightarrow> \<^bold>\<circle><consider_consequence x affect_personal_rights> \<^bold>\<and> \<^bold>\<circle><consider_consequence x affect_personal_freedom>\<rfloor>" 

abbreviation "A2c \<equiv> \<lfloor>\<^bold>\<forall>x. real_time_bioid x \<^bold>\<and> used_public_spaces x \<^bold>\<and> used_law_enforcement x \<^bold>\<and>
(((has_purpose x targeted_search) \<^bold>\<and> (strictly_necessary_for x targeted_search)) \<^bold>\<or> (((has_purpose x prevention) \<^bold>\<and> 
(strictly_necessary_for x prevention))) \<^bold>\<or> (((has_purpose x detection) \<^bold>\<and> (strictly_necessary_for x detection))))
\<^bold>\<rightarrow> \<^bold>\<circle><complies_with_bio_id_rules x>\<rfloor>"

abbreviation "theory_1_2 \<equiv> H1 \<and> H2 \<and> A1 \<and> B1 \<and> C1 \<and> D1a \<and> D1b \<and> A2a \<and> A2b \<and> A2c"

(*Facts, Article 5, 1 + 2*)
consts
  x::aiSys 
  z::aiSys

abbreviation "F1 w \<equiv> (subliminal_technique x) w"
abbreviation "F2 w \<equiv> (has_consequence x harm_physical) w"
abbreviation "F3 w \<equiv> (has_purpose x distort_behavior) w"
abbreviation "F4 w \<equiv> (real_time_bioid z) w"
abbreviation "F5 w \<equiv> (used_public_spaces z) w"
abbreviation "F6 w \<equiv> (used_law_enforcement z) w"
abbreviation "F7 w \<equiv> (has_purpose z targeted_search) w" 
abbreviation "F8 w \<equiv> \<not>(strictly_necessary_for z targeted_search) w"
abbreviation "F9 w \<equiv> (strictly_necessary_for z targeted_search) w"

abbreviation "facts_1_2 \<equiv> F1 \<^bold>\<and> F2 \<^bold>\<and> F3 \<^bold>\<and> F4 \<^bold>\<and> F5 \<^bold>\<and> F6 \<^bold>\<and> F7 \<^bold>\<and> F8 \<^bold>\<and> F9"

theorem Result1a: "H1 \<and> H2 \<and> A1 \<and> B1 \<and> C1 \<longrightarrow> \<lfloor>(F1 \<^bold>\<and> F2 \<^bold>\<and> F3)  \<^bold>\<rightarrow> (\<^bold>\<circle><prohibited x>)\<rfloor>"  
  by metis

theorem Result1b: "H1 \<and> H2 \<and> A1 \<and> B1 \<and> C1 \<longrightarrow> \<lfloor>F1 \<^bold>\<and> F2  \<^bold>\<rightarrow> (\<^bold>\<circle><prohibited x>)\<rfloor>"  
  nitpick [user_axioms] oops (*counterexample found*) 

(*Consistency confirmed by model finder Nitpick.*) 
lemma True nitpick[satisfy,user_axioms,show_all,expect=genuine] oops

theorem Result2a: "D1a \<and> D1b \<and> A2a \<and> A2b \<and> A2c \<longrightarrow> \<lfloor>F4 \<^bold>\<and> F5 \<^bold>\<and> F6 \<^bold>\<and> F7 \<^bold>\<and> F8 \<^bold>\<rightarrow> (\<^bold>\<circle><prohibited z>)\<rfloor>"
  by meson

theorem Result2b: "D1a \<and> D1b \<and> A2a \<and> A2b \<and> A2c \<longrightarrow> \<lfloor>F4 \<^bold>\<and> F5 \<^bold>\<and> F6 \<^bold>\<and> F7 \<^bold>\<and> F9 \<^bold>\<rightarrow> (\<^bold>\<circle><prohibited z>)\<rfloor>"
  nitpick [user_axioms] (*counterexample found*) oops

(*Consistency confirmed by model finder Nitpick.*) 
lemma True nitpick[satisfy,user_axioms,show_all,expect=genuine] oops

(*works!*)

end

