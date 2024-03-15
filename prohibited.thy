theory prohibited
  imports 
   SDL_agents
   types
begin

consts (*Predicates/relations*)
  subliminal_technique::"aiSys\<Rightarrow>\<sigma>" (*deploys a subliminal technique beyond a persons consciousness*)
  has_consequence::"aiSys\<Rightarrow>consequence\<Rightarrow>\<sigma>" (*system has or may have a consequence*)
  has_purpose::"aiSys\<Rightarrow>purpose\<Rightarrow>\<sigma>" (*system has a purpose*)
  exploits_vulnerabilities_group::"aiSys\<Rightarrow>quality_person\<Rightarrow>\<sigma>" 
  exploits_vulnerable_group::"aiSys\<Rightarrow>\<sigma>"
  (*exploits any of the vulnerabilities of a specific group due to a certain quality*)
  employed_by_pauthorities::"aiSys\<Rightarrow>\<sigma>" (*employed by public authorities or on their behalf*)
  real_time_bioid::"aiSys\<Rightarrow>\<sigma>" (*system is a real time bio identification system*)
  use_public_spaces::"aiSys\<Rightarrow>\<sigma>" (*system is planned to be used in public spaces*)
  use_law_enforcement::"aiSys\<Rightarrow>\<sigma>" (*system is used for law enforcement*)
  strictly_necessary_for::"aiSys\<Rightarrow>purpose\<Rightarrow>\<sigma>" (*use of system is strictly necessary for a purpose*)
  consider_consequence::"aiSys\<Rightarrow>consequence\<Rightarrow>\<sigma>" (*consider specific consequence of the use of a system*)
  consider_consequence_no_use::"aiSys\<Rightarrow>consequence\<Rightarrow>\<sigma>" (*consider specific consequence of not using the system*)
  consider_context::"aiSys\<Rightarrow>\<sigma>" (*consider the context in which the system is used*)
  comply_with::"aiSys\<Rightarrow>safety_rules\<Rightarrow>\<sigma>" (*system complies with specific safety rules*)
  authorise_prior::"aiSys\<Rightarrow>\<sigma>" (*systems is authorised before use*)
  authorise_during_after::"aiSys\<Rightarrow>\<sigma>" (*systems is authorised during or after use*)
  authorise::"aiSys\<Rightarrow>\<sigma>"
  use_urgent::"aiSys\<Rightarrow>\<sigma>"
  evidence_indications_necessary_proportionate::"aiSys\<Rightarrow>\<sigma>"
  specify_authorised_use::"safety_rules\<Rightarrow>\<sigma>"

  prohibited :: "aiSys \<Rightarrow> \<sigma>" (*placing on market, putting into service, or use*)
  high_risk :: "aiSys \<Rightarrow> \<sigma>"

  x::aiSys 
  z::aiSys

(*Ai Act Article 5, 1 + 2*)
(*helper: If x has consequence harm_psychological or harm_physical, we can generalize to harm*)
abbreviation "H1 \<equiv> \<lfloor>\<^bold>\<forall>x::aiSys. ((has_consequence x harm_physical) \<^bold>\<or> 
(has_consequence x harm_psychological)) \<^bold>\<leftrightarrow> has_consequence x harm\<rfloor>"

abbreviation "A1 \<equiv> \<lfloor>\<^bold>\<forall>x::aiSys. subliminal_technique x  \<^bold>\<and>  has_consequence x harm \<^bold>\<and> 
has_purpose x distort_behavior \<^bold>\<rightarrow> \<^bold>\<circle><prohibited x>\<rfloor>"

(*helper*)
abbreviation "H2 \<equiv> \<lfloor>\<^bold>\<forall>x::aiSys. ((exploits_vulnerabilities_group x age) \<^bold>\<or> (exploits_vulnerabilities_group x physcial_disability)
\<^bold>\<or> (exploits_vulnerabilities_group x mental_disability)) \<^bold>\<leftrightarrow> exploits_vulnerable_group x\<rfloor>" 

abbreviation "B1 \<equiv> \<lfloor>\<^bold>\<forall>x::aiSys. exploits_vulnerable_group x \<^bold>\<and> has_purpose x distort_behavior \<^bold>\<and> 
has_consequence x harm \<^bold>\<rightarrow> \<^bold>\<circle><prohibited x>\<rfloor>" 

abbreviation "C1 \<equiv> \<lfloor>\<^bold>\<forall>x::aiSys. employed_by_pauthorities x \<^bold>\<and> has_purpose x eval_trustworthiness_over_time \<^bold>\<and> 
(has_consequence x detri_treatment_unrelated_context \<^bold>\<or> has_consequence x detri_treatment_unjustified_disprop)
\<^bold>\<rightarrow> \<^bold>\<circle><prohibited x>\<rfloor>"

abbreviation "D1 \<equiv> \<lfloor>\<^bold>\<forall>x::aiSys. real_time_bioid x \<^bold>\<and> use_public_spaces x \<^bold>\<and> use_law_enforcement x \<^bold>\<and> 
(((has_purpose x targeted_search) \<^bold>\<and> (\<^bold>\<not>(strictly_necessary_for x targeted_search))) \<^bold>\<or>
((has_purpose x detection) \<^bold>\<and> (\<^bold>\<not>(strictly_necessary_for x detection))) \<^bold>\<or> ((has_purpose x prevention) \<^bold>\<and> 
(\<^bold>\<not>(strictly_necessary_for x prevention)))) \<^bold>\<rightarrow> \<^bold>\<circle><prohibited x>\<rfloor>"

abbreviation "A2 \<equiv> \<lfloor>\<^bold>\<forall>x::aiSys. real_time_bioid x \<^bold>\<and> use_public_spaces x \<^bold>\<and> use_law_enforcement x \<^bold>\<and> 
(((has_purpose x targeted_search) \<^bold>\<and> (strictly_necessary_for x targeted_search)) \<^bold>\<or>
((has_purpose x detection) \<^bold>\<and> (strictly_necessary_for x detection)) \<^bold>\<or> ((has_purpose x prevention) \<^bold>\<and> 
(strictly_necessary_for x prevention))) \<^bold>\<rightarrow> \<^bold>\<circle><consider_consequence_no_use x harm_psychological> \<^bold>\<and>
 \<^bold>\<circle><consider_consequence_no_use x harm_physical>\<rfloor>"

(*implicit: not prohibited*)
abbreviation "A2a \<equiv> \<lfloor>\<^bold>\<forall>x::aiSys. real_time_bioid x \<^bold>\<and> use_public_spaces x \<^bold>\<and> use_law_enforcement x \<^bold>\<and> 
(((has_purpose x targeted_search) \<^bold>\<and> (strictly_necessary_for x targeted_search)) \<^bold>\<or>
((has_purpose x detection) \<^bold>\<and> (strictly_necessary_for x detection)) \<^bold>\<or> ((has_purpose x prevention) \<^bold>\<and> 
(strictly_necessary_for x prevention))) \<^bold>\<rightarrow> (\<^bold>\<not>(\<^bold>\<circle><prohibited x>))\<rfloor>"

abbreviation "B2 \<equiv> \<lfloor>\<^bold>\<forall>x::aiSys. real_time_bioid x \<^bold>\<and> use_public_spaces x \<^bold>\<and> use_law_enforcement x \<^bold>\<and>
(((has_purpose x targeted_search) \<^bold>\<and> (strictly_necessary_for x targeted_search)) \<^bold>\<or> (((has_purpose x prevention) \<^bold>\<and> 
(strictly_necessary_for x prevention))) \<^bold>\<or> (((has_purpose x detection) \<^bold>\<and> (strictly_necessary_for x detection))))
\<^bold>\<rightarrow> \<^bold>\<circle><consider_consequence x affect_personal_rights> \<^bold>\<and> \<^bold>\<circle><consider_consequence x affect_personal_freedom>\<rfloor>" 

abbreviation "C2 \<equiv> \<lfloor>\<^bold>\<forall>x::aiSys. real_time_bioid x \<^bold>\<and> use_public_spaces x \<^bold>\<and> use_law_enforcement x \<^bold>\<and>
(((has_purpose x targeted_search) \<^bold>\<and> (strictly_necessary_for x targeted_search)) \<^bold>\<or> (((has_purpose x prevention) \<^bold>\<and> 
(strictly_necessary_for x prevention))) \<^bold>\<or> (((has_purpose x detection) \<^bold>\<and> (strictly_necessary_for x detection))))
\<^bold>\<rightarrow> \<^bold>\<circle><comply_with x bioid_rules>\<rfloor>"

abbreviation "theory_1_2 \<equiv> H1 \<and> H2 \<and> A1 \<and> B1 \<and> C1 \<and> D1 \<and> A2 \<and> A2a \<and> B2 \<and> C2"

(*Facts, Article 5, 1 + 2*)
abbreviation "F1 w \<equiv> (subliminal_technique x) w"
abbreviation "F2 w \<equiv> (has_consequence x harm_physical) w"
abbreviation "F3 w \<equiv> (has_purpose x distort_behavior) w"
abbreviation "F4 w \<equiv> (has_purpose x exploit_groups) w"
abbreviation "F5 w \<equiv> (has_purpose x distort_behavior) w"
abbreviation "F6 w \<equiv> (real_time_bioid z) w"
abbreviation "F7 w \<equiv> (use_public_spaces z) w"
abbreviation "F8 w \<equiv> (use_law_enforcement z) w"
abbreviation "F9 w \<equiv> (has_purpose z targeted_search) w" 
abbreviation "F10 w \<equiv> \<not>(strictly_necessary_for z targeted_search) w"
abbreviation "F11 w \<equiv> (has_purpose z prevention) w" 
abbreviation "F12 w \<equiv> \<not>(strictly_necessary_for z prevention) w"
abbreviation "F13 w \<equiv> (has_purpose z detection) w" 
abbreviation "F14 w \<equiv> (strictly_necessary_for z detection) w"
abbreviation "F15 w \<equiv> (exploits_vulnerabilities_group x age) w"
abbreviation "facts_1_2 \<equiv> F1 \<^bold>\<and> F2 \<^bold>\<and> F3 \<^bold>\<and> F4 \<^bold>\<and> F5 \<^bold>\<and> F6 \<^bold>\<and> F7 \<^bold>\<and> F8 \<^bold>\<and> F9 \<^bold>\<and> F10"

theorem Result1a: "theory_1_2 \<longrightarrow> \<lfloor>(F1 \<^bold>\<and> F2 \<^bold>\<and> F3)  \<^bold>\<rightarrow> (\<^bold>\<circle><prohibited x>)\<rfloor>"  
  by metis

theorem Result1b: "theory_1_2 \<longrightarrow> \<lfloor>F1 \<^bold>\<and> F2  \<^bold>\<rightarrow> (\<^bold>\<circle><prohibited x>)\<rfloor>"  
  nitpick [user_axioms] oops (*counterexample found*)

theorem Result2a: "theory_1_2 \<longrightarrow> \<lfloor>F6 \<^bold>\<and> F7 \<^bold>\<and> F8 \<^bold>\<and> F13 \<^bold>\<and> F14 \<^bold>\<rightarrow> (\<^bold>\<circle><prohibited z>)\<rfloor>"
  nitpick [user_axioms] (*found counterexample*) oops

theorem Result2b: "theory_1_2 \<longrightarrow> \<lfloor>F6 \<^bold>\<and> F7 \<^bold>\<and> F8 \<^bold>\<and> F11 \<^bold>\<and> F12 \<^bold>\<rightarrow> (\<^bold>\<circle><prohibited z>)\<rfloor>"
  by meson

theorem Result2c: "theory_1_2 \<longrightarrow> \<lfloor>F6 \<^bold>\<and> F7 \<^bold>\<and> F8 \<^bold>\<and> F13 \<^bold>\<and> F14 \<^bold>\<rightarrow> (\<^bold>\<not>(\<^bold>\<circle><prohibited z>))\<rfloor>"
  by simp

theorem Result3a: "theory_1_2 \<longrightarrow> \<lfloor>F2 \<^bold>\<and> F3 \<^bold>\<and> F15 \<^bold>\<rightarrow> (\<^bold>\<circle><prohibited x>)\<rfloor>"
  by metis

(*Ai Act Article 5, 3 + 4*)
(*We use a (in Oa, stita) to stand for judicial authority or by an independent administrative authority of Member State,
and Member state b (in Ob, stitb)*)

(*use not urgent \<rightarrow> authority must authorise prior*)
abbreviation "B3 \<equiv> \<lfloor>\<^bold>\<forall>x::aiSys. real_time_bioid x \<^bold>\<and> use_public_spaces x \<^bold>\<and> use_law_enforcement x \<^bold>\<and>
(((has_purpose x targeted_search) \<^bold>\<and> (strictly_necessary_for x targeted_search)) \<^bold>\<or> (((has_purpose x prevention) \<^bold>\<and> 
(strictly_necessary_for x prevention))) \<^bold>\<or> (((has_purpose x detection) \<^bold>\<and> (strictly_necessary_for x detection)))) \<^bold>\<and>
 \<^bold>\<not> use_urgent x \<^bold>\<rightarrow> \<^bold>\<circle>a<stita (authorise_prior x)>\<rfloor>" 

(*use urgent \<rightarrow> authority must not authorise prior, may authorise during or after use*)
abbreviation "C3 \<equiv> \<lfloor>\<^bold>\<forall>x::aiSys. real_time_bioid x \<^bold>\<and> use_public_spaces x \<^bold>\<and> use_law_enforcement x \<^bold>\<and>
(((has_purpose x targeted_search) \<^bold>\<and> (strictly_necessary_for x targeted_search)) \<^bold>\<or> (((has_purpose x prevention) \<^bold>\<and> 
(strictly_necessary_for x prevention))) \<^bold>\<or> (((has_purpose x detection) \<^bold>\<and> (strictly_necessary_for x detection)))) \<^bold>\<and> 
use_urgent x \<^bold>\<rightarrow> (\<^bold>\<not>\<^bold>\<circle>a<stita (authorise_prior x)>) \<^bold>\<and> \<^bold>\<not>(\<^bold>\<circle>a< stita (\<^bold>\<not> (authorise_during_after x))>)\<rfloor>"

(*helpers: authorise x means either prior or during/after authorisation*)
abbreviation "H3 \<equiv> \<lfloor>\<^bold>\<forall>x::aiSys. \<^bold>\<circle>a<(stita (authorise x))> \<^bold>\<leftrightarrow> ((\<^bold>\<circle>a<(stita (authorise_prior x))>) \<^bold>\<or> 
(\<^bold>\<circle>a<(stita (authorise_during_after x))>))\<rfloor>"
abbreviation "H3a \<equiv> \<lfloor>\<^bold>\<forall>x::aiSys. (stita (authorise x)) \<^bold>\<leftrightarrow> ((stita (authorise_prior x)) \<^bold>\<or> 
(stita (authorise_during_after x)))\<rfloor>"

(*Authorise only if evidence and indications show that use of system is necessary and proportionate for achieving
the objective specified*)
abbreviation "D3 \<equiv> \<lfloor>\<^bold>\<forall>x::aiSys. (stita (authorise x)) \<^bold>\<leftrightarrow> evidence_indications_necessary_proportionate x\<rfloor>"

abbreviation "E3 \<equiv> \<lfloor>\<^bold>\<forall>x::aiSys. (stita (authorise x)) \<^bold>\<rightarrow> \<^bold>\<circle>a<stita (consider_consequence_no_use x harm_psychological)> \<^bold>\<and>
 \<^bold>\<circle>a<stita (consider_consequence_no_use x harm_physical)> \<^bold>\<and> \<^bold>\<circle>a<stita (consider_consequence x affect_personal_rights)> \<^bold>\<and>
 \<^bold>\<circle>a<stita (consider_consequence x affect_personal_freedom)>\<rfloor>"

abbreviation "A4 \<equiv> \<lfloor>\<^bold>\<circle><specify_authorised_use national_rules_authorisation>\<rfloor>" 

abbreviation "theory_3_4 \<equiv> B3 \<and> C3 \<and> H3 \<and> H3a \<and> D3 \<and> E3 \<and> A4"

(*Facts, Article 5, 4 + 4*)
abbreviation "F21 w \<equiv> (real_time_bioid x) w"
abbreviation "F22a w \<equiv> \<not> (use_urgent x) w"
abbreviation "F22b w \<equiv> (use_urgent x) w"
abbreviation "F23 w \<equiv> (has_purpose x targeted_search) w"
abbreviation "F24 w \<equiv> (strictly_necessary_for x targeted_search) w"
abbreviation "F25 w \<equiv> (use_public_spaces x) w"
abbreviation "F26 w \<equiv> (use_law_enforcement x) w"
abbreviation "F27a w \<equiv> (stita (authorise_prior x)) w"
abbreviation "F27b w \<equiv> (stita (authorise_during_after x)) w"
abbreviation "facts_3_4 \<equiv> F21 \<^bold>\<and> F23 \<^bold>\<and> F24 \<^bold>\<and> F25 \<^bold>\<and> F26"

theorem Result4a: "theory_3_4 \<longrightarrow> \<lfloor>(facts_3_4 \<^bold>\<and> F22a) \<^bold>\<rightarrow> (\<^bold>\<circle>a<(stita (authorise_prior x))>)\<rfloor>"  
  by auto

theorem Result4b: "theory_3_4 \<longrightarrow> \<lfloor>(facts_3_4 \<^bold>\<and> F22b) \<^bold>\<rightarrow> (\<^bold>\<circle>a<(stita (authorise_prior x))>)\<rfloor>"  
  nitpick (*counterexample found*) oops

theorem Result4c: "theory_3_4 \<longrightarrow> \<lfloor>(facts_3_4 \<^bold>\<and> F22b) \<^bold>\<rightarrow> (\<^bold>\<not>(\<^bold>\<circle>a< stita (\<^bold>\<not> authorise_during_after x)>))\<rfloor>"  
  by simp

theorem Result4d: "theory_3_4 \<longrightarrow> \<lfloor>(facts_3_4 \<^bold>\<and> F22a \<^bold>\<and> F27a) \<^bold>\<rightarrow> (evidence_indications_necessary_proportionate x)\<rfloor>"  
  by metis

theorem Result4e: "theory_3_4 \<longrightarrow> \<lfloor>(facts_3_4 \<^bold>\<and> F22b \<^bold>\<and> F27b) \<^bold>\<rightarrow> ((evidence_indications_necessary_proportionate x) \<^bold>\<and> 
  \<^bold>\<circle>a<stita (consider_consequence_no_use x harm_psychological)>)\<rfloor>"  
  by metis

(* This tile can be expressed in SDL, with some drawbacks: There is no perfect way to express exceptions from general rules.
We would need this when defining the exception from the prohibition of real-time-bioid-systems (D1, A2, A2a), and the exception 
from needing prior authorisation (B3 and C3). I solved this here defining two obligations, one for everything but the exception
and one for the exception.
One further difficulty is expressing the obligation: ‘In deciding the request, xy shall\<dots>’ (Article 5, 3), because the phrase 'in
deciding...' implies some temporal aspect which can not be expressed in SDL. I represented this obligation in E3 by 
simply saying that if a is authorising ai-system x, then a is obligated to consider the context of x and the consequences of x.
Parts of Article 5,  point 3 + 4 need agency to be expressed correctly. I did not use my STIT embedding here due to the infinite 
models but simple placeholder operators. *)

end

