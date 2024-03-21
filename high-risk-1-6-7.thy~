theory "high-risk-1-6-7"
  imports 
  types
  SDL_agents
begin

consts (*Predicates/relations*)
   covered_by_Union_harmonisation_legislation_Annex_2 :: "aiSys \<Rightarrow> \<sigma>"
   is_required_to_undergo_thirdparty_conformity_assessment ::  "aiSys \<Rightarrow> \<sigma>"
   is_listed_Annex_3 :: "aiSys \<Rightarrow> \<sigma>"
   is_used_areas_1to8_Annex_3 :: "aiSys \<Rightarrow> \<sigma>"
   poses_risk_equivalent_greater_systems_Annex_3 :: "aiSys \<Rightarrow> \<sigma>"

   purpose_sys :: "aiSys \<Rightarrow> purpose" 
   extent :: "(aiSys \<Rightarrow> degree) list"
   extent_use :: "aiSys \<Rightarrow> degree"
   extent_harm_caused :: "aiSys \<Rightarrow> degree"
   potential_extent_harm :: "aiSys \<Rightarrow> degree"
   extent_harmed_people_dependent :: "aiSys \<Rightarrow> degree"
   extent_harmed_people_vulnerable :: "aiSys \<Rightarrow> degree"
   extent_union_legislation_redress_prevention :: "aiSys \<Rightarrow> degree"
   extent_produced_outcome_reversible :: "aiSys \<Rightarrow> degree"

   adapt_delegated_acts :: "agent \<Rightarrow> \<sigma>" 
   risk_assessed :: "aiSys \<Rightarrow> \<sigma>" (*risk of a system is being assessed*)

   take_into_account :: "(aiSys \<Rightarrow> degree) \<Rightarrow> aiSys \<Rightarrow> \<sigma>"
   take_into_account' :: " (aiSys \<Rightarrow> purpose) \<Rightarrow> aiSys \<Rightarrow> \<sigma>"

   prohibited :: "aiSys \<Rightarrow> \<sigma>"
   high_risk :: "aiSys \<Rightarrow> \<sigma>" 

consts x::"aiSys" (*aiSystem*) 

(*Ai Act article 6 + 7*)
(*We use a (in Oc, stitc) to stand for the eu_commission*)
abbreviation "A1 \<equiv> \<lfloor>\<^bold>\<forall>x::aiSys. (((covered_by_Union_harmonisation_legislation_Annex_2 x) \<^bold>\<and> 
                   (is_required_to_undergo_thirdparty_conformity_assessment x)) \<^bold>\<rightarrow> (\<^bold>\<circle><high_risk x>))\<rfloor>"

abbreviation "A2 \<equiv> \<lfloor>\<^bold>\<forall>x::aiSys. ((is_listed_Annex_3 x) \<^bold>\<rightarrow> (\<^bold>\<circle><high_risk x>))\<rfloor>"

(*...the eu commission may see to it that the eu commission adapts delegated acts*)
abbreviation "A3 \<equiv> \<lfloor>\<^bold>\<forall>x::aiSys. (((is_used_areas_1to8_Annex_3 x) \<^bold>\<and> (poses_risk_equivalent_greater_systems_Annex_3 x)) 
                   \<^bold>\<rightarrow> (\<^bold>\<not>(\<^bold>\<circle><\<^bold>\<not> stitc (adapt_delegated_acts eu_comm)>)))\<rfloor>"

abbreviation "A4 \<equiv> \<lfloor>\<^bold>\<forall>x::aiSys. ((stitc (risk_assessed x)) \<^bold>\<rightarrow>
                    (\<^bold>\<circle>c<stitc (take_into_account' purpose_sys x)>) \<^bold>\<and>
                    (\<^bold>\<circle>c<stitc (take_into_account extent_use x)>)) \<^bold>\<and> 
                    (\<^bold>\<circle>c<stitc (take_into_account extent_harm_caused x)>) \<^bold>\<and> 
                    (\<^bold>\<circle>c<stitc (take_into_account extent_harmed_people_vulnerable x)>) \<^bold>\<and> 
                    (\<^bold>\<circle>c<stitc (take_into_account extent_harmed_people_dependent x)>) \<^bold>\<and> 
                    (\<^bold>\<circle>c<stitc (take_into_account extent_union_legislation_redress_prevention x)>) \<^bold>\<and>
                    (\<^bold>\<circle>c<stitc (take_into_account potential_extent_harm x)>) \<^bold>\<and>
                    (\<^bold>\<circle>c<stitc (take_into_account extent_produced_outcome_reversible x)>)\<rfloor>"  

abbreviation "a_theory \<equiv> A1 \<and> A2 \<and> A3 \<and> A4"

(*Facts*)
abbreviation "F1 w \<equiv> (covered_by_Union_harmonisation_legislation_Annex_2 x)  w"
abbreviation "F2 w \<equiv> (is_required_to_undergo_thirdparty_conformity_assessment x) w"
abbreviation "F3 w \<equiv> (stitc (risk_assessed x)) w"
abbreviation "a_facts \<equiv> F1 \<^bold>\<and> F2 \<^bold>\<and> F3"

theorem Result1a: "a_theory \<longrightarrow> \<lfloor>F1 \<^bold>\<and> F2 \<^bold>\<rightarrow> (\<^bold>\<circle><high_risk x>)\<rfloor>"  
  by auto

theorem Result1b: "a_theory \<longrightarrow> \<lfloor>F1 \<^bold>\<and> F3 \<^bold>\<rightarrow> (\<^bold>\<circle><high_risk x>)\<rfloor>" 
  nitpick oops (*counterexample found*)

theorem Result2a: "a_theory \<longrightarrow> \<lfloor>F3 \<^bold>\<rightarrow> (\<^bold>\<circle>c<stitc (take_into_account' purpose_sys x)> \<^bold>\<and>
                    (\<^bold>\<circle>c<stitc (take_into_account' purpose_sys x)>) \<^bold>\<and>
                    (\<^bold>\<circle>c<stitc (take_into_account extent_use x)>) \<^bold>\<and> 
                    (\<^bold>\<circle>c<stitc (take_into_account extent_harm_caused x)>) \<^bold>\<and> 
                    (\<^bold>\<circle>c<stitc (take_into_account extent_harmed_people_vulnerable x)>) \<^bold>\<and> 
                    (\<^bold>\<circle>c<stitc (take_into_account extent_harmed_people_dependent x)>) \<^bold>\<and> 
                    (\<^bold>\<circle>c<stitc (take_into_account extent_union_legislation_redress_prevention x)>) \<^bold>\<and>
                    (\<^bold>\<circle>c<stitc (take_into_account potential_extent_harm x)>) \<^bold>\<and>
                    (\<^bold>\<circle>c<stitc (take_into_account extent_produced_outcome_reversible x)>))\<rfloor>"
  by simp
 
(*This chapter can be expressed in SDL, with one drawback, similar to the one we encountered in the prohibited tile: 
The phrase 'When assessing..., x shall' implies a temporal dimension which can not be expressed in SDL. I represented this obligation in A4
by simply saying that : "If the EU commission is assessing the risk of AI System x, then the EU commission shall see to it that (...) is taken 
into account."*)

end