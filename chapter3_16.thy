theory chapter3_16
  imports Main Dstit_Deontic types
begin

consts
  ensure_compliance_chap_2::"aiSys\<Rightarrow>\<sigma>"
  quality_management_art_17::"aiSys\<Rightarrow>\<sigma>"
  tech_doc::"aiSys\<Rightarrow>\<sigma>"
  keep_logs::"aiSys\<Rightarrow>\<sigma>"
  conformity_assessment_prior::"aiSys\<Rightarrow>\<sigma>"
  comply_registration_obl_art_51::"aiSys\<Rightarrow>\<sigma>"
  take_corr_action::"aiSys\<Rightarrow>\<sigma>"
  not_in_conformity_chap_2::"aiSys\<Rightarrow>\<sigma>"
  inform_authorities::"aiSys\<Rightarrow>\<sigma>"
  CE_marking_art_49::"aiSys\<Rightarrow>\<sigma>"
  demonstrate_conformity_art_2::"ag\<Rightarrow>aiSys\<Rightarrow>\<sigma>"
  request::"ag\<Rightarrow>aiSys\<Rightarrow>\<sigma>" 
  nch::ag

(*g and h are missing here due to the CTD part*)
axiomatization where
  a: "\<lfloor>\<^bold>\<forall>x::aiSys. (\<^bold>\<otimes>d a1 (ensure_compliance_chap_2 x))\<rfloor>" and
  b: "\<lfloor>\<^bold>\<forall>x::aiSys. (\<^bold>\<otimes>d a1 (quality_management_art_17 x))\<rfloor>" and
  c: "\<lfloor>\<^bold>\<forall>x::aiSys. (\<^bold>\<otimes>d a1 (tech_doc x))\<rfloor>" and
  d: "\<lfloor>\<^bold>\<forall>x::aiSys. (\<^bold>\<otimes>d a1 (keep_logs x))\<rfloor>" and
  e: "\<lfloor>\<^bold>\<forall>x::aiSys. (\<^bold>\<otimes>d a1 (conformity_assessment_prior x))\<rfloor>" and
  f: "\<lfloor>\<^bold>\<forall>x::aiSys. (\<^bold>\<otimes>d a1 (comply_registration_obl_art_51 x))\<rfloor>" and
  i: "\<lfloor>\<^bold>\<forall>x::aiSys. (\<^bold>\<otimes>d a1 (CE_marking_art_49 x))\<rfloor>" and
  j: "\<lfloor>\<^bold>\<forall>x::aiSys. ((request nch x) \<^bold>\<rightarrow> (\<^bold>\<otimes>d a1 (demonstrate_conformity_art_2 nch x)))\<rfloor>"

lemma True nitpick [satisfy, user_axioms, show_all] oops (*time-out, infinite models with dstit*)

end

   