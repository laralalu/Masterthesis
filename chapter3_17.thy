theory chapter3_17
  imports Main Dstit_Deontic types
begin

(*Example: DDL in combination with dstit*)
(*assume providers are of a1*)

consts  
  is_credit_inst::"ag\<Rightarrow>\<sigma>"
  quality_man_in_place::"aiSys\<Rightarrow>\<sigma>" 
  document_quality_man::"qualManSys\<Rightarrow>\<sigma>" 
  qual_man_includes_a_to_m::"qualManSys\<Rightarrow>\<sigma>"
  implementation_proportionate::"aiSys\<Rightarrow>size\<Rightarrow>\<sigma>"
  obl_deemed_fulfilled_by_art_74_40::"aiSys\<Rightarrow>\<sigma>"
  take_into_account::"standard\<Rightarrow>aiSys\<Rightarrow>\<sigma>" 

axiomatization where
  A1: "\<lfloor>\<^bold>\<forall>x::aiSys. (\<^bold>\<otimes> a1 (quality_man_in_place x))\<rfloor>" and
  B1: "\<lfloor>\<^bold>\<forall>y::qualManSys. (\<^bold>\<otimes> a1 (document_quality_man y))\<rfloor>" and
  C1: "\<lfloor>\<^bold>\<forall>y::qualManSys. (\<^bold>\<otimes> a1(qual_man_includes_a_to_m y))\<rfloor>" and
  2: "\<lfloor>\<^bold>\<forall>x::aiSys. \<^bold>\<forall>z::size. (\<^bold>\<otimes> a1 (implementation_proportionate x z))\<rfloor>" and
  (*A3: "\<lfloor>\<^bold>\<forall>x::aiSys. ((is_credit_inst a1) \<^bold>\<rightarrow> \<^bold>\<circle><(obl_deemed_fulfilled_by_art_74_40 x)>)\<rfloor>" and*)
  B3: "\<lfloor>\<^bold>\<forall>x::aiSys. ((is_credit_inst a1) \<^bold>\<rightarrow> (\<^bold>\<otimes> a1 (take_into_account harm_stand_art_40 x)))\<rfloor>" 

lemma True nitpick [satisfy, user_axioms, show_all] oops (*time-out, infinite models with dstit*)

  
  
  