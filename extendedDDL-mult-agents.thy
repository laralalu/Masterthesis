theory "extendedDDL-mult-agents"
  imports 
    types
    DDL_agents_2
begin

consts 
  e::ag 
  notif_auth_of::"ag\<Rightarrow>ag" (*gives back notifying authority of a member state*)
  established_in::"ag\<Rightarrow>ag" (*member state in which conf ass body is established*)
  submit_appl_for_notific::"ag\<Rightarrow>ag\<Rightarrow>\<sigma>" (*conf ass body submits application to a
  notifying authority*)

axiomatization where
  F1: "\<lfloor>conf_ass_body e\<rfloor>\<^sub>l" and
  R1: "\<lfloor>\<^bold>\<forall>a.(conf_ass_body a) \<^bold>\<rightarrow> \<^bold>\<circle>a<stit a (submit_appl_for_notific a (notif_auth_of (established_in a)))>\<rfloor>" 

lemma test1: "\<lfloor>\<^bold>\<circle>e<stit e (submit_appl_for_notific e (notif_auth_of (established_in e)))>\<rfloor>\<^sub>l" using F1 R1 by auto

lemma True nitpick [satisfy, user_axioms, show_all] (*Consistency-check: Nitpick finds a model.*) oops


consts
  c::ag
  f::ag
  h::ag
  notification_changes::"ag\<Rightarrow>\<sigma>"
  inform::"ag\<Rightarrow>ag\<Rightarrow>\<sigma>"

axiomatization where
  A2: "\<lfloor>eu_comm c\<rfloor>" and
  A3: "\<lfloor>notif_authority f\<rfloor>" and
  A4: "\<lfloor>member_state h\<rfloor>" and
  A6: "\<lfloor>(notification_changes f) \<^bold>\<rightarrow> \<^bold>\<circle>f<stit f (inform f c)> \<^bold>\<and> \<^bold>\<circle>f<stit f (inform f h)>\<rfloor>"

lemma True nitpick [satisfy, user_axioms, show_all] oops (*Consistency-check: Nitpick finds a model.*)


consts
  have_qual_man_art17::"aiSys\<Rightarrow>\<sigma>"
  conf_ass_done::"aiSys\<Rightarrow>\<sigma>"
  has_conformity_marking::"aiSys\<Rightarrow>\<sigma>"
  safeguard_info::\<sigma>
  verify_conformity_Art43::"aiSys\<Rightarrow>\<sigma>"

(*abbreviation "sixteenB \<equiv> \<lfloor>\<^bold>\<forall>x. (high_risk x) \<^bold>\<rightarrow> \<^bold>\<circle>d<stit d (have_qual_man_art17 x)>\<rfloor>" (*d = provider*)
abbreviation "twentysix1a \<equiv> \<lfloor>\<^bold>\<forall>x. (high_risk x) \<^bold>\<rightarrow> \<^bold>\<circle>b<stit b (stit d (conf_ass_done x))>\<rfloor>" (*b = importer*)
abbreviation "thirty6 \<equiv> \<lfloor>\<^bold>\<circle>f<stit f (safeguard_info)>\<rfloor>" (*f = notifying authority*)*)