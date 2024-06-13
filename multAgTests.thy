
(*Article 32 (?) \<rightarrow> pick example and formalize, once in ExtDDL and once in ModExtDDL (agents_2)*)
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