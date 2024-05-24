theory DDL_agents  (*DDL including STIT operator and agentive obligations*)
  imports 
    Main
    types
begin 

consts 
cw::i (*current world*)
av::"i\<Rightarrow>\<sigma>" pv::"i\<Rightarrow>\<sigma>" ob::"\<sigma>\<Rightarrow>(\<sigma>\<Rightarrow>bool)" (*general accessibility relations*)
                 
(*avb::"i\<Rightarrow>\<sigma>" pvb::"i\<Rightarrow>\<sigma>" obb::"\<sigma>\<Rightarrow>(\<sigma>\<Rightarrow>bool)" (*accessibility relations for agent b*) 
avc::"i\<Rightarrow>\<sigma>" pvc::"i\<Rightarrow>\<sigma>" obc::"\<sigma>\<Rightarrow>(\<sigma>\<Rightarrow>bool)" (*accessibility relations for agent c*)*)
avd::"i\<Rightarrow>\<sigma>" pvd::"i\<Rightarrow>\<sigma>" obd::"\<sigma>\<Rightarrow>(\<sigma>\<Rightarrow>bool)" (*accessibility relations for agent d*)
(*ave::"i\<Rightarrow>\<sigma>" pve::"i\<Rightarrow>\<sigma>" obe::"\<sigma>\<Rightarrow>(\<sigma>\<Rightarrow>bool)" (*accessibility relations for agent e*)
avf::"i\<Rightarrow>\<sigma>" pvf::"i\<Rightarrow>\<sigma>" obf::"\<sigma>\<Rightarrow>(\<sigma>\<Rightarrow>bool)" (*accessibility relations for agent f*)
avg::"i\<Rightarrow>\<sigma>" pvg::"i\<Rightarrow>\<sigma>" obg::"\<sigma>\<Rightarrow>(\<sigma>\<Rightarrow>bool)" (*accessibility relations for agent g*)
avh::"i\<Rightarrow>\<sigma>" pvh::"i\<Rightarrow>\<sigma>" obh::"\<sigma>\<Rightarrow>(\<sigma>\<Rightarrow>bool)" (*accessibility relations for agent h*)*)

(*simplifier? etc., pragmatisch vorgehen, erklären warum nicht, etc.
agents die mehrere Typen sind, geht auch nicht*)

(*stit operator*) 
stit::"ag\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (*ag sees to it that*)

 axiomatization where
  ax_3a: "\<forall>w.\<exists>x. av(w)(x)" and ax_4a: "\<forall>w x. av(w)(x) \<longrightarrow> pv(w)(x)" and ax_4b: "\<forall>w. pv(w)(w)" and
  ax_5a: "\<forall>X.\<not>ob(X)(\<lambda>x. False)" and
  ax_5b: "\<forall>X Y Z. (\<forall>w. ((Y(w) \<and> X(w)) \<longleftrightarrow> (Z(w) \<and> X(w)))) \<longrightarrow> (ob(X)(Y) \<longleftrightarrow> ob(X)(Z))" and
  ax_5ca: "\<forall>X \<beta>. ((\<forall>Z. \<beta>(Z) \<longrightarrow> ob(X)(Z)) \<and> (\<exists>Z. \<beta>(Z))) \<longrightarrow> 
      (((\<exists>y. ((\<lambda>w. \<forall>Z. (\<beta> Z) \<longrightarrow> (Z w))(y) \<and> X(y))) \<longrightarrow> ob(X)(\<lambda>w. \<forall>Z. (\<beta> Z) \<longrightarrow> (Z w))))" and
  ax_5c: "\<forall>X Y Z. (((\<exists>w. (X(w) \<and> Y(w) \<and> Z(w))) \<and>  ob(X)(Y)  \<and>  ob(X)(Z))  \<longrightarrow>  ob(X)(\<lambda>w. Y(w) \<and> Z(w)))" and
  ax_5d: "\<forall>X Y Z. ((\<forall>w. Y(w) \<longrightarrow> X(w)) \<and> ob(X)(Y) \<and> (\<forall>w. X(w) \<longrightarrow> Z(w)))
                   \<longrightarrow> ob(Z)(\<lambda>w. (Z(w) \<and> \<not>X(w)) \<or> Y(w))" and
  ax_5e: "\<forall>X Y Z. ((\<forall>w. Y(w) \<longrightarrow> X(w)) \<and> ob(X)(Z) \<and> (\<exists>w. Y(w) \<and> Z(w))) \<longrightarrow> ob(Y)(Z)" and

  (*(*for agent b: importers*)
  axb_3a: "\<forall>w.\<exists>x. avb(w)(x)" and axb_4a: "\<forall>w x. avb(w)(x) \<longrightarrow> pvb(w)(x)" and axb_4ba: "\<forall>w. pvb(w)(w)" and
  axb_5a: "\<forall>X.\<not>obb(X)(\<lambda>x. False)" and
  axb_5b: "\<forall>X Y Z. (\<forall>w. ((Y(w) \<and> X(w)) \<longleftrightarrow> (Z(w) \<and> X(w)))) \<longrightarrow> (obb(X)(Y) \<longleftrightarrow> obb(X)(Z))" and
  axb_5ca: "\<forall>X \<beta>. ((\<forall>Z. \<beta>(Z) \<longrightarrow> obb(X)(Z)) \<and> (\<exists>Z. \<beta>(Z))) \<longrightarrow> 
      (((\<exists>y. ((\<lambda>w. \<forall>Z. (\<beta> Z) \<longrightarrow> (Z w))(y) \<and> X(y))) \<longrightarrow> obb(X)(\<lambda>w. \<forall>Z. (\<beta> Z) \<longrightarrow> (Z w))))" and
  axb_5c: "\<forall>X Y Z. (((\<exists>w. (X(w) \<and> Y(w) \<and> Z(w))) \<and>  obb(X)(Y)  \<and>  obb(X)(Z))  \<longrightarrow>  obb(X)(\<lambda>w. Y(w) \<and> Z(w)))" and
  axb_5d: "\<forall>X Y Z. ((\<forall>w. Y(w) \<longrightarrow> X(w)) \<and> obb(X)(Y) \<and> (\<forall>w. X(w) \<longrightarrow> Z(w)))
                   \<longrightarrow> obb(Z)(\<lambda>w. (Z(w) \<and> \<not>X(w)) \<or> Y(w))" and
  axb_5e: "\<forall>X Y Z. ((\<forall>w. Y(w) \<longrightarrow> X(w)) \<and> obb(X)(Z) \<and> (\<exists>w. Y(w) \<and> Z(w))) \<longrightarrow> obb(Y)(Z)" and

  (*for agent c: distributors*)
  axc_3: "\<forall>w.\<exists>x. avc(w)(x)" and axl_4a: "\<forall>w x. avc(w)(x) \<longrightarrow> pvc(w)(x)" and axm_4ba: "\<forall>w. pvc(w)(w)" and
  axc_5a: "\<forall>X.\<not>obc(X)(\<lambda>x. False)" and
  axc_5b: "\<forall>X Y Z. (\<forall>w. ((Y(w) \<and> X(w)) \<longleftrightarrow> (Z(w) \<and> X(w)))) \<longrightarrow> (obc(X)(Y) \<longleftrightarrow> obc(X)(Z))" and
  axc_5ca: "\<forall>X \<beta>. ((\<forall>Z. \<beta>(Z) \<longrightarrow> obc(X)(Z)) \<and> (\<exists>Z. \<beta>(Z))) \<longrightarrow> 
      (((\<exists>y. ((\<lambda>w. \<forall>Z. (\<beta> Z) \<longrightarrow> (Z w))(y) \<and> X(y))) \<longrightarrow> obc(X)(\<lambda>w. \<forall>Z. (\<beta> Z) \<longrightarrow> (Z w))))" and
  axc_5c: "\<forall>X Y Z. (((\<exists>w. (X(w) \<and> Y(w) \<and> Z(w))) \<and>  obc(X)(Y)  \<and>  obc(X)(Z))  \<longrightarrow>  obc(X)(\<lambda>w. Y(w) \<and> Z(w)))" and
  axc_5d: "\<forall>X Y Z. ((\<forall>w. Y(w) \<longrightarrow> X(w)) \<and> obc(X)(Y) \<and> (\<forall>w. X(w) \<longrightarrow> Z(w)))
                   \<longrightarrow> obc(Z)(\<lambda>w. (Z(w) \<and> \<not>X(w)) \<or> Y(w))" and
  axc_5e: "\<forall>X Y Z. ((\<forall>w. Y(w) \<longrightarrow> X(w)) \<and> obc(X)(Z) \<and> (\<exists>w. Y(w) \<and> Z(w))) \<longrightarrow> obc(Y)(Z)" and*)

   (*for agent d: providers*)
  axd_3a: "\<forall>w.\<exists>x. avd(w)(x)" and axd_4a: "\<forall>w x. avd(w)(x) \<longrightarrow> pvd(w)(x)" and axa_4ba: "\<forall>w. pvd(w)(w)" and
  axd_5a: "\<forall>X.\<not>obd(X)(\<lambda>x. False)" and
  axd_5b: "\<forall>X Y Z. (\<forall>w. ((Y(w) \<and> X(w)) \<longleftrightarrow> (Z(w) \<and> X(w)))) \<longrightarrow> (obd(X)(Y) \<longleftrightarrow> obd(X)(Z))" and
  axd_5ca: "\<forall>X \<beta>. ((\<forall>Z. \<beta>(Z) \<longrightarrow> obd(X)(Z)) \<and> (\<exists>Z. \<beta>(Z))) \<longrightarrow> 
      (((\<exists>y. ((\<lambda>w. \<forall>Z. (\<beta> Z) \<longrightarrow> (Z w))(y) \<and> X(y))) \<longrightarrow> obd(X)(\<lambda>w. \<forall>Z. (\<beta> Z) \<longrightarrow> (Z w))))" and
  axd_5c: "\<forall>X Y Z. (((\<exists>w. (X(w) \<and> Y(w) \<and> Z(w))) \<and>  obd(X)(Y)  \<and>  obd(X)(Z))  \<longrightarrow>  obd(X)(\<lambda>w. Y(w) \<and> Z(w)))" and
  axd_5d: "\<forall>X Y Z. ((\<forall>w. Y(w) \<longrightarrow> X(w)) \<and> obd(X)(Y) \<and> (\<forall>w. X(w) \<longrightarrow> Z(w)))
                   \<longrightarrow> obd(Z)(\<lambda>w. (Z(w) \<and> \<not>X(w)) \<or> Y(w))" and
  axd_5e: "\<forall>X Y Z. ((\<forall>w. Y(w) \<longrightarrow> X(w)) \<and> obd(X)(Z) \<and> (\<exists>w. Y(w) \<and> Z(w))) \<longrightarrow> obd(Y)(Z)" and

  (*(*for agent e: conformity assessment bodies*)
  axe_3a: "\<forall>w.\<exists>x. ave(w)(x)" and axe_4a: "\<forall>w x. ave(w)(x) \<longrightarrow> pve(w)(x)" and axe_4ba: "\<forall>w. pve(w)(w)" and
  axe_5a: "\<forall>X.\<not>obe(X)(\<lambda>x. False)" and
  axe_5b: "\<forall>X Y Z. (\<forall>w. ((Y(w) \<and> X(w)) \<longleftrightarrow> (Z(w) \<and> X(w)))) \<longrightarrow> (obe(X)(Y) \<longleftrightarrow> obe(X)(Z))" and
  axe_5ca: "\<forall>X \<beta>. ((\<forall>Z. \<beta>(Z) \<longrightarrow> obe(X)(Z)) \<and> (\<exists>Z. \<beta>(Z))) \<longrightarrow> 
      (((\<exists>y. ((\<lambda>w. \<forall>Z. (\<beta> Z) \<longrightarrow> (Z w))(y) \<and> X(y))) \<longrightarrow> obe(X)(\<lambda>w. \<forall>Z. (\<beta> Z) \<longrightarrow> (Z w))))" and
  axe_5c: "\<forall>X Y Z. (((\<exists>w. (X(w) \<and> Y(w) \<and> Z(w))) \<and>  obe(X)(Y)  \<and>  obe(X)(Z))  \<longrightarrow>  obe(X)(\<lambda>w. Y(w) \<and> Z(w)))" and
  axe_5d: "\<forall>X Y Z. ((\<forall>w. Y(w) \<longrightarrow> X(w)) \<and> obe(X)(Y) \<and> (\<forall>w. X(w) \<longrightarrow> Z(w)))
                   \<longrightarrow> obe(Z)(\<lambda>w. (Z(w) \<and> \<not>X(w)) \<or> Y(w))" and
  axe_5e: "\<forall>X Y Z. ((\<forall>w. Y(w) \<longrightarrow> X(w)) \<and> obe(X)(Z) \<and> (\<exists>w. Y(w) \<and> Z(w))) \<longrightarrow> obe(Y)(Z)" and

  (*for agent f: notifying authority*)
  axf_3a: "\<forall>w.\<exists>x. avf(w)(x)" and axf_4a: "\<forall>w x. avf(w)(x) \<longrightarrow> pvf(w)(x)" and axf_4ba: "\<forall>w. pvf(w)(w)" and
  axf_5a: "\<forall>X.\<not>obf(X)(\<lambda>x. False)" and
  axf_5b: "\<forall>X Y Z. (\<forall>w. ((Y(w) \<and> X(w)) \<longleftrightarrow> (Z(w) \<and> X(w)))) \<longrightarrow> (obf(X)(Y) \<longleftrightarrow> obf(X)(Z))" and
  axf_5ca: "\<forall>X \<beta>. ((\<forall>Z. \<beta>(Z) \<longrightarrow> obf(X)(Z)) \<and> (\<exists>Z. \<beta>(Z))) \<longrightarrow> 
      (((\<exists>y. ((\<lambda>w. \<forall>Z. (\<beta> Z) \<longrightarrow> (Z w))(y) \<and> X(y))) \<longrightarrow> obf(X)(\<lambda>w. \<forall>Z. (\<beta> Z) \<longrightarrow> (Z w))))" and
  axf_5c: "\<forall>X Y Z. (((\<exists>w. (X(w) \<and> Y(w) \<and> Z(w))) \<and>  obf(X)(Y)  \<and>  obf(X)(Z))  \<longrightarrow>  obf(X)(\<lambda>w. Y(w) \<and> Z(w)))" and
  axf_5d: "\<forall>X Y Z. ((\<forall>w. Y(w) \<longrightarrow> X(w)) \<and> obf(X)(Y) \<and> (\<forall>w. X(w) \<longrightarrow> Z(w)))
                   \<longrightarrow> obf(Z)(\<lambda>w. (Z(w) \<and> \<not>X(w)) \<or> Y(w))" and
  axf_5e: "\<forall>X Y Z. ((\<forall>w. Y(w) \<longrightarrow> X(w)) \<and> obf(X)(Z) \<and> (\<exists>w. Y(w) \<and> Z(w))) \<longrightarrow> obf(Y)(Z)" and

  (*for agent g: notified bodies*)
  axg_3a: "\<forall>w.\<exists>x. avg(w)(x)" and axg_4a: "\<forall>w x. avg(w)(x) \<longrightarrow> pvg(w)(x)" and axg_4ba: "\<forall>w. pvg(w)(w)" and
  axg_5a: "\<forall>X.\<not>obg(X)(\<lambda>x. False)" and
  axg_5b: "\<forall>X Y Z. (\<forall>w. ((Y(w) \<and> X(w)) \<longleftrightarrow> (Z(w) \<and> X(w)))) \<longrightarrow> (obg(X)(Y) \<longleftrightarrow> obg(X)(Z))" and
  axg_5ca: "\<forall>X \<beta>. ((\<forall>Z. \<beta>(Z) \<longrightarrow> obg(X)(Z)) \<and> (\<exists>Z. \<beta>(Z))) \<longrightarrow> 
      (((\<exists>y. ((\<lambda>w. \<forall>Z. (\<beta> Z) \<longrightarrow> (Z w))(y) \<and> X(y))) \<longrightarrow> obg(X)(\<lambda>w. \<forall>Z. (\<beta> Z) \<longrightarrow> (Z w))))" and
  axg_5c: "\<forall>X Y Z. (((\<exists>w. (X(w) \<and> Y(w) \<and> Z(w))) \<and>  obg(X)(Y)  \<and>  obg(X)(Z))  \<longrightarrow>  obg(X)(\<lambda>w. Y(w) \<and> Z(w)))" and
  axg_5d: "\<forall>X Y Z. ((\<forall>w. Y(w) \<longrightarrow> X(w)) \<and> obg(X)(Y) \<and> (\<forall>w. X(w) \<longrightarrow> Z(w)))
                   \<longrightarrow> obg(Z)(\<lambda>w. (Z(w) \<and> \<not>X(w)) \<or> Y(w))" and
  axg_5e: "\<forall>X Y Z. ((\<forall>w. Y(w) \<longrightarrow> X(w)) \<and> obg(X)(Z) \<and> (\<exists>w. Y(w) \<and> Z(w))) \<longrightarrow> obg(Y)(Z)" and

  (*for agent h: member state*)
  axh_3a: "\<forall>w.\<exists>x. avh(w)(x)" and axh_4a: "\<forall>w x. avh(w)(x) \<longrightarrow> pvh(w)(x)" and axh_4ba: "\<forall>w. pvh(w)(w)" and
  axh_5a: "\<forall>X.\<not>obh(X)(\<lambda>x. False)" and
  axh_5b: "\<forall>X Y Z. (\<forall>w. ((Y(w) \<and> X(w)) \<longleftrightarrow> (Z(w) \<and> X(w)))) \<longrightarrow> (obh(X)(Y) \<longleftrightarrow> obh(X)(Z))" and
  axh_5ca: "\<forall>X \<beta>. ((\<forall>Z. \<beta>(Z) \<longrightarrow> obh(X)(Z)) \<and> (\<exists>Z. \<beta>(Z))) \<longrightarrow> 
      (((\<exists>y. ((\<lambda>w. \<forall>Z. (\<beta> Z) \<longrightarrow> (Z w))(y) \<and> X(y))) \<longrightarrow> obh(X)(\<lambda>w. \<forall>Z. (\<beta> Z) \<longrightarrow> (Z w))))" and
  axh_5c: "\<forall>X Y Z. (((\<exists>w. (X(w) \<and> Y(w) \<and> Z(w))) \<and>  obh(X)(Y)  \<and>  obh(X)(Z))  \<longrightarrow>  obh(X)(\<lambda>w. Y(w) \<and> Z(w)))" and
  axh_5d: "\<forall>X Y Z. ((\<forall>w. Y(w) \<longrightarrow> X(w)) \<and> obh(X)(Y) \<and> (\<forall>w. X(w) \<longrightarrow> Z(w)))
                   \<longrightarrow> obh(Z)(\<lambda>w. (Z(w) \<and> \<not>X(w)) \<or> Y(w))" and
  axh_5e: "\<forall>X Y Z. ((\<forall>w. Y(w) \<longrightarrow> X(w)) \<and> obh(X)(Z) \<and> (\<exists>w. Y(w) \<and> Z(w))) \<longrightarrow> obh(Y)(Z)" and*)

  stit1: "\<forall>a F w. ((stit a F) w) \<longrightarrow> F w"

 abbreviation ddlneg::\<gamma> ("\<^bold>\<not>_"[52]53) where "\<^bold>\<not>A \<equiv> \<lambda>w. \<not>A(w)" 
 abbreviation ddland::\<rho> (infixr"\<^bold>\<and>"51) where "A\<^bold>\<and>B \<equiv> \<lambda>w. A(w)\<and>B(w)"   
 abbreviation ddlor::\<rho> (infixr"\<^bold>\<or>"50) where "A\<^bold>\<or>B \<equiv> \<lambda>w. A(w)\<or>B(w)"   
 abbreviation ddlimp::\<rho> (infixr"\<^bold>\<rightarrow>"49) where "A\<^bold>\<rightarrow>B \<equiv> \<lambda>w. A(w)\<longrightarrow>B(w)"  
 abbreviation ddlequiv::\<rho> (infixr"\<^bold>\<leftrightarrow>"48) where "A\<^bold>\<leftrightarrow>B \<equiv> \<lambda>w. A(w)\<longleftrightarrow>B(w)"  

 abbreviation ddlbox::\<gamma> ("\<^bold>\<box>") where "\<^bold>\<box>A \<equiv> \<lambda>w.\<forall>v. A(v)"  (*A = (\<lambda>w. True)*) 
 abbreviation ddldia_g::\<gamma>  ("\<^bold>\<diamond>") where "\<^bold>\<diamond> A \<equiv> \<^bold>\<not>\<^bold>\<box>(\<^bold>\<not>A)"
 abbreviation ddlboxa::\<gamma> ("\<^bold>\<box>\<^sub>a") where "\<^bold>\<box>\<^sub>a A \<equiv> \<lambda>w. (\<forall>x. av (w)(x) \<longrightarrow> A(x))"  (*in all actual worlds*)
 abbreviation ddlboxp::\<gamma> ("\<^bold>\<box>\<^sub>p") where "\<^bold>\<box>\<^sub>p A \<equiv> \<lambda>w. (\<forall>x. pv (w)(x) \<longrightarrow> A(x))" (*in all potential worlds*)
 abbreviation ddldiaa::\<gamma> ("\<^bold>\<diamond>\<^sub>a") where "\<^bold>\<diamond>\<^sub>a A \<equiv> \<^bold>\<not>\<^bold>\<box>\<^sub>a (\<^bold>\<not>A)" 
 abbreviation ddldiap::\<gamma> ("\<^bold>\<diamond>\<^sub>p") where "\<^bold>\<diamond>\<^sub>p A \<equiv> \<^bold>\<not>\<^bold>\<box>\<^sub>p (\<^bold>\<not>A)" 

 (*Necessity/possibility for agents*)
 abbreviation ddlboxa_g::\<zeta> ("\<^bold>\<box>\<^sub>a") where "\<^bold>\<box>\<^sub>a rel A \<equiv> \<lambda>w. (\<forall>x. (rel (w)(x) \<longrightarrow> A(x)))"  (*in all actual worlds*)
 abbreviation ddlboxp_g::\<zeta> ("\<^bold>\<box>\<^sub>p") where "\<^bold>\<box>\<^sub>p rel A \<equiv> \<lambda>w. (\<forall>x. (rel (w)(x) \<longrightarrow> A(x)))" (*in all potential worlds*)
 abbreviation ddldiaa_g::\<zeta> ("\<^bold>\<diamond>\<^sub>a") where "\<^bold>\<diamond>\<^sub>a rel A \<equiv> \<^bold>\<not>\<^bold>\<box>\<^sub>a (\<^bold>\<not>A)" 
 abbreviation ddldiap_g::\<zeta> ("\<^bold>\<diamond>\<^sub>p") where "\<^bold>\<diamond>\<^sub>p rel A \<equiv> \<^bold>\<not>\<^bold>\<box>\<^sub>p (\<^bold>\<not>A)" 

 (*generalised obligation operators with relation as a parameter*)
 abbreviation ddlo_g::\<nu> ("\<^bold>O _ \<^bold>\<langle>_\<^bold>|_\<^bold>\<rangle>") where "\<^bold>O rel \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<equiv> \<lambda>w. rel (A)(B)"  (*it ought to be A, given B *)
 abbreviation ddloa_g::\<mu>  ("\<^bold>O\<^sub>a ") where "\<^bold>O\<^sub>a rel1 rel2 A \<equiv> \<lambda>w. rel1(rel2(w))(A) \<and> (\<exists>x. rel2(w)(x) \<and> \<not>A(x))" (*actual obligation*)
 abbreviation ddlop_g::\<mu>  ("\<^bold>O\<^sub>p") where "\<^bold>O\<^sub>p rel1 rel2 A \<equiv> \<lambda>w. rel1(rel2(w))(A) \<and> (\<exists>x. rel2(w)(x) \<and> \<not>A(x))"  (*primary obligation*)
 
 abbreviation ddltop::\<sigma> ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<lambda>w. True"
 abbreviation ddlbot::\<sigma> ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"

(*Possibilist Quantification.*)
 abbreviation ddlforall ("\<^bold>\<forall>") where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>w.\<forall>x. (\<Phi> x w)"
 abbreviation ddlforallB (binder"\<^bold>\<forall>"[8]9) where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"  
 abbreviation ddlexists ("\<^bold>\<exists>") where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>w.\<exists>x. (\<Phi> x w)"   
 abbreviation ddlexistsB (binder"\<^bold>\<exists>"[8]9) where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>" 

 abbreviation ddlvalid::"\<sigma> \<Rightarrow> bool" ("\<lfloor>_\<rfloor>"[7]105) where "\<lfloor>A\<rfloor> \<equiv> \<forall>w. A w"   (*Global validity*)
 abbreviation ddlvalidcw::"\<sigma> \<Rightarrow> bool" ("\<lfloor>_\<rfloor>\<^sub>l"[7]105) where "\<lfloor>A\<rfloor>\<^sub>l \<equiv> A cw" (*Local validity (in cw)*)

(* A is obligatory *)
 abbreviation ddlobl::\<gamma> ("\<^bold>\<circle><_>") where "\<^bold>\<circle><A> \<equiv>  \<^bold>O ob \<^bold>\<langle>A\<^bold>|\<^bold>\<top>\<^bold>\<rangle>"  (*New syntax: A is obligatory.*)
 (*abbreviation ddloblb::\<gamma> ("\<^bold>\<circle>b<_>") where "\<^bold>\<circle>b<A> \<equiv>  \<^bold>O obb \<^bold>\<langle>A\<^bold>|\<^bold>\<top>\<^bold>\<rangle>"  (*New syntax: A is obligatory for agent b.*) 
 abbreviation ddloblc::\<gamma> ("\<^bold>\<circle>c<_>") where "\<^bold>\<circle>c<A> \<equiv>  \<^bold>O obc \<^bold>\<langle>A\<^bold>|\<^bold>\<top>\<^bold>\<rangle>"  (*New syntax: A is obligatory for agent c.*) *)
 abbreviation ddlobld::\<gamma> ("\<^bold>\<circle>d<_>") where "\<^bold>\<circle>d<A> \<equiv>  \<^bold>O obd \<^bold>\<langle>A\<^bold>|\<^bold>\<top>\<^bold>\<rangle>"  (*New syntax: A is obligatory for agent d.*)
 (*abbreviation ddloble::\<gamma> ("\<^bold>\<circle>e<_>") where "\<^bold>\<circle>e<A> \<equiv>  \<^bold>O obe \<^bold>\<langle>A\<^bold>|\<^bold>\<top>\<^bold>\<rangle>"  (*New syntax: A is obligatory for agent e.*)
 abbreviation ddloblf::\<gamma> ("\<^bold>\<circle>f<_>") where "\<^bold>\<circle>f<A> \<equiv>  \<^bold>O obf \<^bold>\<langle>A\<^bold>|\<^bold>\<top>\<^bold>\<rangle>"  (*New syntax: A is obligatory for agent f.*)
 abbreviation ddloblg::\<gamma> ("\<^bold>\<circle>g<_>") where "\<^bold>\<circle>g<A> \<equiv>  \<^bold>O obg \<^bold>\<langle>A\<^bold>|\<^bold>\<top>\<^bold>\<rangle>"  (*New syntax: A is obligatory for agent g.*)
 abbreviation ddloblh::\<gamma> ("\<^bold>\<circle>h<_>") where "\<^bold>\<circle>h<A> \<equiv>  \<^bold>O obg \<^bold>\<langle>A\<^bold>|\<^bold>\<top>\<^bold>\<rangle>"  (*New syntax: A is obligatory for agent h.*)*)

(* Consistency *) 
 lemma True nitpick [satisfy,user_axioms,show_all, card i = 2] oops 
end


