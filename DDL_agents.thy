theory DDL_agents     (* DDL: Dyadic Deontic Logic by Carmo and Jones, Benzmüller, Parent Farjami, 2018 *)
  imports Main
begin 

 typedecl i (*type for possible worlds*)
 type_synonym \<sigma> = "(i\<Rightarrow>bool)"
 type_synonym \<gamma> = "\<sigma>\<Rightarrow>\<sigma>" 
 type_synonym \<rho> = "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"
 type_synonym \<tau> = "(i\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"
 type_synonym \<mu> = "(\<sigma>\<Rightarrow>(\<sigma>\<Rightarrow>bool))\<Rightarrow>(i\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"
 type_synonym \<nu> = "(\<sigma>\<Rightarrow>(\<sigma>\<Rightarrow>bool))\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"

consts 
cw::i (*current world*)
av::"i\<Rightarrow>\<sigma>" pv::"i\<Rightarrow>\<sigma>" ob::"\<sigma>\<Rightarrow>(\<sigma>\<Rightarrow>bool)" (*general accessibility relations*)
ava::"i\<Rightarrow>\<sigma>" pva::"i\<Rightarrow>\<sigma>" oba::"\<sigma>\<Rightarrow>(\<sigma>\<Rightarrow>bool)" (*accessibility relations for agent a*)
avb::"i\<Rightarrow>\<sigma>" pvb::"i\<Rightarrow>\<sigma>" obb::"\<sigma>\<Rightarrow>(\<sigma>\<Rightarrow>bool)" (*accessibility relations for agent b*)         

(*stit operators for a and b, no meaning assigned*) 
stita::"\<sigma>\<Rightarrow>\<sigma>" (*a sees to it that*)
stitb::"\<sigma>\<Rightarrow>\<sigma>" (*b sees to it that*)

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

  (*for agent a*)
  axa_3a: "\<forall>w.\<exists>x. ava(w)(x)" and axa_4a: "\<forall>w x. ava(w)(x) \<longrightarrow> pva(w)(x)" and axa_4ba: "\<forall>w. pva(w)(w)" and
  axa_5a: "\<forall>X.\<not>oba(X)(\<lambda>x. False)" and
  axa_5b: "\<forall>X Y Z. (\<forall>w. ((Y(w) \<and> X(w)) \<longleftrightarrow> (Z(w) \<and> X(w)))) \<longrightarrow> (oba(X)(Y) \<longleftrightarrow> oba(X)(Z))" and
  axa_5ca: "\<forall>X \<beta>. ((\<forall>Z. \<beta>(Z) \<longrightarrow> oba(X)(Z)) \<and> (\<exists>Z. \<beta>(Z))) \<longrightarrow> 
      (((\<exists>y. ((\<lambda>w. \<forall>Z. (\<beta> Z) \<longrightarrow> (Z w))(y) \<and> X(y))) \<longrightarrow> oba(X)(\<lambda>w. \<forall>Z. (\<beta> Z) \<longrightarrow> (Z w))))" and
  axa_5c: "\<forall>X Y Z. (((\<exists>w. (X(w) \<and> Y(w) \<and> Z(w))) \<and>  oba(X)(Y)  \<and>  oba(X)(Z))  \<longrightarrow>  oba(X)(\<lambda>w. Y(w) \<and> Z(w)))" and
  axa_5d: "\<forall>X Y Z. ((\<forall>w. Y(w) \<longrightarrow> X(w)) \<and> oba(X)(Y) \<and> (\<forall>w. X(w) \<longrightarrow> Z(w)))
                   \<longrightarrow> oba(Z)(\<lambda>w. (Z(w) \<and> \<not>X(w)) \<or> Y(w))" and
  axa_5e: "\<forall>X Y Z. ((\<forall>w. Y(w) \<longrightarrow> X(w)) \<and> oba(X)(Z) \<and> (\<exists>w. Y(w) \<and> Z(w))) \<longrightarrow> oba(Y)(Z)" and

  (*for agent b*)
  axb_3: "\<forall>w.\<exists>x. avb(w)(x)" and axb_4a: "\<forall>w x. avb(w)(x) \<longrightarrow> pvb(w)(x)" and axb_4ba: "\<forall>w. pvb(w)(w)" and
  axb_5a: "\<forall>X.\<not>obb(X)(\<lambda>x. False)" and
  axb_5b: "\<forall>X Y Z. (\<forall>w. ((Y(w) \<and> X(w)) \<longleftrightarrow> (Z(w) \<and> X(w)))) \<longrightarrow> (obb(X)(Y) \<longleftrightarrow> obb(X)(Z))" and
  axb_5ca: "\<forall>X \<beta>. ((\<forall>Z. \<beta>(Z) \<longrightarrow> obb(X)(Z)) \<and> (\<exists>Z. \<beta>(Z))) \<longrightarrow> 
      (((\<exists>y. ((\<lambda>w. \<forall>Z. (\<beta> Z) \<longrightarrow> (Z w))(y) \<and> X(y))) \<longrightarrow> obb(X)(\<lambda>w. \<forall>Z. (\<beta> Z) \<longrightarrow> (Z w))))" and
  axb_5c: "\<forall>X Y Z. (((\<exists>w. (X(w) \<and> Y(w) \<and> Z(w))) \<and>  obb(X)(Y)  \<and>  obb(X)(Z))  \<longrightarrow>  obb(X)(\<lambda>w. Y(w) \<and> Z(w)))" and
  axb_5d: "\<forall>X Y Z. ((\<forall>w. Y(w) \<longrightarrow> X(w)) \<and> obb(X)(Y) \<and> (\<forall>w. X(w) \<longrightarrow> Z(w)))
                   \<longrightarrow> obb(Z)(\<lambda>w. (Z(w) \<and> \<not>X(w)) \<or> Y(w))" and
  axb_5e: "\<forall>X Y Z. ((\<forall>w. Y(w) \<longrightarrow> X(w)) \<and> obb(X)(Z) \<and> (\<exists>w. Y(w) \<and> Z(w))) \<longrightarrow> obb(Y)(Z)"

 abbreviation ddlneg::\<gamma> ("\<^bold>\<not>_"[52]53) where "\<^bold>\<not>A \<equiv> \<lambda>w. \<not>A(w)" 
 abbreviation ddland::\<rho> (infixr"\<^bold>\<and>"51) where "A\<^bold>\<and>B \<equiv> \<lambda>w. A(w)\<and>B(w)"   
 abbreviation ddlor::\<rho> (infixr"\<^bold>\<or>"50) where "A\<^bold>\<or>B \<equiv> \<lambda>w. A(w)\<or>B(w)"   
 abbreviation ddlimp::\<rho> (infixr"\<^bold>\<rightarrow>"49) where "A\<^bold>\<rightarrow>B \<equiv> \<lambda>w. A(w)\<longrightarrow>B(w)"  
 abbreviation ddlequiv::\<rho> (infixr"\<^bold>\<leftrightarrow>"48) where "A\<^bold>\<leftrightarrow>B \<equiv> \<lambda>w. A(w)\<longleftrightarrow>B(w)"  
 abbreviation ddlbox::\<gamma> ("\<^bold>\<box>") where "\<^bold>\<box>A \<equiv> \<lambda>w.\<forall>v. A(v)"  (*A = (\<lambda>w. True)*) 
 abbreviation ddldia_g::\<gamma>  ("\<^bold>\<diamond>") where "\<^bold>\<diamond> A \<equiv> \<^bold>\<not>\<^bold>\<box>(\<^bold>\<not>A)"

(*generalised operators with relation as a parameter*)
 abbreviation ddlboxa_g::\<tau> ("\<^bold>\<box>\<^sub>a") where "\<^bold>\<box>\<^sub>a rel A \<equiv> \<lambda>w. (\<forall>x. rel (w)(x) \<longrightarrow> A(x))"  (*in all actual worlds*)
 abbreviation ddlboxp_g::\<tau> ("\<^bold>\<box>\<^sub>p") where "\<^bold>\<box>\<^sub>p rel A \<equiv> \<lambda>w. (\<forall>x. rel (w)(x) \<longrightarrow> A(x))" (*in all potential worlds*)
 abbreviation ddldiaa_g::\<tau> ("\<^bold>\<diamond>\<^sub>a") where "\<^bold>\<diamond>\<^sub>a rel A \<equiv> \<^bold>\<not>\<^bold>\<box>\<^sub>a rel (\<^bold>\<not>A)" 
 abbreviation ddldiap_g::\<tau> ("\<^bold>\<diamond>\<^sub>p") where "\<^bold>\<diamond>\<^sub>p rel A \<equiv> \<^bold>\<not>\<^bold>\<box>\<^sub>p rel (\<^bold>\<not>A)" 
 abbreviation ddlo_g::\<nu> ("\<^bold>O _ \<^bold>\<langle>_\<^bold>|_\<^bold>\<rangle>") where "\<^bold>O rel \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<equiv> \<lambda>w. rel (A)(B)"  (*it ought to be \<psi>, given \<phi> *)
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

(* A is obliagtory *)
 abbreviation ddlobl::\<gamma> ("\<^bold>\<circle><_>") where "\<^bold>\<circle><A> \<equiv>  \<^bold>O ob \<^bold>\<langle>A\<^bold>|\<^bold>\<top>\<^bold>\<rangle>"  (*New syntax: A is obligatory.*)
 abbreviation ddlobla::\<gamma> ("\<^bold>\<circle>a<_>") where "\<^bold>\<circle>a<A> \<equiv>  \<^bold>O oba \<^bold>\<langle>A\<^bold>|\<^bold>\<top>\<^bold>\<rangle>"  (*New syntax: A is obligatory for agent a.*)
 abbreviation ddloblb::\<gamma> ("\<^bold>\<circle>b<_>") where "\<^bold>\<circle>b<A> \<equiv>  \<^bold>O obb \<^bold>\<langle>A\<^bold>|\<^bold>\<top>\<^bold>\<rangle>"  (*New syntax: A is obligatory for agent a.*) 

(* Consistency *) 
 lemma True nitpick [satisfy,user_axioms,show_all] oops 
end


