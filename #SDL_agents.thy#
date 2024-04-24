theory SDL_agents
  imports types Main 
begin

consts 
  Rela::"i\<Rightarrow>i\<Rightarrow>bool" (infixr "Ra" 70) (*Accessibility relation agent a, Judicial authority or independent administrative authority of Member State.*)  
  Relb::"i\<Rightarrow>i\<Rightarrow>bool" (infixr "Rb" 70) (*Accessibility relation agent b, Importer.*) 
  Relc::"i\<Rightarrow>i\<Rightarrow>bool" (infixr "Rc" 70) (*Accessibility relation agent c, EU commission.*) 
  Reld::"i\<Rightarrow>i\<Rightarrow>bool" (infixr "Rd" 70) (*Accessibility relation agent d, Provider.*) 
  Rele::"i\<Rightarrow>i\<Rightarrow>bool" (infixr "Re" 70) (*Accessibility relation agent e, Conformity assessment body.*) 
  Relf::"i\<Rightarrow>i\<Rightarrow>bool" (infixr "Rf" 70) (*Accessibility relation agent f, Notifying authority.*) 
  Relg::"i\<Rightarrow>i\<Rightarrow>bool" (infixr "Rg" 70) (*Accessibility relation agent g, Notified body.*) 
  Relh::"i\<Rightarrow>i\<Rightarrow>bool" (infixr "Rh" 70) (*Accessibility relation agent h, Member state.*) 
  Relj::"i\<Rightarrow>i\<Rightarrow>bool" (infixr "Rj" 70) (*Accessibility relation agent j, national competent authorities.*) 
  Relk::"i\<Rightarrow>i\<Rightarrow>bool" (infixr "Rk" 70) (*Accessibility relation agent k, credit institutions.*) 
  Rell::"i\<Rightarrow>i\<Rightarrow>bool" (infixr "Rl" 70) (*Accessibility relation agent l, distributor.*) 
  Rel::"i\<Rightarrow>i\<Rightarrow>bool" (infixr "R" 70) (*General accessibility relation, not related to an agent.*)
 
  aw::i (*Actual world.*)

 (*stit operator, no meaning assigned*)
  stit::"ag\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (*ag sees to it that*) 

 abbreviation (input) SDLtop::\<sigma> ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<lambda>w. True" 
 abbreviation (input) SDLbot::\<sigma> ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<lambda>w. False" 
 abbreviation (input) SDLnot::\<gamma> ("\<^bold>\<not>_"[52]53) where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>\<phi>(w)" 
 abbreviation (input) SDLand::\<rho> (infixr"\<^bold>\<and>"51) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. \<phi>(w) \<and> \<psi>(w)"   
 abbreviation (input) SDLor::\<rho> (infixr"\<^bold>\<or>"50) where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. \<phi>(w) \<or> \<psi>(w)"   
 abbreviation (input) SDLimp::\<rho> (infixr"\<^bold>\<rightarrow>"49) where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w) \<longrightarrow> \<psi>(w)"  
 abbreviation (input) SDLequ::\<rho> (infixr"\<^bold>\<leftrightarrow>"48) where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w) \<longleftrightarrow> \<psi>(w)"  

 (*obligations (where accessibility relation is a parameter)*)
 abbreviation (input) SDLobligatoryGen::\<tau> ("OBg") where "OBg rel \<phi> \<equiv> \<lambda>w. \<forall>v.  rel w v \<longrightarrow> \<phi>(v)"
 abbreviation (input) SDLpermissibleGen::\<tau> ("PEg") where "PEg rel \<phi> \<equiv> \<^bold>\<not>(OBg rel (\<^bold>\<not>\<phi>))"
 abbreviation (input) SDLimpermissibleGen::\<tau> ("IMg") where "IMg rel \<phi> \<equiv> OBg rel (\<^bold>\<not>\<phi>)"
 abbreviation (input) SDLomissibleGen::\<tau> ("OMg") where "OMg rel \<phi> \<equiv> \<^bold>\<not>(OBg rel \<phi>)"
 abbreviation (input) SDLoptionalGen::\<tau> ("OPg") where "OPg rel \<phi> \<equiv> (\<^bold>\<not>(OBg rel \<phi>) \<^bold>\<and>  \<^bold>\<not>(OBg rel (\<^bold>\<not>\<phi>)))"

 (*Possibilist Quantification.*)
 abbreviation (input) SDLforall ("\<^bold>\<forall>") where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>w.\<forall>x. (\<Phi> x w)"
 abbreviation (input) SDLforallB (binder"\<^bold>\<forall>"[8]9) where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"  
 abbreviation (input) SDLexists ("\<^bold>\<exists>") where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>w.\<exists>x. (\<Phi> x w)"   
 abbreviation (input) SDLexistsB (binder"\<^bold>\<exists>"[8]9) where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>"

 abbreviation (input) SDLvalid::"\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>"[7]105)  where "\<lfloor>\<phi>\<rfloor> \<equiv> \<forall>w. \<phi> w"      (*Global validity.*)
 abbreviation (input) SDLvalidcw::"\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sub>l"[7]105)    where "\<lfloor>\<phi>\<rfloor>\<^sub>l \<equiv> \<phi> aw"   (*Validity in actual world.*)

 (* New syntax *)
abbreviation (input) SDLobl::\<gamma> ("\<^bold>\<circle><_>") where "\<^bold>\<circle><\<phi>> \<equiv>  OBg Rel \<phi>"  (*New syntax: A is obligatory*)

 abbreviation (input) SDLobla::\<gamma> ("\<^bold>\<circle>a<_>") where "\<^bold>\<circle>a<\<phi>> \<equiv>  OBg Rela \<phi>" (*A is obligatory for a*)
 abbreviation (input) SDLoblb::\<gamma> ("\<^bold>\<circle>b<_>") where "\<^bold>\<circle>b<\<phi>> \<equiv>  OBg Relb \<phi>" (*A is obligatory for b*)
 abbreviation (input) SDLoblc::\<gamma> ("\<^bold>\<circle>c<_>") where "\<^bold>\<circle>c<\<phi>> \<equiv>  OBg Relc \<phi>" (*A is obligatory for c*)
 abbreviation (input) SDLobld::\<gamma> ("\<^bold>\<circle>d<_>") where "\<^bold>\<circle>d<\<phi>> \<equiv>  OBg Reld \<phi>" (*A is obligatory for d*)
 abbreviation (input) SDLoble::\<gamma> ("\<^bold>\<circle>e<_>") where "\<^bold>\<circle>e<\<phi>> \<equiv>  OBg Rele \<phi>" (*A is obligatory for e*)
 abbreviation (input) SDLoblf::\<gamma> ("\<^bold>\<circle>f<_>") where "\<^bold>\<circle>f<\<phi>> \<equiv>  OBg Relf \<phi>" (*A is obligatory for f*)
 abbreviation (input) SDLoblg::\<gamma> ("\<^bold>\<circle>g<_>") where "\<^bold>\<circle>g<\<phi>> \<equiv>  OBg Relg \<phi>" (*A is obligatory for g*)
 abbreviation (input) SDLoblh::\<gamma> ("\<^bold>\<circle>h<_>") where "\<^bold>\<circle>h<\<phi>> \<equiv>  OBg Relh \<phi>" (*A is obligatory for h*)
 abbreviation (input) SDLoblj::\<gamma> ("\<^bold>\<circle>j<_>") where "\<^bold>\<circle>j<\<phi>> \<equiv>  OBg Relj \<phi>" (*A is obligatory for j*)
 abbreviation (input) SDLoblk::\<gamma> ("\<^bold>\<circle>k<_>") where "\<^bold>\<circle>k<\<phi>> \<equiv>  OBg Relk \<phi>" (*A is obligatory for k*)
 abbreviation (input) SDLobll::\<gamma> ("\<^bold>\<circle>l<_>") where "\<^bold>\<circle>l<\<phi>> \<equiv>  OBg Rell \<phi>" (*A is obligatory for l*)

(* Corrspondence, generic *)
lemma "\<lfloor>\<^bold>\<not>(OBg rel \<phi> \<^bold>\<and> OBg rel (\<^bold>\<not>\<phi>))\<rfloor> \<longleftrightarrow> (\<forall>w. \<exists>v. rel w v)"  by auto 

(* Corrspondences *)
lemma "\<lfloor>\<^bold>\<not> (\<^bold>\<circle><\<phi>> \<^bold>\<and> \<^bold>\<circle><\<^bold>\<not>\<phi>>)\<rfloor> \<longleftrightarrow> (\<forall>w. \<exists>v. w R v)" by blast
lemma "\<lfloor>\<^bold>\<not> (\<^bold>\<circle>a<\<phi>> \<^bold>\<and> \<^bold>\<circle>a<\<^bold>\<not>\<phi>>)\<rfloor> \<longleftrightarrow> (\<forall>w. \<exists>v. w Ra v)" by blast
lemma "\<lfloor>\<^bold>\<not> (\<^bold>\<circle>b<\<phi>> \<^bold>\<and> \<^bold>\<circle>b<\<^bold>\<not>\<phi>>)\<rfloor> \<longleftrightarrow> (\<forall>w. \<exists>v. w Rb v)" by blast

(* We postulate these axioms, they are computationally better suited; the other way around is 
   clearly also possible though. *)

axiomatization where 
  seriality: "(\<forall>w. \<exists>v. w R v)" and
  serialitya: "(\<forall>w. \<exists>v. w Ra v)" and
  serialityb: "(\<forall>w. \<exists>v. w Rb v)" 

lemma "\<lfloor>\<^bold>\<not> (\<^bold>\<circle><\<phi>> \<^bold>\<and> \<^bold>\<circle><\<^bold>\<not>\<phi>>)\<rfloor>" using seriality by blast
lemma "\<lfloor>\<^bold>\<not> (\<^bold>\<circle>a<\<phi>> \<^bold>\<and> \<^bold>\<circle>a<\<^bold>\<not>\<phi>>)\<rfloor>" using serialitya by blast
lemma "\<lfloor>\<^bold>\<not> (\<^bold>\<circle>b<\<phi>> \<^bold>\<and> \<^bold>\<circle>b<\<^bold>\<not>\<phi>>)\<rfloor>" using serialityb by blast

(*Consistency confirmed by model finder Nitpick.*) 
lemma True nitpick[satisfy,user_axioms,expect=genuine] oops

(*Barcan formulas, generic*) 
lemma BarcanG:         "\<lfloor>(\<^bold>\<forall>d. OBg rel (\<phi> d)) \<^bold>\<rightarrow> (OBg rel (\<^bold>\<forall>d. (\<phi> d)))\<rfloor>" by simp  
lemma CoverseBarcanG:  "\<lfloor>(OBg rel (\<^bold>\<forall>d. (\<phi> d))) \<^bold>\<rightarrow> (\<^bold>\<forall>d. OBg rel (\<phi> d))\<rfloor>" by simp  

(*Barcan formulas*) 
lemma Barcan:         "\<lfloor>(\<^bold>\<forall>d. \<^bold>\<circle><\<phi>(d)>) \<^bold>\<rightarrow> (\<^bold>\<circle><\<^bold>\<forall>d. \<phi>(d)>)\<rfloor>" by simp  
lemma ConverseBarcan: "\<lfloor>(\<^bold>\<circle><\<^bold>\<forall>d. \<phi>(d)>) \<^bold>\<rightarrow> (\<^bold>\<forall>d. \<^bold>\<circle><\<phi>(d)>)\<rfloor>" by simp 

(*Barcan formulas a (same would hold for b)*) 
lemma Barcana:         "\<lfloor>(\<^bold>\<forall>d. \<^bold>\<circle>a<\<phi>(d)>) \<^bold>\<rightarrow> (\<^bold>\<circle>a<\<^bold>\<forall>d. \<phi>(d)>)\<rfloor>" by simp  
lemma ConverseBarcaan: "\<lfloor>(\<^bold>\<circle>a<\<^bold>\<forall>d. \<phi>(d)>) \<^bold>\<rightarrow> (\<^bold>\<forall>d. \<^bold>\<circle>a<\<phi>(d)>)\<rfloor>" by simp 

(*axioms test*)
lemma OBK: "\<lfloor>\<^bold>\<circle><(p \<^bold>\<rightarrow> q)> \<^bold>\<rightarrow> (\<^bold>\<circle><p> \<^bold>\<rightarrow> \<^bold>\<circle><q> )\<rfloor>" by simp
lemma OBNC: "\<lfloor>(\<^bold>\<circle><p> \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>\<circle><\<^bold>\<not>p>)\<rfloor>" by (simp add: seriality)
lemma OBMP: "\<lbrakk>\<lfloor>\<^bold>\<circle><A>\<rfloor>; \<lfloor>\<^bold>\<circle><A> \<^bold>\<rightarrow> B\<rfloor>\<rbrakk> \<Longrightarrow> \<lfloor>B\<rfloor>" by simp
lemma OBNEC: "\<lfloor>A\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>\<circle><A>\<rfloor>" by simp

lemma OBaK: "\<lfloor>\<^bold>\<circle>a<(p \<^bold>\<rightarrow> q)> \<^bold>\<rightarrow> (\<^bold>\<circle>a<p> \<^bold>\<rightarrow> \<^bold>\<circle>a<q> )\<rfloor>" by simp
lemma OBaNC: "\<lfloor>(\<^bold>\<circle>a<p> \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>\<circle>a<\<^bold>\<not>p>)\<rfloor>" by (simp add: serialitya)
lemma OBaMP: "\<lbrakk>\<lfloor>\<^bold>\<circle>a<A>\<rfloor>; \<lfloor>\<^bold>\<circle>a<A> \<^bold>\<rightarrow> B\<rfloor>\<rbrakk> \<Longrightarrow> \<lfloor>B\<rfloor>" by simp
lemma OBaNEC: "\<lfloor>A\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>\<circle>a<A>\<rfloor>" by simp

lemma OBbK: "\<lfloor>\<^bold>\<circle>b<(p \<^bold>\<rightarrow> q)> \<^bold>\<rightarrow> (\<^bold>\<circle>b<p> \<^bold>\<rightarrow> \<^bold>\<circle>b<q> )\<rfloor>" by simp
lemma OBbNC: "\<lfloor>(\<^bold>\<circle>b<p> \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>\<circle>b<\<^bold>\<not>p>)\<rfloor>" by (simp add: serialityb)
lemma OBbMP: "\<lbrakk>\<lfloor>\<^bold>\<circle>b<A>\<rfloor>; \<lfloor>\<^bold>\<circle>b<A> \<^bold>\<rightarrow> B\<rfloor>\<rbrakk> \<Longrightarrow> \<lfloor>B\<rfloor>" by simp
lemma OBbNEC: "\<lfloor>A\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>\<circle>b<A>\<rfloor>" by simp

lemma "\<lfloor>\<^bold>\<circle>a<\<phi>> \<^bold>\<rightarrow> \<^bold>\<circle>a<\<^bold>\<circle>a<\<phi>>>\<rfloor>"
  nitpick[falsify,user_axioms,expect=genuine] oops

lemma True nitpick [satisfy, user_axioms, show_all] oops
end







