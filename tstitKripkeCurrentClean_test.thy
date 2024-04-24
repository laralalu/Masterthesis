theory tstitKripkeCurrentClean_test
  imports 
    "tstitKripkeCurrent-clean"
    Main
begin

(*Tautologies of classical propositional calculus*)
lemma Identity: "\<lfloor>A\<rfloor>  \<Longrightarrow> \<lfloor>A\<rfloor>" by simp
lemma NonContradiction: "\<lfloor>\<^bold>\<not> (A \<^bold>\<and> (\<^bold>\<not>A))\<rfloor>" by simp
lemma ExcludedMiddle: "\<lfloor>A \<^bold>\<or> (\<^bold>\<not>A)\<rfloor>" by simp
lemma DoubleNegation: "\<lfloor>(\<^bold>\<not> (\<^bold>\<not> A)) \<^bold>\<rightarrow> A\<rfloor>" by simp
lemma Implication: "\<lfloor>A \<^bold>\<rightarrow> A\<rfloor>" by simp
lemma DeMorgan1: "\<lfloor>(\<^bold>\<not>(A \<^bold>\<and> B)) \<^bold>\<leftrightarrow> ((\<^bold>\<not> A) \<^bold>\<or> (\<^bold>\<not> B))\<rfloor>" by simp
lemma DeMorgan2:  "\<lfloor>(\<^bold>\<not>(A \<^bold>\<or> B)) \<^bold>\<leftrightarrow> ((\<^bold>\<not>A) \<^bold>\<and> (\<^bold>\<not>B))\<rfloor>" by simp
lemma Contrapositive: "\<lfloor>(A \<^bold>\<rightarrow> B) \<^bold>\<leftrightarrow> ((\<^bold>\<not>B) \<^bold>\<rightarrow> (\<^bold>\<not>A))\<rfloor>" by blast

(*S5 Box*)
lemma BoxRef: "\<lfloor>(\<^bold>\<box>A) \<^bold>\<rightarrow> A\<rfloor>" by simp
lemma BoxTrans: "\<lfloor>(\<^bold>\<box>A) \<^bold>\<rightarrow> (\<^bold>\<box>\<^bold>\<box>A)\<rfloor>" by simp 
lemma BoxSym: "\<lfloor>(\<^bold>\<box>A) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<diamond>A)\<rfloor>" by simp

(*S5 [ag]*)
lemma stitRef: "\<lfloor>([a1]A) \<^bold>\<rightarrow> A\<rfloor>" by (simp add: accReR_ag)
lemma stitTrans: "\<lfloor>([a1]A) \<^bold>\<rightarrow> ([a1]([a1]A))\<rfloor>" using accTraR_ag by blast
lemma stitSym: "\<lfloor>([a1]A) \<^bold>\<rightarrow> [a1](\<^bold>\<not>[a1](\<^bold>\<not>A))\<rfloor>" using accSymR_ag accTraR_ag by blast

(*S5 [ag]gr *)
lemma stitGrRef: "\<lfloor>([Agt] A) \<^bold>\<rightarrow> A\<rfloor>" by (simp add: accReR_set)
lemma stitGrTrans: "\<lfloor>([Agt] A) \<^bold>\<rightarrow> ([Agt]([Agt] A))\<rfloor>" using accTraR_set by blast
lemma stitGrSym: "\<lfloor>([Agt] A) \<^bold>\<rightarrow> [Agt](\<^bold>\<not><Agt>(\<^bold>\<not>A))\<rfloor>" using accSymR_set accTraR_set by blast

(*K and Nec for Box, [ag] and [g]gr*)
lemma BoxK: "\<lfloor>(\<^bold>\<box> (A \<^bold>\<rightarrow> I)) \<^bold>\<rightarrow> ((\<^bold>\<box> A) \<^bold>\<rightarrow> (\<^bold>\<box> I))\<rfloor>" by simp
lemma stitK: "\<lfloor>([a1] (A \<^bold>\<rightarrow> I)) \<^bold>\<rightarrow> (([a1] A) \<^bold>\<rightarrow> ([a1] I))\<rfloor>" by simp
lemma stitGrK: "\<lfloor>([Agt] (A \<^bold>\<rightarrow> I)) \<^bold>\<rightarrow> (([Agt] A) \<^bold>\<rightarrow> ([Agt] I))\<rfloor>" by simp
lemma BoxNec: "\<lfloor>A\<rfloor> \<Longrightarrow> \<lfloor>(\<^bold>\<box> A)\<rfloor>" by simp
lemma stitNec: "\<lfloor>A\<rfloor> \<Longrightarrow> \<lfloor>([a1] A)\<rfloor>" by simp
lemma stitGrNec: "\<lfloor>A\<rfloor> \<Longrightarrow> \<lfloor>([a1] A)\<rfloor>" by simp

(*KD4 principles for G*)
lemma NecG: "\<lfloor>A\<rfloor> \<Longrightarrow> \<lfloor>(G A)\<rfloor>" by simp
lemma KG: "\<lfloor>(G (A \<^bold>\<rightarrow> I)) \<^bold>\<rightarrow> ((G A) \<^bold>\<rightarrow> (G I))\<rfloor>" by simp
lemma FourG: "\<lfloor>(G A) \<^bold>\<rightarrow> (G G A)\<rfloor>" using RG_trans by blast 
lemma DG: "\<lfloor>\<^bold>\<not>((G A) \<^bold>\<and> (G (\<^bold>\<not> A)))\<rfloor>" using RG_serial by auto

(*K principles for H*)
lemma NecH: "\<lfloor>A\<rfloor> \<Longrightarrow> \<lfloor>(H A)\<rfloor>" by simp
lemma KH: "\<lfloor>(H(A\<^bold>\<rightarrow>B)) \<^bold>\<rightarrow> ((H A) \<^bold>\<rightarrow> (H B))\<rfloor>" by simp

(*[ag]d (dstit) tests  \<rightarrow> HortyBelnap1995 Chapter 3.1*) 
lemma REDstit: "\<lbrakk>\<lfloor>A \<^bold>\<leftrightarrow> B\<rfloor>; \<lfloor>[a1]d A\<rfloor>\<rbrakk>  \<Longrightarrow> \<lfloor>[a1]d B\<rfloor>" by simp
lemma CDstit: "\<lfloor>(([a1]d A) \<^bold>\<and> ([a1]d B)) \<^bold>\<rightarrow> ([a1]d (A \<^bold>\<and> B))\<rfloor>" by blast  
lemma TDstit: "\<lfloor>([a1]d A) \<^bold>\<rightarrow> A\<rfloor>" using accReR_ag by blast 
lemma FourDstit: "\<lfloor>([a1]d A) \<^bold>\<rightarrow> ([a1]d [a1]d A)\<rfloor>" using accReR_ag accTraR_ag by blast
lemma SAd: "\<lfloor>([a1]d ([a1]d A)) \<^bold>\<rightarrow> [a1]d A\<rfloor>" using accReR_ag by auto
lemma NSlashd: "\<lfloor>\<^bold>\<not> ([a1]d \<^bold>\<top>)\<rfloor>" by simp 
lemma SMPd: "\<lbrakk>\<lfloor>[a1]d A\<rfloor>; \<lfloor>([a1]d A) \<^bold>\<rightarrow> B\<rfloor>\<rbrakk> \<Longrightarrow> \<lfloor>[a1]d B\<rfloor>" using FourDstit by blast

(*[Agt]dgr (dstitAgt) tests \<rightarrow> HortyBelnap1995 Chapter 3.1*)
lemma REAgtDstit: "\<lbrakk>\<lfloor>A \<^bold>\<leftrightarrow> B\<rfloor>; \<lfloor>[Agt]d A\<rfloor>\<rbrakk>  \<Longrightarrow> \<lfloor>[Agt]d B\<rfloor>" by simp
lemma CAgtDstit: "\<lfloor>(([Agt]d A) \<^bold>\<and> ([Agt]d B)) \<^bold>\<rightarrow> ([Agt]d (A \<^bold>\<and> B))\<rfloor>" by blast  
lemma TAgtDstit: "\<lfloor>([Agt]d A) \<^bold>\<rightarrow> A\<rfloor>" using accReR_set by blast 
lemma FourAgtDstit: "\<lfloor>([Agt]d A) \<^bold>\<rightarrow> ([Agt]d[Agt]d A)\<rfloor>" using accReR_set accTraR_set by blast
lemma SAAgtd: "\<lfloor>([Agt]d ([a1]d A)) \<^bold>\<rightarrow> [Agt]d A\<rfloor>" using accReR_ag accReR_set by blast
lemma NSlashAgtd: "\<lfloor>\<^bold>\<not> ([Agt]d \<^bold>\<top>)\<rfloor>" by simp 
lemma SMPAgd: "\<lbrakk>\<lfloor>[Agt]d A\<rfloor>; \<lfloor>([Agt]d A) \<^bold>\<rightarrow> B\<rfloor>\<rbrakk> \<Longrightarrow> \<lfloor>[Agt]d B\<rfloor>" using FourAgtDstit by blast

(*others*)
lemma Box_i: "\<lfloor>(\<^bold>\<box> A) \<^bold>\<rightarrow> ([a1] A)\<rfloor>" by simp 
lemma i_Agt: "\<lfloor>(([a1]A) \<^bold>\<and> ([a2] B)) \<^bold>\<rightarrow> ([Agt](A \<^bold>\<and> B))\<rfloor>" by (simp add: C3 a1Set a2Set)
lemma ModusPonens: "\<lbrakk>\<lfloor>A\<rfloor>; \<lfloor>A \<^bold>\<rightarrow> B\<rfloor>\<rbrakk> \<Longrightarrow> \<lfloor>B\<rfloor>" by simp
lemma Conv_GH: "\<lfloor>A \<^bold>\<rightarrow> (G (P A))\<rfloor>" by (metis Inv Inv_def) 
lemma Conv_HG: "\<lfloor>A \<^bold>\<rightarrow> (H (F A))\<rfloor>"
  by (metis Inv Inv_def) 
lemma Connected_G: "\<lfloor>(P (F A)) \<^bold>\<rightarrow> (((F A) \<^bold>\<or> (P A)) \<^bold>\<or> A)\<rfloor>" 
  by (metis Inv C4 Inv_def) 
lemma Connected_H: "\<lfloor>(F (P A)) \<^bold>\<rightarrow> (((P A) \<^bold>\<or> (F A)) \<^bold>\<or> A)\<rfloor>"
  by (metis Inv C5 Inv_def) 
lemma AIA: "\<lfloor>((\<^bold>\<diamond> ([a1]A)) \<^bold>\<and> (\<^bold>\<diamond> ([a2]B))) \<^bold>\<rightarrow> (\<^bold>\<diamond>(([a1]A) \<^bold>\<and> ([a2]B)))\<rfloor>"
  nitpick [user_axioms] oops (*no counterexample, ran out of time*)
lemma NCUH: "\<lfloor>(F \<^bold>\<diamond>A) \<^bold>\<rightarrow> (<Agt> F A)\<rfloor>"(*it will be true at some point in the future that it is possible that A \<rightarrow>
  It is not guaranteed by a choice of all agents that it will be true at some point in the future that A*)
  nitpick [user_axioms, card i=3] oops (*no counterexample*)
lemma IRR: "\<lfloor>((\<^bold>\<box>(\<^bold>\<not> A)) \<^bold>\<and> (\<^bold>\<box>((G A) \<^bold>\<and> (H A)))) \<^bold>\<rightarrow> B\<rfloor> \<Longrightarrow> \<lfloor>B\<rfloor>" 
  nitpick [user_axioms, card i=1] oops (*no counterexample*)

end

