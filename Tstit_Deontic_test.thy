theory Tstit_Deontic_test  (*Neutral_temporal deontic stit logic*)
  imports Main Tstit_Deontic_clean
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

(*other axioms*)
lemma A1: "\<lfloor>(\<^bold>\<box>(A\<^bold>\<rightarrow>B)) \<^bold>\<rightarrow> ((\<^bold>\<box>A)\<^bold>\<rightarrow>(\<^bold>\<box>B))\<rfloor>" by simp
lemma A2: "\<lfloor>(\<^bold>\<box>A) \<^bold>\<rightarrow> A\<rfloor>" by simp                                        
lemma A3: "\<lfloor>(\<^bold>\<diamond>A) \<^bold>\<rightarrow> (\<^bold>\<box>(\<^bold>\<diamond>A))\<rfloor>" by simp
lemma A4: "\<lfloor>([a1](A \<^bold>\<rightarrow> B)) \<^bold>\<rightarrow> (([a1]A) \<^bold>\<rightarrow> ([a1]B))\<rfloor>" by simp
lemma A5: "\<lfloor>([a1]A) \<^bold>\<rightarrow> A\<rfloor>" by (simp add: accReR_ag)
lemma A6: "\<lfloor>(<a1> A) \<^bold>\<rightarrow> [a1](<a1>A)\<rfloor>" using accSymR_ag accTraR_ag by blast
lemma A7: "\<lfloor>([Ag](A \<^bold>\<rightarrow> B)) \<^bold>\<rightarrow> (([Ag]A) \<^bold>\<rightarrow> ([Ag]B))\<rfloor>" by simp
lemma A8: "\<lfloor>([Ag] A) \<^bold>\<rightarrow> A\<rfloor>" by (simp add: accReR_set)
lemma A9: "\<lfloor>(<Ag> A) \<^bold>\<rightarrow> [Ag] (<Ag> A)\<rfloor>" using accSymR_set accTraR_set by blast
lemma A10: "\<lfloor>((\<^bold>\<diamond> ([a1] A)) \<^bold>\<and> (\<^bold>\<diamond> ([a2] B))) \<^bold>\<rightarrow> (\<^bold>\<diamond>(([a1] A) \<^bold>\<and> ([a2] B)))\<rfloor>" nitpick[user_axioms, card i=3] oops (*no counterexample found*)
lemma A11: "\<lfloor>(([a1] A) \<^bold>\<and> ([a2] B)) \<^bold>\<rightarrow> ([Ag](A \<^bold>\<and> B))\<rfloor>" by (simp add: C3 a1Set a2Set)
lemma A12: "\<lfloor>(\<^bold>\<otimes> a1 (A \<^bold>\<rightarrow> B)) \<^bold>\<rightarrow> ((\<^bold>\<otimes> a1 A) \<^bold>\<rightarrow> (\<^bold>\<otimes> a1 B))\<rfloor>" by simp
lemma A13: "\<lfloor>(\<^bold>\<box> A) \<^bold>\<rightarrow> (([a1] A) \<^bold>\<and> (\<^bold>\<otimes> a1 A))\<rfloor>" by simp
lemma A14: "\<lfloor>(\<^bold>\<otimes> a1 A) \<^bold>\<rightarrow> (\<^bold>\<diamond> ([a1] A))\<rfloor>" using D9 by blast
lemma A15: "\<lfloor>(\<^bold>\<diamond> (\<^bold>\<otimes> a1 A)) \<^bold>\<rightarrow> (\<^bold>\<box> (\<^bold>\<otimes> a1 A))\<rfloor>" nitpick[user_axioms, card i=3] oops (*no counterexample found*)
lemma A16: "\<lfloor>(\<^bold>\<box> (([a1] A) \<^bold>\<rightarrow> ([a1] B))) \<^bold>\<rightarrow> ((\<^bold>\<otimes> a1 A) \<^bold>\<rightarrow> (\<^bold>\<otimes> a1 B))\<rfloor>" by (meson D11)
lemma A17: "\<lfloor>(G (A \<^bold>\<rightarrow> B)) \<^bold>\<rightarrow> ((G A) \<^bold>\<rightarrow> (G B))\<rfloor>" by simp
lemma A18: "\<lfloor>(G A ) \<^bold>\<rightarrow> (G (G A))\<rfloor>" using RG_trans by blast
lemma A19: "\<lfloor>(G A ) \<^bold>\<rightarrow> (F A)\<rfloor>" by (simp add: RG_serial)
lemma A20: "\<lfloor>(H (A \<^bold>\<rightarrow> B)) \<^bold>\<rightarrow> ((H A) \<^bold>\<rightarrow> (H B))\<rfloor>" by simp
lemma A21: "\<lfloor>A \<^bold>\<rightarrow> (G (P A))\<rfloor>" by (metis Inv Inv_def)
lemma A22: "\<lfloor>A \<^bold>\<rightarrow> (H (F A))\<rfloor>" by (metis Inv Inv_def)
lemma A23: "\<lfloor>(F (P A)) \<^bold>\<rightarrow> (((P A) \<^bold>\<or> A) \<^bold>\<or> (F A))\<rfloor>" by (metis T5 Inv Inv_def)
lemma A24: "\<lfloor>(P (F A)) \<^bold>\<rightarrow> (((P A) \<^bold>\<or> A) \<^bold>\<or> (F A))\<rfloor>" by (metis T4 Inv Inv_def)
lemma A25: "\<lfloor>(F (\<^bold>\<diamond> A)) \<^bold>\<rightarrow> (<Ag>gr (F A))\<rfloor>" nitpick[user_axioms, card i=3] oops (*no counterexample found*)
lemma R0: "\<lbrakk>\<lfloor>A\<rfloor>; \<lfloor>A \<^bold>\<rightarrow> B\<rfloor>\<rbrakk> \<Longrightarrow> \<lfloor>B\<rfloor>" by simp
lemma R1a: "\<lfloor>A\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>\<box> A\<rfloor>" by simp
lemma R1b: "\<lfloor>A\<rfloor> \<Longrightarrow> \<lfloor>G A\<rfloor>" by simp
lemma R1c: "\<lfloor>A\<rfloor> \<Longrightarrow> \<lfloor>H A\<rfloor>" by simp
lemma R2: "\<lfloor>((\<^bold>\<box>(\<^bold>\<not> A)) \<^bold>\<and> (\<^bold>\<box>((G A) \<^bold>\<and> (H A)))) \<^bold>\<rightarrow> B\<rfloor> \<Longrightarrow> \<lfloor>B\<rfloor>" nitpick[user_axioms] oops (*no counterexample found*)

(*[ag]d (dstit) tests  \<rightarrow> HortyBelnap1995 Chapter 3.1*) 
lemma REDstit: "\<lbrakk>\<lfloor>A \<^bold>\<leftrightarrow> B\<rfloor>; \<lfloor>[a1]d A\<rfloor>\<rbrakk>  \<Longrightarrow> \<lfloor>[a1]d B\<rfloor>" by simp
lemma CDstit: "\<lfloor>(([a1]d A) \<^bold>\<and> ([a1]d B)) \<^bold>\<rightarrow> ([a1]d (A \<^bold>\<and> B))\<rfloor>" by blast  
lemma TDstit: "\<lfloor>([a1]d A) \<^bold>\<rightarrow> A\<rfloor>" using accReR_ag by blast 
lemma FourDstit: "\<lfloor>([a1]d A) \<^bold>\<rightarrow> ([a1]d [a1]d A)\<rfloor>" using accReR_ag accTraR_ag by blast
lemma SAd: "\<lfloor>([a1]d ([a1]d A)) \<^bold>\<rightarrow> [a1]d A\<rfloor>" using accReR_ag by auto
lemma NSlashd: "\<lfloor>\<^bold>\<not> ([a1]d \<^bold>\<top>)\<rfloor>" by simp 
lemma SMPd: "\<lbrakk>\<lfloor>[a1]d A\<rfloor>; \<lfloor>([a1]d A) \<^bold>\<rightarrow> B\<rfloor>\<rbrakk> \<Longrightarrow> \<lfloor>[a1]d B\<rfloor>" using FourDstit by blast

(*[Ag] (dstitAg) tests \<rightarrow> HortyBelnap1995 Chapter 3.1*)
lemma REAgtDstit: "\<lbrakk>\<lfloor>A \<^bold>\<leftrightarrow> B\<rfloor>; \<lfloor>[Ag]d A\<rfloor>\<rbrakk>  \<Longrightarrow> \<lfloor>[Ag]d B\<rfloor>" by simp
lemma CAgtDstit: "\<lfloor>(([Ag]d A) \<^bold>\<and> ([Ag]d B)) \<^bold>\<rightarrow> ([Ag]d (A \<^bold>\<and> B))\<rfloor>" by blast  
lemma TAgtDstit: "\<lfloor>([Ag]d A) \<^bold>\<rightarrow> A\<rfloor>" using accReR_set by blast 
lemma FourAgtDstit: "\<lfloor>([Ag]d A) \<^bold>\<rightarrow> ([Ag]d[Ag]d A)\<rfloor>" using accReR_set accTraR_set by blast
lemma SAAgtd: "\<lfloor>([Ag]d ([a1]d A)) \<^bold>\<rightarrow> [Ag]d A\<rfloor>" using accReR_ag accReR_set by blast
lemma NSlashAgtd: "\<lfloor>\<^bold>\<not> ([Ag]d \<^bold>\<top>)\<rfloor>" by simp 
lemma SMPAgd: "\<lbrakk>\<lfloor>[Ag]d A\<rfloor>; \<lfloor>([Ag]d A) \<^bold>\<rightarrow> B\<rfloor>\<rbrakk> \<Longrightarrow> \<lfloor>[Ag]d B\<rfloor>" using FourAgtDstit by blast

end
