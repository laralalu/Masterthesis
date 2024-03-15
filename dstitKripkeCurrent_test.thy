theory dstitKripkeCurrent_test
  imports 
    dstitKripkeCurrent
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

(*Principles for \<^bold>\<box> Thesis Meder*)
lemma NecBox: "\<lfloor>A\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>\<box>A\<rfloor>" by simp
lemma KBox: "\<lfloor>(\<^bold>\<box>(A \<^bold>\<rightarrow> B)) \<^bold>\<rightarrow> ((\<^bold>\<box>A) \<^bold>\<rightarrow> (\<^bold>\<box>B))\<rfloor>" by simp
lemma TBox: "\<lfloor>(\<^bold>\<box>A) \<^bold>\<rightarrow> A\<rfloor>" by simp 
lemma BBox: "\<lfloor>(A) \<^bold>\<rightarrow> (\<^bold>\<box>(\<^bold>\<not>(\<^bold>\<box>\<^bold>\<not>A)))\<rfloor>" by simp 
lemma FourBox: "\<lfloor>(\<^bold>\<box>A) \<^bold>\<rightarrow> (\<^bold>\<box>(\<^bold>\<box>A))\<rfloor>" by simp 
lemma FiveBox: "\<lfloor>(\<^bold>\<diamond>A) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<diamond>A)\<rfloor>" by simp
lemma SerialityBox: "\<lfloor>(\<^bold>\<box>A) \<^bold>\<rightarrow> \<^bold>\<diamond>A\<rfloor>" by simp

(*S5 Principles Box*)
lemma BoxRef: "\<lfloor>(\<^bold>\<box>A) \<^bold>\<rightarrow> A\<rfloor>" by simp
lemma BoxSym: "\<lfloor>(\<^bold>\<box>A) \<^bold>\<rightarrow> (\<^bold>\<box>\<^bold>\<box>A)\<rfloor>" by simp 
lemma BoxTrans: "\<lfloor>((\<^bold>\<box>A) \<^bold>\<and> \<^bold>\<box>(A \<^bold>\<rightarrow> B)) \<^bold>\<rightarrow> \<^bold>\<box>B\<rfloor>" by simp
lemma BoxEuclidean: "\<lfloor>((\<^bold>\<box>A) \<^bold>\<and> (\<^bold>\<box>B)) \<^bold>\<rightarrow> \<^bold>\<box>(A \<^bold>\<and> B)\<rfloor>" by simp

(*Principles for [ag] (Chellas stit) Thesis Meder*)
lemma NecStit: "\<lfloor>A\<rfloor> \<Longrightarrow> \<lfloor>[(i::ag)] A\<rfloor>" by simp
lemma KStit: "\<lfloor>([(i::ag)](A \<^bold>\<rightarrow> B)) \<^bold>\<rightarrow> (([i]A) \<^bold>\<rightarrow> ([i]B))\<rfloor>" by simp
lemma TStit: "\<lfloor>([(i::ag)]A) \<^bold>\<rightarrow> A\<rfloor>" using accReR_ag by auto
lemma BStit: "\<lfloor>(A) \<^bold>\<rightarrow> ([(i::ag)](\<^bold>\<not>([i]\<^bold>\<not>A)))\<rfloor>" using accSymR_ag by blast
lemma FourStit: "\<lfloor>([(i::ag)]A) \<^bold>\<rightarrow> ([i]([i]A))\<rfloor>" using accTraR_ag by blast
lemma FiveStit: "\<lfloor>(\<^bold>\<diamond>A) \<^bold>\<rightarrow> [(i::ag)](\<^bold>\<diamond>A)\<rfloor>" by simp 
lemma SerialityStit: "\<lfloor>([i]A) \<^bold>\<rightarrow> \<^bold>\<diamond>[(i::ag)]A\<rfloor>" by simp

(*S5 Principles [ag]*)
lemma stitRef: "\<lfloor>([i]A) \<^bold>\<rightarrow> A\<rfloor>" solve_direct oops
lemma stitSym: "\<lfloor>([i]A) \<^bold>\<rightarrow> ([i]([i]A))\<rfloor>" solve_direct oops
lemma stitTrans: "\<lfloor>(([i]A) \<^bold>\<and> [i](A \<^bold>\<rightarrow> B)) \<^bold>\<rightarrow> [i]B\<rfloor>" by simp
lemma stitEuclidean: "\<lfloor>(([i]A) \<^bold>\<and> ([i]B)) \<^bold>\<rightarrow> [i](A \<^bold>\<and> B)\<rfloor>" by simp

(*[Agt] (chellas stitAgt) tests Thesis Meder*)
lemma NecAgtStit: "\<lfloor>A\<rfloor> \<Longrightarrow> \<lfloor>[Agt]gr A\<rfloor>" by simp
lemma KAgtStit: "\<lfloor>([Agt]gr (A \<^bold>\<rightarrow> B)) \<^bold>\<rightarrow> (([Agt]gr A) \<^bold>\<rightarrow> ([Agt]gr B))\<rfloor>" by simp
lemma TAgtStit: "\<lfloor>([Agt]gr A) \<^bold>\<rightarrow> A\<rfloor>" using accReR_set by blast
lemma BAgtStit: "\<lfloor>(A) \<^bold>\<rightarrow> ([Agt]gr (\<^bold>\<not>([Agt]gr \<^bold>\<not>A)))\<rfloor>" using accSymR_set by blast
lemma FourAgtStit: "\<lfloor>([Agt]gr A) \<^bold>\<rightarrow> ([Agt]gr [Agt]gr A)\<rfloor>" using accTraR_set by blast
lemma FiveAgtStit: "\<lfloor>(\<^bold>\<diamond>A) \<^bold>\<rightarrow> [Agt]gr (\<^bold>\<diamond>A)\<rfloor>" by simp               
lemma SerialityAgtStit: "\<lfloor>([Agt]gr A) \<^bold>\<rightarrow> \<^bold>\<diamond>[Agt]gr A\<rfloor>" by simp

(*S5 Principles [ag]*)
lemma stitGrRef: "\<lfloor>([S]gr A) \<^bold>\<rightarrow> A\<rfloor>" solve_direct oops
lemma stitGrSym: "\<lfloor>([S]gr A) \<^bold>\<rightarrow> ([S]gr([S]gr A))\<rfloor>" solve_direct oops
lemma stitGrTrans: "\<lfloor>(([S]gr A) \<^bold>\<and> [S]gr(A \<^bold>\<rightarrow> B)) \<^bold>\<rightarrow> [S]gr B\<rfloor>" by simp
lemma stitGrEuclidean: "\<lfloor>(([S]gr A) \<^bold>\<and> ([S]gr B)) \<^bold>\<rightarrow> [S]gr (A \<^bold>\<and> B)\<rfloor>" by simp

(*[ag]d (dstit) tests  \<rightarrow> HortyBelnap1995 Chapter 3.1*) 
lemma REDstit: "\<lbrakk>\<lfloor>A \<^bold>\<leftrightarrow> B\<rfloor>; \<lfloor>[i]d A\<rfloor>\<rbrakk>  \<Longrightarrow> \<lfloor>[i]d B\<rfloor>" by simp
lemma CDstit: "\<lfloor>(([i]d A) \<^bold>\<and> ([i]d B)) \<^bold>\<rightarrow> ([i]d (A \<^bold>\<and> B))\<rfloor>" by blast  
lemma TDstit: "\<lfloor>([i]d A) \<^bold>\<rightarrow> A\<rfloor>" using accReR_ag by blast 
lemma FourDstit: "\<lfloor>([i]d A) \<^bold>\<rightarrow> ([i]d [i]d A)\<rfloor>" using accReR_ag accTraR_ag by blast
lemma SAd: "\<lfloor>([i]d ([i]d A)) \<^bold>\<rightarrow> [i]d A\<rfloor>" solve_direct oops
lemma M: "\<lfloor>([i]d (A \<^bold>\<and> B)) \<^bold>\<rightarrow> (([i]d A) \<^bold>\<and> ([i]d B))\<rfloor>" nitpick [user_axioms] oops (*counterexample found \<rightarrow> correct!*)
lemma NSlashd: "\<lfloor>\<^bold>\<not> ([i]d \<^bold>\<top>)\<rfloor>" by simp 
lemma NSlashc: "\<lfloor>\<^bold>\<not> ([i] \<^bold>\<top>)\<rfloor>" nitpick [user_axioms] oops (*counterexample found \<rightarrow> does not hold for Chellas stit!*)
lemma SMPd: "\<lbrakk>\<lfloor>[i]d A\<rfloor>; \<lfloor>([i]d A) \<^bold>\<rightarrow> B\<rfloor>\<rbrakk> \<Longrightarrow> \<lfloor>[i]d B\<rfloor>" using FourDstit by blast

(*[Agt]dgr (dstitAgt) tests \<rightarrow> HortyBelnap1995 Chapter 3.1*)
lemma REAgtDstit: "\<lbrakk>\<lfloor>A \<^bold>\<leftrightarrow> B\<rfloor>; \<lfloor>[Agt]dgr A\<rfloor>\<rbrakk>  \<Longrightarrow> \<lfloor>[Agt]dgr B\<rfloor>" by simp
lemma CAgtDstit: "\<lfloor>(([Agt]dgr A) \<^bold>\<and> ([Agt]dgr B)) \<^bold>\<rightarrow> ([Agt]dgr (A \<^bold>\<and> B))\<rfloor>" by blast  
lemma TAgtDstit: "\<lfloor>([Agt]dgr A) \<^bold>\<rightarrow> A\<rfloor>" using accReR_set by blast 
lemma FourAgtDstit: "\<lfloor>([Agt]dgr A) \<^bold>\<rightarrow> ([Agt]dgr[Agt]dgr A)\<rfloor>" using accReR_set accTraR_set by blast
lemma SAAgtd: "\<lfloor>([Agt]dgr ([i]d A)) \<^bold>\<rightarrow> [Agt]dgr A\<rfloor>" solve_direct oops
lemma MAgtd: "\<lfloor>([Agt]dgr (A \<^bold>\<and> B)) \<^bold>\<rightarrow> (([Agt]dgr A) \<^bold>\<and> ([Agt]dgr B))\<rfloor>" nitpick [user_axioms] oops (*counterexample found \<rightarrow> correct!*)
lemma NSlashAgtd: "\<lfloor>\<^bold>\<not> ([Agt]dgr \<^bold>\<top>)\<rfloor>" by simp 
lemma NSlashAgtc: "\<lfloor>\<^bold>\<not> ([Agt]gr \<^bold>\<top>)\<rfloor>" nitpick [user_axioms] oops (*counterexample found \<rightarrow> does not hold for Chellas stit!*)
lemma SMPAgd: "\<lbrakk>\<lfloor>[Agt]dgr A\<rfloor>; \<lfloor>([Agt]dgr A) \<^bold>\<rightarrow> B\<rfloor>\<rbrakk> \<Longrightarrow> \<lfloor>[Agt]dgr B\<rfloor>" using FourAgtDstit by blast

(*All KD4 principles hold for G*)
lemma NecG: "\<lfloor>A\<rfloor> \<Longrightarrow> \<lfloor>(G A)\<rfloor>" by simp
lemma KG: "\<lfloor>(G (A \<^bold>\<rightarrow> I)) \<^bold>\<rightarrow> ((G A) \<^bold>\<rightarrow> (G I))\<rfloor>" by simp
lemma FourG: "\<lfloor>(G A) \<^bold>\<rightarrow> (G G A)\<rfloor>" using RG_trans by blast 
lemma DG: "\<lfloor>\<^bold>\<not>((G A) \<^bold>\<and> (G (\<^bold>\<not> A)))\<rfloor>" using RG_serial by auto

(*K principle hold for H*)
lemma NecH: "\<lfloor>A\<rfloor> \<Longrightarrow> \<lfloor>(H A)\<rfloor>" by simp
lemma KH: "\<lfloor>(H(A\<^bold>\<rightarrow>B)) \<^bold>\<rightarrow> ((H A) \<^bold>\<rightarrow> (H B))\<rfloor>" by simp

(*others*)
lemma Box_i: "\<lfloor>(\<^bold>\<box> A) \<^bold>\<rightarrow> ([(i::ag)] A)\<rfloor>" by simp 
lemma i_Agt: "\<lfloor>(([i]A) \<^bold>\<and> ([j] B)) \<^bold>\<rightarrow> ([S]gr(A \<^bold>\<and> B))\<rfloor>" oops
lemma ModusPonens: "\<lbrakk>\<lfloor>A\<rfloor>; \<lfloor>A \<^bold>\<rightarrow> B\<rfloor>\<rbrakk> \<Longrightarrow> \<lfloor>B\<rfloor>" by simp
lemma Conv_GH: "\<lfloor>A \<^bold>\<rightarrow> (G (P A))\<rfloor>" by (metis Inv Inv_def) 
lemma Conv_HG: "\<lfloor>A \<^bold>\<rightarrow> (H (F A))\<rfloor>"
  by (metis Inv Inv_def) 
lemma Connected_G: "\<lfloor>(P (F A)) \<^bold>\<rightarrow> (((F A) \<^bold>\<or> (P A)) \<^bold>\<or> A)\<rfloor>" 
  by (metis Inv C4 Inv_def) 
lemma Connected_H: "\<lfloor>(F (P A)) \<^bold>\<rightarrow> (((P A) \<^bold>\<or> (F A)) \<^bold>\<or> A)\<rfloor>"
  by (metis Inv C5 Inv_def) 
lemma AIA: "\<lfloor>((\<^bold>\<diamond> ([a1]A)) \<^bold>\<and> (\<^bold>\<diamond> ([a2]B))) \<^bold>\<rightarrow> (\<^bold>\<diamond>(([a1]A) \<^bold>\<and> ([a2]B)))\<rfloor>"
  nitpick [user_axioms] oops (*countermodel found for every card other then 1 if I add w \<noteq> v, else no countermodel*)
lemma AIAnew: "\<lfloor>(\<^bold>\<diamond> A)  \<^bold>\<rightarrow> (<a1> (<a2> A))\<rfloor>"  (*alternative formulation PHILIPPE BALBIANI, ANDREAS HERZIG, NICOLAS TROQUARD, p. 6*)y
  nitpick [user_axioms] oops (*countermodel found for every card other then 1 if I add w \<noteq> v, else no countermodel*)
lemma NCUH: "\<lfloor>(F \<^bold>\<diamond>A) \<^bold>\<rightarrow> (<Agt>gr F A)\<rfloor>"(*it will be true at some point in the future that it is possible that A \<rightarrow>
It is not guaranteed by a choice of all agents that it will be true at some point in the future that A*)
  nitpick [user_axioms, card i=3] oops (*countermodel found for every card other then 1 if I add w \<noteq> v, else no countermodel*)
lemma IRR: "\<lfloor>((\<^bold>\<box>(\<^bold>\<not> A)) \<^bold>\<and> (\<^bold>\<box>((G A) \<^bold>\<and> (H A)))) \<^bold>\<rightarrow> B\<rfloor> \<Longrightarrow> \<lfloor>B\<rfloor>" 
  nitpick [user_axioms, card i=1] oops (*countermodel found for every card if I add w \<noteq> v, else no countermodel*)

(*stuff that should not hold*)
lemma x1: "\<lfloor>([i]d A) \<^bold>\<rightarrow> ([j] B)\<rfloor>" nitpick [user_axioms] oops (*counterexample found*)
lemma x2: "\<lfloor>(F A) \<^bold>\<rightarrow> (P A)\<rfloor>" nitpick [user_axioms] oops (*counterexample found*)
lemma x3: "\<lfloor>([S]grd A) \<^bold>\<rightarrow> ([i] A)\<rfloor>" nitpick [user_axioms] oops (*counterexample found*)
lemma x4: "\<lfloor>((G A) \<^bold>\<rightarrow> (H A))\<rfloor>" nitpick [user_axioms] oops (*counterexample found*)

end

