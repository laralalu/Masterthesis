theory tstitKripkeCurrent (*Kripke style, Lorini Emiliano*)
  imports Main 
begin
                 
declare [[show_types]]
nitpick_params[user_axioms, show_all, format=2] (*global parameter setting for nitpick*) 

typedecl i (*possible world*)
type_synonym \<sigma> = "(i\<Rightarrow>bool)"
type_synonym \<gamma> = "\<sigma>\<Rightarrow>\<sigma>"
type_synonym \<rho> = "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"
type_synonym \<delta> = "i\<Rightarrow>i\<Rightarrow>bool" (* type of accessibility relations between worlds *)

datatype ag = a1 | a2  (* dataype of mutually different agents; we provide 3, more can be added as needed *)

type_synonym \<omega> = "ag\<Rightarrow>i\<Rightarrow>i\<Rightarrow>bool"   (* type of agent dependent accessibility relations between worlds *)
type_synonym \<nu> = "(ag\<Rightarrow>bool)\<Rightarrow>i\<Rightarrow>i\<Rightarrow>bool" (* type of set-of-agents dependent accessibility relations between worlds *)

abbreviation RAgt :: "ag set" where
"RAgt \<equiv> {a1, a2}"

consts
  (*accessibility relations*)
  RBox::\<delta> (*worlds that are alternatives to each other: if (w, w1) then w1 is an alternative to w*)
  R_ag::\<omega> (*worlds that are actual choices for agent a, set of alternatives that are forced by agents i choice or action at world w*)
  R_set::\<nu> (*worlds that are actual choices for the set of Agents Agt*)
 
  RG::\<delta> (*all worlds that are the strict future of world w: (w, w1) means that w1 is the strict future of w*)
  RH::\<delta> (*all worlds that are the strict past of world w: (w, w1) means that w1 is the strict past of w*)

  Agt::"ag\<Rightarrow>bool" (*set of all agents*)

(*inverse of a relation*)
definition Inv::"\<delta> \<Rightarrow> \<delta>" ("Inv _") where 
"Inv R \<equiv> \<lambda>y x. R x y" 

lemma True nitpick [satisfy,user_axioms, show_all] oops

axiomatization where
  a1Set: "Agt a1" and
  a2Set: "Agt a2" 

axiomatization where
 (*reflexivity, symmetry, and transitivity for all equivalence relations*)
  accReR_ag:  "\<forall>a w. (R_ag a) w w" and
  accSymR_ag: "\<forall>a w v. (R_ag a) w v \<longrightarrow> (R_ag a) v w" and
  accTraR_ag: "\<forall>a w v u. ((R_ag a) w v \<and> (R_ag a) v u) \<longrightarrow> (R_ag a) w u" and

  accReRBox:  "\<forall>w. RBox w w" and
  accSymRBox: "\<forall>w v. RBox w v \<longrightarrow> RBox v w" and
  accTraRBox: "\<forall>w v u. (RBox w v \<and> RBox v u) \<longrightarrow> RBox w u" and

  accReR_set:  "\<forall>S w. (R_set S) w w" and
  accSymR_set: "\<forall>S w v. (R_set S) w v \<longrightarrow> (R_set S) v w" and
  accTraR_set: "\<forall>S w v u. ((R_set S) w v \<and> (R_set S) v u) \<longrightarrow> (R_set S) w u" 

abbreviation emptyset::"\<sigma>" ("{}") where "{} \<equiv> (\<lambda>x. False)"
abbreviation (input) big_intersection_rel::"((i\<Rightarrow>bool)\<Rightarrow>bool)\<Rightarrow>(i\<Rightarrow>bool)" ("\<^bold>\<Inter>") where "\<^bold>\<Inter> S \<equiv> \<lambda>v. \<forall>R. (S R) \<longrightarrow> (R v)"

axiomatization where
 (*axioms for RBox, Ri, Rj, and RAgt*)
  C1: "\<forall>a w1 w2. (R_ag a) w1 w2 \<longrightarrow> RBox w1 w2" and (*agents can only choose between alternatives*) 
  (*independence of agents/choices \<rightarrow> if w1 and w2 are alternatives to each other, there exists a world w which is 
  part of the actual choice of all agents \<rightarrow> see tests*)
  C2: "\<forall>w1 w2. (RBox w1 w2) \<longrightarrow> (\<exists>w. \<forall>a. (R_ag a) w1 w)" and
  C3: "\<forall>S w1 w2. ((R_set S) w1 w2) \<longrightarrow> (\<forall>a. S a \<longrightarrow> (R_ag a) w1 w2)" (*choices of agents in group are 
  made up of the choices of the intersection of choices of each individual agent, if (w1, w2) is part of R_set, 
  then for all agents a in the set, (w1, w2) is part of R_ag \<rightarrow> see test*) 

lemma C2test: 
  "(\<forall>w1 w2. (RBox w1 w2) \<longrightarrow> ((\<^bold>\<Inter> (\<lambda>S::i\<Rightarrow>bool. (\<forall>x a. (S x) \<longleftrightarrow> ((R_ag a) w1 x)))) \<noteq> {}))
    \<longleftrightarrow>
    (\<forall>w1 w2. (RBox w1 w2) \<longrightarrow> (\<exists>w. \<forall>a. (R_ag a) w1 w))"
  using C2 by metis

lemma C2test': 
   "((\<^bold>\<Inter> (\<lambda>S::i\<Rightarrow>bool. (\<forall>x a. (S x) \<longleftrightarrow> ((R_ag a) w1 x)))) \<noteq> {})
    \<longleftrightarrow>
    (\<exists>w. \<forall>a. (R_ag a) w1 w)"
  using C2 by (meson accReR_ag)

lemma C3test: "(\<forall>w1 w2. ((R_set Agt) w1 w2) 
   \<longrightarrow> ((R_ag a1) w1 w2) \<and> ((R_ag a2) w1 w2))" 
  by (simp add: C3 a1Set a2Set)

abbreviation "infinity \<equiv> \<exists>M. (\<exists>z::i. \<not>(M z) \<and> (\<exists>G. (\<forall>y::i. (\<exists>x. (M x) \<and> (G x) = y))))"

lemma assumes
  (*axioms for RG and RH*)
  RG_serial: "(\<forall>x. (\<exists>y. (RG x y)))" and (*seriality of RG*) 
  RG_trans: "(\<forall>x y z. (RG x y) \<and> (RG y z) \<longrightarrow> (RG x z))" and (*transitivity of RG*)
  C7: "\<forall>w v. ((RBox w v) \<and> w \<noteq> v) \<longrightarrow> \<not>(RG w v)" (*if worlds are in the same moment, they can't be in each others future*)
shows "infinity" nitpick[show_all] oops (* countermodel found, but only with the unwanted addition in C7*)

lemma assumes
  (*axioms for RG and RH*)
  RG_serial: "(\<forall>x. (\<exists>y. (RG x y)))" and (*seriality of RG*) 
  RG_trans: "(\<forall>x y z. (RG x y) \<and> (RG y z) \<longrightarrow> (RG x z))" and (*transitivity of RG*)
  C7: "\<forall>w v. ((RBox w v)) \<longrightarrow> \<not>(RG w v)" (*if worlds are in the same moment, they can't be in each others future*)
shows "infinity" nitpick[show_all] oops 
(*no countermodel found, time out*)
(*no countermodel for: i=2, i=3, i=4, i=5, out of time at i=6*)
(*C7 ohne w \<noteq> v impliziert infinite Modelle in Verbindung mit Serialität und Transitivität!*) 

axiomatization where
  (*axioms for RG and RH*)
  RG_serial: "(\<forall>x. (\<exists>y. (RG x y)))" and (*seriality of RG*)
  RG_trans: "(\<forall>x y z. (RG x y) \<and> (RG y z) \<longrightarrow> (RG x z))" and (*transitivity of RG*)
  Inv: "(Inv RG) = RH" and (*RH is the inverse of RG*)
  
  C4: "\<forall>u v w. ((RG w u) \<and> (RG w v)) \<longrightarrow> ((RG v u) \<or> (RG u v) \<or> u = v)" and (*future*)
  C5: "\<forall>u v w. ((RH w u) \<and> (RH w v)) \<longrightarrow> ((RH v u) \<or> (RH u v) \<or> u = v)" and (*past*)
  (* If v is in the future of w and u and v are in the same moment,  then there exists an alternative z 
  in the collective choice of all agents at w such that u is in the future of z \<rightarrow> no choice between 
  undivided histories*)
  C6: "\<forall>v w u S. (RG w v) \<and> (RBox v u) \<longrightarrow> (\<exists>z. ((R_set S) w z) \<and> (RG z u))" and
  C7: "\<forall>w v. ((RBox w v))  \<longrightarrow> \<not>(RG w v)" (*if worlds are in the same moment, they can't be in each others future*)

lemma "infinity" nitpick [show_all] oops (*no countermodel found, time out *)

(*tests: if I add w\<noteq>v: model found up until i=3, at i=4 no model is found*)
(*lemma True nitpick [satisfy, user_axioms, show_all, card i = 3] oops *)

(*usual connectives lifted*)
abbreviation dstitTop::\<sigma> ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<lambda>w. True"  
abbreviation dstitBot::\<sigma> ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"
abbreviation dstitNot::\<gamma> ("\<^bold>\<not> _ ") where "\<^bold>\<not> A  \<equiv> \<lambda>w. \<not> A (w)" 
abbreviation dstitAnd::\<rho> ("_ \<^bold>\<and>_ ") where "A \<^bold>\<and> B \<equiv> \<lambda>w. A (w) \<and> B (w)" 
abbreviation dstitOr::\<rho> ("_ \<^bold>\<or> _") where "A \<^bold>\<or> B \<equiv> \<lambda>w. A (w) \<or> B (w)"  
abbreviation dstitImp::\<rho> ("_ \<^bold>\<rightarrow> _") where "A \<^bold>\<rightarrow> B \<equiv> \<lambda>w. A (w) \<longrightarrow> B (w)" 
abbreviation dstitEqu::\<rho> ("_ \<^bold>\<leftrightarrow> _") where "A \<^bold>\<leftrightarrow> B \<equiv> \<lambda>w. A (w) \<longleftrightarrow> B (w)"
abbreviation (input) dstitNec::\<gamma> ("\<^bold>\<box> _") where "\<^bold>\<box> A \<equiv> \<lambda>w. \<forall>x. A(x)"  (*true no matter what agents do, necessarily true*) 
abbreviation (input) dstitPoss::\<gamma> ("\<^bold>\<diamond> _") where "\<^bold>\<diamond> A \<equiv> \<^bold>\<not>\<^bold>\<box>(\<^bold>\<not> A)" (*not necessary that not A, possible*) 

abbreviation tstitCstit::"ag\<Rightarrow>\<gamma>" ("[_] _") where "[k] A \<equiv> \<lambda>w. (\<forall>y. ((R_ag k) w y) \<longrightarrow> (A y))" (*Chellas Stit*)
abbreviation tstitCstitPoss::"ag\<Rightarrow>\<gamma>" ("<_> _") where "<k> A \<equiv> \<^bold>\<not>[k] \<^bold>\<not> A" (*Chellas Stit Poss*)
abbreviation tstitCstitGr::"\<gamma>" ("[Agt]_") where "[Agt] A \<equiv> \<lambda>w. (\<forall>v. ((R_set Agt) w v) \<longrightarrow> (A v))" (*Chellas stit group*)
abbreviation tstitCstitGrPoss::"\<gamma>" ("<Agt>_") where "<Agt> A \<equiv> \<^bold>\<not>([Agt] (\<^bold>\<not> A))"
abbreviation tstitDstit::"ag\<Rightarrow>\<gamma>" ("[_]d _") where "[i]d A \<equiv> ([i]A) \<^bold>\<and> \<^bold>\<not>(\<^bold>\<box>A)" (*Dstit*)
abbreviation tstitDstitPoss::"ag\<Rightarrow>\<gamma>" ("<_>d _") where "<i>d A \<equiv> \<^bold>\<not>[i]d \<^bold>\<not> A" (*Dstit Poss*)
abbreviation tstitDstitGr::"\<gamma>" ("[Agt]d _") where "[Agt]d A \<equiv> ([Agt] A) \<^bold>\<and> (\<^bold>\<not>(\<^bold>\<box>A))" (*Dstit group*)
abbreviation tstitDstitGrPoss::"\<gamma>" ("<Agt>d_") where "<Agt>d A \<equiv> \<^bold>\<not>([Agt]d(\<^bold>\<not> A))"

abbreviation (input) dstitG::\<gamma> ("G_") where "G A \<equiv> \<lambda>w. (\<forall>v. ((RG w v) \<longrightarrow> (A v)))" (*A will always be true in the future*)
abbreviation dstitH::\<gamma> ("H_") where "H A \<equiv> \<lambda>w. (\<forall>v. ((RH w v) \<longrightarrow> (A v)))" (*A has always been true in the past*)
abbreviation dstitP::\<gamma> ("P_") where "P A \<equiv> \<^bold>\<not> (H (\<^bold>\<not> A))" (*it has not always been true that not A*)
abbreviation (input) dstitF::\<gamma> ("F_") where "F A \<equiv> \<^bold>\<not> (G (\<^bold>\<not> A))" (*it will not always be true that not A*)

consts
  cw::i (*current world*)
abbreviation dstitValidLocal :: "(i\<Rightarrow>bool) \<Rightarrow> bool" ("\<Turnstile> _") where
  "\<Turnstile> A \<equiv> A cw"

abbreviation (input) dstitValidGlobal :: "(i \<Rightarrow> bool) \<Rightarrow> bool" ("\<lfloor>_\<rfloor>") where "\<lfloor>A\<rfloor> \<equiv> \<forall>w. A w" 

(*tests if I add w\<noteq>v: model found up until card i=3*)
lemma True nitpick [satisfy, user_axioms, show_all] oops

end