theory CJ_DDL_agents_Tests imports DDL_agents_clean           (* Christoph Benzmüller, Ali Farjami, Xavier Parent, 2020  *)
begin (* Some Tests on the Meta-Theory of DDL*)
lemma True nitpick [satisfy,user_axioms,expect=genuine] oops  (* Consistency confirmed by Nitpick *)  
 
lemma MP: "\<lbrakk>\<lfloor>A\<rfloor>; \<lfloor>A \<^bold>\<rightarrow> B\<rfloor>\<rbrakk> \<Longrightarrow> \<lfloor>B\<rfloor>" by simp
lemma Nec: "\<lfloor>A\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>\<box>A\<rfloor>" by simp
lemma Neca: "\<lfloor>A\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>\<box>\<^sub>a av A\<rfloor>"  by simp
lemma Necp: "\<lfloor>A\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>\<box>\<^sub>p pv A\<rfloor>"  by simp

(* "\<^bold>\<box>" is an S5 modality *)
lemma C_1_refl: "\<lfloor>\<^bold>\<box>A \<^bold>\<rightarrow> A\<rfloor>" by simp
lemma C_1_trans: "\<lfloor>\<^bold>\<box>A \<^bold>\<rightarrow> (\<^bold>\<box>(\<^bold>\<box>A))\<rfloor>"  by simp
lemma C_1_sym: "\<lfloor>A \<^bold>\<rightarrow> (\<^bold>\<box>(\<^bold>\<diamond>A))\<rfloor>"  by simp

(* "\<^bold>\<box>\<^sub>p" is an KT modality *)
lemma C_9_p_refl: "\<lfloor>\<^bold>\<box>\<^sub>p pv A \<^bold>\<rightarrow> A\<rfloor>"  by (simp add: ax_4b)
lemma "\<lfloor>\<^bold>\<box>\<^sub>p pv A \<^bold>\<rightarrow> (\<^bold>\<box>\<^sub>p pv (\<^bold>\<box>\<^sub>p pv A))\<rfloor>" nitpick [user_axioms] oops (*ran out of time*)
lemma "\<lfloor>A \<^bold>\<rightarrow> (\<^bold>\<box>\<^sub>p pv (\<^bold>\<diamond>\<^sub>p pv A))\<rfloor>"   nitpick [user_axioms] oops (* counterexample*)

(* "\<^bold>\<box>\<^sub>a" is an KD modality *)
lemma C_10_a_serial: "\<lfloor>\<^bold>\<box>\<^sub>a av A \<^bold>\<rightarrow> \<^bold>\<diamond>\<^sub>a av A\<rfloor>"  by (simp add: ax_3a) 
lemma "\<lfloor>\<^bold>\<box>\<^sub>a av A \<^bold>\<rightarrow> A\<rfloor>" nitpick [user_axioms] oops (* countermodel *)
lemma "\<lfloor>\<^bold>\<box>\<^sub>a av A \<^bold>\<rightarrow> (\<^bold>\<box>\<^sub>a av (\<^bold>\<box>\<^sub>a av A))\<rfloor>" nitpick [user_axioms] oops (* countermodel *)
lemma "\<lfloor>A \<^bold>\<rightarrow> (\<^bold>\<box>\<^sub>a av (\<^bold>\<diamond>\<^sub>a av A))\<rfloor>" nitpick [user_axioms] oops (* countermodel *)

(* Relationship between "\<^bold>\<box>,\<^bold>\<box>\<^sub>a,\<^bold>\<box>\<^sub>p" *)
lemma C_11: "\<lfloor>\<^bold>\<box> A \<^bold>\<rightarrow> \<^bold>\<box>\<^sub>p pv A\<rfloor>" by simp 
lemma C_12: "\<lfloor>\<^bold>\<box>\<^sub>p pv A \<^bold>\<rightarrow> \<^bold>\<box>\<^sub>a av A\<rfloor>"  using ax_4a by auto

(* Observation II-2-1 *)
lemma ax_5b': "ob X Y \<longleftrightarrow> ob X (\<lambda>z. X z \<and> Y z)" by (metis (no_types, lifting) ax_5b) 
lemma ax_5b'': "ob X Y \<longleftrightarrow> ob X (\<lambda>z. Y z \<and> X z)" by (metis (no_types, lifting) ax_5b) 

(* Characterisation of "\<^bold>O" *)
lemma C_2: "\<lfloor>\<^bold>O ob \<^bold>\<langle>A\<^bold>|B\<^bold>\<rangle> \<^bold>\<rightarrow> \<^bold>\<diamond>(B \<^bold>\<and> A)\<rfloor>" by (metis ax_5a ax_5b)  
lemma C_3: "\<lfloor>(\<^bold>\<diamond>(A \<^bold>\<and> B \<^bold>\<and> C) \<^bold>\<and> \<^bold>O ob \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>O ob \<^bold>\<langle>C\<^bold>|A\<^bold>\<rangle> ) \<^bold>\<rightarrow> \<^bold>O ob\<^bold>\<langle>(B \<^bold>\<and> C)\<^bold>|A\<^bold>\<rangle>\<rfloor>" using ax_5c by auto 
lemma C_4: "\<lfloor>(\<^bold>\<box>(A \<^bold>\<rightarrow> B) \<^bold>\<and> (\<^bold>\<diamond>(A \<^bold>\<and> C)) \<^bold>\<and> \<^bold>O ob \<^bold>\<langle>C\<^bold>|B\<^bold>\<rangle>) \<^bold>\<rightarrow> \<^bold>O ob \<^bold>\<langle>C\<^bold>|A\<^bold>\<rangle>\<rfloor>"  using ax_5e by blast
lemma C_5: "\<lfloor>\<^bold>\<box>(A \<^bold>\<leftrightarrow> B) \<^bold>\<rightarrow> (\<^bold>O ob \<^bold>\<langle>C\<^bold>|A\<^bold>\<rangle> \<^bold>\<leftrightarrow> \<^bold>O ob \<^bold>\<langle>C\<^bold>|B\<^bold>\<rangle>)\<rfloor>"  by presburger 
lemma C_6: "\<lfloor>\<^bold>\<box>(C \<^bold>\<rightarrow> (A \<^bold>\<leftrightarrow> B)) \<^bold>\<rightarrow> (\<^bold>O ob \<^bold>\<langle>A\<^bold>|C\<^bold>\<rangle> \<^bold>\<leftrightarrow> \<^bold>O ob \<^bold>\<langle>B\<^bold>|C\<^bold>\<rangle>)\<rfloor>"  by (metis ax_5b) 
lemma C_7: "\<lfloor>\<^bold>O ob \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>O ob \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>)\<rfloor>"  by blast 
lemma C_8: "\<lfloor>\<^bold>O ob \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<rightarrow> \<^bold>O ob \<^bold>\<langle>(A \<^bold>\<rightarrow> B)\<^bold>|\<^bold>\<top>\<^bold>\<rangle>\<rfloor>"  
 proof -   
   have  "\<forall>X Y Z. (ob X Y \<and> (\<forall>w. X w  \<longrightarrow> Z w)) \<longrightarrow> ob Z (\<lambda>w. (Z w \<and> \<not>X w) \<or> Y w)" 
     by  (smt ax_5d  ax_5b ax_5b'')
     thus ?thesis using ax_5b by fastforce qed

(* Relationship between "\<^bold>O\<^sub>a,\<^bold>O\<^sub>p,\<^bold>\<box>\<^sub>a,\<^bold>\<box>\<^sub>p" *)
lemma C_13_a: "\<lfloor>\<^bold>\<box>\<^sub>a av A \<^bold>\<rightarrow> (\<^bold>\<not>\<^bold>O\<^sub>a ob av A \<^bold>\<and> \<^bold>\<not>\<^bold>O\<^sub>a ob av (\<^bold>\<not>A))\<rfloor>"  by (metis (full_types) ax_5a ax_5b)
lemma C_13_b: "\<lfloor>\<^bold>\<box>\<^sub>p pv A \<^bold>\<rightarrow> (\<^bold>\<not>\<^bold>O\<^sub>p ob pv A \<^bold>\<and> \<^bold>\<not>\<^bold>O\<^sub>p ob pv (\<^bold>\<not>A))\<rfloor>"   by (metis (full_types) ax_5a ax_5b) 
lemma C_14_a: "\<lfloor>\<^bold>\<box>\<^sub>a av (A \<^bold>\<leftrightarrow> B) \<^bold>\<rightarrow> (\<^bold>O\<^sub>a ob av A \<^bold>\<leftrightarrow> \<^bold>O\<^sub>a ob av B)\<rfloor>"  by (metis ax_5b)
lemma C_14_b: "\<lfloor>\<^bold>\<box>\<^sub>p pv (A \<^bold>\<leftrightarrow> B) \<^bold>\<rightarrow> (\<^bold>O\<^sub>p ob pv A \<^bold>\<leftrightarrow> \<^bold>O\<^sub>p ob pv B)\<rfloor>"  by (metis ax_5b)

(* Relationship between "\<^bold>O\<^sub>,\<^bold>O\<^sub>a,\<^bold>O\<^sub>p,\<^bold>\<box>\<^sub>a,\<^bold>\<box>\<^sub>p" *)
lemma C_15_a: "\<lfloor>(\<^bold>O ob \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<box>\<^sub>a av A \<^bold>\<and> \<^bold>\<diamond>\<^sub>a av B \<^bold>\<and> \<^bold>\<diamond>\<^sub>a av (\<^bold>\<not>B)) \<^bold>\<rightarrow> \<^bold>O\<^sub>a ob av B\<rfloor>"  using ax_5e by blast
lemma C_15_b: "\<lfloor>(\<^bold>O ob \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<box>\<^sub>p pv A \<^bold>\<and> \<^bold>\<diamond>\<^sub>p pv B \<^bold>\<and> \<^bold>\<diamond>\<^sub>p pv (\<^bold>\<not>B)) \<^bold>\<rightarrow> \<^bold>O\<^sub>p ob pv B\<rfloor>"  using ax_5e by blast

(* Soundness and consistency *)
lemma II_3_1: "((\<lfloor>\<^bold>O ob \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>\<rfloor>) \<and> (\<exists>x. Z(x) \<and> A(x) \<and> B(x))) \<longrightarrow> ob(Z)(A \<^bold>\<rightarrow> B)" 
  proof 
    assume "(\<lfloor>\<^bold>O ob \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>\<rfloor>) \<and> (\<exists>x. Z(x) \<and> A(x) \<and> B(x))"
     hence "ob (\<lambda>z. A z \<and> Z z) (\<lambda>z. A z \<and> Z z \<and> B z)" using ax_5e ax_5b  ax_5b' ax_5d by smt
     hence "ob (\<lambda>z. Z z \<and> A z) (\<lambda>z. Z z \<and> A z \<and> B z)" using ax_5e ax_5b  ax_5b' ax_5d by smt
     hence "ob Z (\<lambda>w. (Z w \<and> \<not>(Z w \<and> A w)) \<or> (Z w \<and> A w \<and> B w))" by (metis (mono_tags) ax_5d) 
     from this show  L19: "ob(Z)(A \<^bold>\<rightarrow> B)" by (smt ax_5b) qed

(* Some theorems and derived (proof) rules *)
lemma II_4_1: "\<lfloor>\<^bold>\<box>(A \<^bold>\<leftrightarrow> B) \<^bold>\<rightarrow> (C(A) \<^bold>\<leftrightarrow> C(B))\<rfloor>"  using ext by blast
lemma obs_II_4_1_a  : "\<lfloor>A \<^bold>\<leftrightarrow> B\<rfloor> \<Longrightarrow> \<lfloor>C(A) \<^bold>\<leftrightarrow> C(B)\<rfloor>"  using ext by blast 
lemma obs_II_4_1_b  : "\<lfloor>A \<^bold>\<leftrightarrow> B\<rfloor> \<Longrightarrow> \<lfloor>(\<^bold>\<diamond>(A \<^bold>\<and> C) \<^bold>\<and> \<^bold>O ob \<^bold>\<langle>C\<^bold>|B\<^bold>\<rangle>) \<^bold>\<rightarrow> \<^bold>O ob \<^bold>\<langle>C\<^bold>|A\<^bold>\<rangle>\<rfloor>"  using ax_5e by blast
lemma obs_II_4_1_c_1: "\<lfloor>\<^bold>\<diamond>(\<^bold>O ob \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<box>(\<^bold>O ob \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>))\<rfloor>"  by blast
lemma obs_II_4_1_c_2: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<box>(\<^bold>O ob \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>)) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>O ob \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>)\<rfloor>"  by auto
lemma obs_II_4_1_c_3: "\<lfloor>\<^bold>\<diamond>(\<^bold>O ob \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>O ob \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>)\<rfloor>"  by blast
lemma obs_II_4_1_c_4: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<not>(\<^bold>O ob \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<not>(\<^bold>O ob \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>))\<rfloor>"  by blast
lemma res_II_4_1_a_1: "\<lfloor>\<^bold>\<not>(\<^bold>O ob \<^bold>\<langle>\<^bold>\<bottom>\<^bold>|A\<^bold>\<rangle>)\<rfloor>"  by (simp add: ax_5a)  
lemma res_II_4_1_a_2: "\<lfloor>(\<^bold>\<diamond>\<^sub>p pv (A \<^bold>\<and> B \<^bold>\<and> C) \<^bold>\<and> \<^bold>O ob \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>O ob \<^bold>\<langle>C\<^bold>|A\<^bold>\<rangle>) \<^bold>\<rightarrow> \<^bold>O ob \<^bold>\<langle>(B \<^bold>\<and> C)\<^bold>|A\<^bold>\<rangle>\<rfloor>"  using C_3  by auto
lemma res_II_4_1_a_3: "\<lfloor>\<^bold>O ob \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<rightarrow> \<^bold>O ob \<^bold>\<langle>B\<^bold>|(A \<^bold>\<and> B)\<^bold>\<rangle>\<rfloor>"  by (smt ax_5a ax_5b ax_5e)
lemma res_II_4_1_a_4: "\<lfloor>\<^bold>\<diamond>\<^sub>p pv (\<^bold>O ob \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>) \<^bold>\<rightarrow> \<^bold>\<box>\<^sub>p pv (\<^bold>O ob \<^bold>\<langle>B\<^bold>|(A \<^bold>\<and> B)\<^bold>\<rangle>)\<rfloor>"  by (smt ax_5a ax_5b ax_5e)
lemma res_II_4_1_a_5: "\<lfloor>(\<^bold>\<diamond>\<^sub>p pv (A \<^bold>\<and> B \<^bold>\<and> C) \<^bold>\<and> \<^bold>O ob \<^bold>\<langle>C\<^bold>|A\<^bold>\<rangle>) \<^bold>\<rightarrow> \<^bold>O ob \<^bold>\<langle>C\<^bold>|(A \<^bold>\<and> B)\<^bold>\<rangle>\<rfloor>"  by (smt ax_5a ax_5b ax_5e)
lemma res_II_4_1_b_1:  "\<lfloor>A \<^bold>\<leftrightarrow> B\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>O ob \<^bold>\<langle>C\<^bold>|A\<^bold>\<rangle> \<^bold>\<leftrightarrow> \<^bold>O ob \<^bold>\<langle>C\<^bold>|B\<^bold>\<rangle>\<rfloor>"  by (smt ax_5a ax_5b ax_5e)
lemma res_II_4_1_b_2:  "\<lfloor>C \<^bold>\<rightarrow> (A \<^bold>\<leftrightarrow> B)\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>O ob \<^bold>\<langle>A\<^bold>|C\<^bold>\<rangle> \<^bold>\<leftrightarrow> \<^bold>O ob \<^bold>\<langle>B\<^bold>|C\<^bold>\<rangle>\<rfloor>"  by (smt ax_5b)
lemma obs_II_4_2_1: "\<lfloor>(\<^bold>O ob \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>a av (A \<^bold>\<and> B) \<^bold>\<and> \<^bold>\<diamond>\<^sub>a av (A \<^bold>\<and> \<^bold>\<not>B)) \<^bold>\<rightarrow> (\<^bold>O ob \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>a av (A \<^bold>\<rightarrow> B) \<^bold>\<and> \<^bold>\<diamond>\<^sub>a av (\<^bold>\<not>(A \<^bold>\<rightarrow> B)))\<rfloor>"  by blast
lemma obs_II_4_2_2: "\<lfloor>\<^bold>O ob \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<rightarrow> \<^bold>O ob \<^bold>\<langle>(A \<^bold>\<rightarrow> B)\<^bold>|\<^bold>\<top>\<^bold>\<rangle>\<rfloor>" by (simp add: C_8)
lemma obs_II_4_2_3: "\<lfloor>(\<^bold>O ob \<^bold>\<langle>(A \<^bold>\<rightarrow> B)\<^bold>|\<^bold>\<top>\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<box>\<^sub>a av \<^bold>\<top> \<^bold>\<and> \<^bold>\<diamond>\<^sub>a av (A \<^bold>\<rightarrow> B) \<^bold>\<and> \<^bold>\<diamond>\<^sub>a av (\<^bold>\<not>(A \<^bold>\<rightarrow> B))) \<^bold>\<rightarrow> \<^bold>O\<^sub>a ob av (A \<^bold>\<rightarrow> B)\<rfloor>"  by (smt ax_5e)
lemma obs_II_4_2_4: "\<lfloor>\<^bold>\<box>\<^sub>a av \<^bold>\<top>\<rfloor>"  by simp
lemma obs_II_4_2_5: "\<lfloor>(\<^bold>O ob \<^bold>\<langle>(A \<^bold>\<rightarrow> B)\<^bold>|\<^bold>\<top>\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>a av (A \<^bold>\<rightarrow> B) \<^bold>\<and> \<^bold>\<diamond>\<^sub>a av (\<^bold>\<not>(A \<^bold>\<rightarrow> B))) \<^bold>\<rightarrow> \<^bold>O\<^sub>a ob av (A \<^bold>\<rightarrow> B)\<rfloor>"  by (smt ax_5e)
lemma obs_II_4_2_6: "\<lfloor>(\<^bold>O ob \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>a av (A \<^bold>\<and> B) \<^bold>\<and> \<^bold>\<diamond>\<^sub>a av (A \<^bold>\<and> \<^bold>\<not>B)) \<^bold>\<rightarrow> \<^bold>O\<^sub>a ob av (A \<^bold>\<rightarrow> B)\<rfloor>"   by (simp add: II_3_1)  
lemma obs_II_4_2_6_p: "\<lfloor>(\<^bold>O ob \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>p pv (A \<^bold>\<and> B) \<^bold>\<and> \<^bold>\<diamond>\<^sub>p pv (A \<^bold>\<and> \<^bold>\<not>B)) \<^bold>\<rightarrow> \<^bold>O\<^sub>p ob pv (A \<^bold>\<rightarrow> B)\<rfloor>"  by (simp add: II_3_1)  

lemma Oa_C: "\<lfloor>\<^bold>\<diamond>\<^sub>a av (A \<^bold>\<and> B) \<^bold>\<and> \<^bold>O\<^sub>a ob av A \<^bold>\<and> \<^bold>O\<^sub>a ob av B \<^bold>\<rightarrow>  \<^bold>O\<^sub>a ob av (A \<^bold>\<and> B)\<rfloor>" using ax_5c by auto
lemma Op_C: "\<lfloor>\<^bold>\<diamond>\<^sub>p pv (A \<^bold>\<and> B) \<^bold>\<and> \<^bold>O\<^sub>p ob pv A \<^bold>\<and> \<^bold>O\<^sub>p ob pv B \<^bold>\<rightarrow>  \<^bold>O\<^sub>p ob pv (A \<^bold>\<and> B)\<rfloor>" using ax_5c by auto
lemma Oa_DD: "\<lfloor>(\<^bold>O\<^sub>a ob av A \<^bold>\<and> \<^bold>O ob \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>a av (A \<^bold>\<and> B)) \<^bold>\<rightarrow> \<^bold>O\<^sub>a ob av (A \<^bold>\<and> B)\<rfloor>" using ax_5b ax_5c obs_II_4_2_6 by smt 
declare [[smt_timeout=300]]
lemma Op_DD: "\<lfloor>(\<^bold>O\<^sub>p ob pv A \<^bold>\<and> \<^bold>O ob \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>p pv (A \<^bold>\<and> B)) \<^bold>\<rightarrow> \<^bold>O\<^sub>p ob pv (A \<^bold>\<and> B)\<rfloor>" using ax_5b ax_5c obs_II_4_2_6_p by smt

(*Tests for agent d*)
(* Observation II-2-1 *)
lemma dax_5b': "obd X Y \<longleftrightarrow> obd X (\<lambda>z. X z \<and> Y z)" by (metis (no_types, lifting) axd_5b) 
lemma dax_5b'': "obd X Y \<longleftrightarrow> obd X (\<lambda>z. Y z \<and> X z)" by (simp add: axd_5b)

(* Characterisation of "\<^bold>O" *)
lemma dC_2: "\<lfloor>\<^bold>O obd \<^bold>\<langle>A\<^bold>|B\<^bold>\<rangle> \<^bold>\<rightarrow> \<^bold>\<diamond>(B \<^bold>\<and> A)\<rfloor>" by (metis axd_5a axd_5b) 
lemma dC_3: "\<lfloor>(\<^bold>\<diamond>(A \<^bold>\<and> B \<^bold>\<and> C) \<^bold>\<and> \<^bold>O obd \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>O obd \<^bold>\<langle>C\<^bold>|A\<^bold>\<rangle> ) \<^bold>\<rightarrow> \<^bold>O obd \<^bold>\<langle>(B \<^bold>\<and> C)\<^bold>|A\<^bold>\<rangle>\<rfloor>" by (metis axd_5c)
lemma dC_4: "\<lfloor>(\<^bold>\<box>(A \<^bold>\<rightarrow> B) \<^bold>\<and> (\<^bold>\<diamond>(A \<^bold>\<and> C)) \<^bold>\<and> \<^bold>O obd \<^bold>\<langle>C\<^bold>|B\<^bold>\<rangle>) \<^bold>\<rightarrow> \<^bold>O obd \<^bold>\<langle>C\<^bold>|A\<^bold>\<rangle>\<rfloor>" using axd_5e by blast
lemma dC_5: "\<lfloor>\<^bold>\<box>(A \<^bold>\<leftrightarrow> B) \<^bold>\<rightarrow> (\<^bold>O obd \<^bold>\<langle>C\<^bold>|A\<^bold>\<rangle> \<^bold>\<leftrightarrow> \<^bold>O obd \<^bold>\<langle>C\<^bold>|B\<^bold>\<rangle>)\<rfloor>" by presburger
lemma dC_6: "\<lfloor>\<^bold>\<box>(C \<^bold>\<rightarrow> (A \<^bold>\<leftrightarrow> B)) \<^bold>\<rightarrow> (\<^bold>O obd \<^bold>\<langle>A\<^bold>|C\<^bold>\<rangle> \<^bold>\<leftrightarrow> \<^bold>O obd \<^bold>\<langle>B\<^bold>|C\<^bold>\<rangle>)\<rfloor>" by (metis axd_5b)
lemma dC_7: "\<lfloor>\<^bold>O obd \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>O obd \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>)\<rfloor>" by simp 
(*lemma dC_8: "\<lfloor>\<^bold>O obd \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<rightarrow> \<^bold>O obd \<^bold>\<langle>(A \<^bold>\<rightarrow> B)\<^bold>|\<^bold>\<top>\<^bold>\<rangle>\<rfloor>" 
 proof -   
   have  "\<forall>X Y Z. (obd X Y \<and> (\<forall>w. X w  \<longrightarrow> Z w)) \<longrightarrow> obd Z (\<lambda>w. (Z w \<and> \<not>X w) \<or> Y w)" by (smt axd_5d  axd_5b axd_5b)
     thus ?thesis using axd_5b by fastforce qed*)

(* Relationship between "\<^bold>O\<^sub>a,\<^bold>O\<^sub>p,\<^bold>\<box>\<^sub>a,\<^bold>\<box>\<^sub>p" *)
lemma dC_13_a: "\<lfloor>\<^bold>\<box>\<^sub>a avd A \<^bold>\<rightarrow> (\<^bold>\<not>\<^bold>O\<^sub>a obd avd A \<^bold>\<and> \<^bold>\<not>\<^bold>O\<^sub>a obd avd (\<^bold>\<not>A))\<rfloor>" using dC_2 by auto
lemma dC_13_b: "\<lfloor>\<^bold>\<box>\<^sub>p pvd A \<^bold>\<rightarrow> (\<^bold>\<not>\<^bold>O\<^sub>p obd pvd A \<^bold>\<and> \<^bold>\<not>\<^bold>O\<^sub>p obd pvd (\<^bold>\<not>A))\<rfloor>" using dC_2 by blast 
lemma dC_14_a: "\<lfloor>\<^bold>\<box>\<^sub>a avd (A \<^bold>\<leftrightarrow> B) \<^bold>\<rightarrow> (\<^bold>O\<^sub>a obd avd A \<^bold>\<leftrightarrow> \<^bold>O\<^sub>a obd avd B)\<rfloor>" using dC_6 by blast
lemma dC_14_b: "\<lfloor>\<^bold>\<box>\<^sub>p pvd (A \<^bold>\<leftrightarrow> B) \<^bold>\<rightarrow> (\<^bold>O\<^sub>p obd pvd A \<^bold>\<leftrightarrow> \<^bold>O\<^sub>p obd pvd B)\<rfloor>" using dC_6 by blast

(* Relationship between "\<^bold>O\<^sub>,\<^bold>O\<^sub>a,\<^bold>O\<^sub>p,\<^bold>\<box>\<^sub>a,\<^bold>\<box>\<^sub>p" *)
lemma dC_15_a: "\<lfloor>(\<^bold>O obd \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<box>\<^sub>a avd A \<^bold>\<and> \<^bold>\<diamond>\<^sub>a avd B \<^bold>\<and> \<^bold>\<diamond>\<^sub>a avd (\<^bold>\<not>B)) \<^bold>\<rightarrow> \<^bold>O\<^sub>a obd avd B\<rfloor>" using dC_4 by blast
lemma dC_15_b: "\<lfloor>(\<^bold>O obd \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<box>\<^sub>p pvd A \<^bold>\<and> \<^bold>\<diamond>\<^sub>p pvd B \<^bold>\<and> \<^bold>\<diamond>\<^sub>p pvd (\<^bold>\<not>B)) \<^bold>\<rightarrow> \<^bold>O\<^sub>p obd pvd B\<rfloor>" using dC_4 by blast

(* Soundness and consistency *)
lemma dII_3_1: "((\<lfloor>\<^bold>O obd \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>\<rfloor>) \<and> (\<exists>x. Z(x) \<and> A(x) \<and> B(x))) \<longrightarrow> obd (Z)(A \<^bold>\<rightarrow> B)" 
  proof 
    assume "(\<lfloor>\<^bold>O obd \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>\<rfloor>) \<and> (\<exists>x. Z(x) \<and> A(x) \<and> B(x))"
     hence "obd (\<lambda>z. A z \<and> Z z) (\<lambda>z. A z \<and> Z z \<and> B z)" using axd_5e axd_5b axd_5b axd_5d by smt
     hence "obd (\<lambda>z. Z z \<and> A z) (\<lambda>z. Z z \<and> A z \<and> B z)" using axd_5e axd_5b axd_5b axd_5d by smt
     hence "obd Z (\<lambda>w. (Z w \<and> \<not>(Z w \<and> A w)) \<or> (Z w \<and> A w \<and> B w))" by (metis (mono_tags) axd_5d) 
     from this show  L19: "obd(Z)(A \<^bold>\<rightarrow> B)" by (smt axd_5b) qed

(* Some theorems and derived (proof) rules *)
lemma dII_4_1: "\<lfloor>\<^bold>\<box>(A \<^bold>\<leftrightarrow> B) \<^bold>\<rightarrow> (C(A) \<^bold>\<leftrightarrow> C(B))\<rfloor>"  using ext by blast
lemma dobs_II_4_1_a  : "\<lfloor>A \<^bold>\<leftrightarrow> B\<rfloor> \<Longrightarrow> \<lfloor>C(A) \<^bold>\<leftrightarrow> C(B)\<rfloor>"  using ext by blast 
lemma dobs_II_4_1_b  : "\<lfloor>A \<^bold>\<leftrightarrow> B\<rfloor> \<Longrightarrow> \<lfloor>(\<^bold>\<diamond>(A \<^bold>\<and> C) \<^bold>\<and> \<^bold>O obd \<^bold>\<langle>C\<^bold>|B\<^bold>\<rangle>) \<^bold>\<rightarrow> \<^bold>O obd \<^bold>\<langle>C\<^bold>|A\<^bold>\<rangle>\<rfloor>"  by presburger
lemma dobs_II_4_1_c_1: "\<lfloor>\<^bold>\<diamond>(\<^bold>O obd \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<box>(\<^bold>O obd \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>))\<rfloor>"  by blast
lemma dobs_II_4_1_c_2: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<box>(\<^bold>O obd \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>)) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>O obd \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>)\<rfloor>"  by auto
lemma dobs_II_4_1_c_3: "\<lfloor>\<^bold>\<diamond>(\<^bold>O obd \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>O obd \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>)\<rfloor>" by simp
lemma dobs_II_4_1_c_4: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<not>(\<^bold>O obd \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<not>(\<^bold>O obd \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>))\<rfloor>"  by blast
lemma dres_II_4_1_a_1: "\<lfloor>\<^bold>\<not>(\<^bold>O obd \<^bold>\<langle>\<^bold>\<bottom>\<^bold>|A\<^bold>\<rangle>)\<rfloor>"  by (simp add: axd_5a)  
lemma dres_II_4_1_a_2: "\<lfloor>(\<^bold>\<diamond>\<^sub>p pvd (A \<^bold>\<and> B \<^bold>\<and> C) \<^bold>\<and> \<^bold>O obd \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>O obd \<^bold>\<langle>C\<^bold>|A\<^bold>\<rangle>) \<^bold>\<rightarrow> \<^bold>O obd \<^bold>\<langle>(B \<^bold>\<and> C)\<^bold>|A\<^bold>\<rangle>\<rfloor>"  by (metis dC_3)
lemma dres_II_4_1_a_3: "\<lfloor>\<^bold>O obd \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<rightarrow> \<^bold>O obd \<^bold>\<langle>B\<^bold>|(A \<^bold>\<and> B)\<^bold>\<rangle>\<rfloor>"  by (smt (verit) dC_2 dC_4)
lemma dres_II_4_1_a_4: "\<lfloor>\<^bold>\<diamond>\<^sub>p pvd (\<^bold>O obd \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>) \<^bold>\<rightarrow> \<^bold>\<box>\<^sub>p pvd (\<^bold>O obd \<^bold>\<langle>B\<^bold>|(A \<^bold>\<and> B)\<^bold>\<rangle>)\<rfloor>" by (simp add: dres_II_4_1_a_3)
lemma dres_II_4_1_a_5: "\<lfloor>(\<^bold>\<diamond>\<^sub>p pvd (A \<^bold>\<and> B \<^bold>\<and> C) \<^bold>\<and> \<^bold>O obd \<^bold>\<langle>C\<^bold>|A\<^bold>\<rangle>) \<^bold>\<rightarrow> \<^bold>O obd \<^bold>\<langle>C\<^bold>|(A \<^bold>\<and> B)\<^bold>\<rangle>\<rfloor>" by (smt (verit) axd_5e)
lemma dres_II_4_1_b_1:  "\<lfloor>A \<^bold>\<leftrightarrow> B\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>O obd \<^bold>\<langle>C\<^bold>|A\<^bold>\<rangle> \<^bold>\<leftrightarrow> \<^bold>O obd \<^bold>\<langle>C\<^bold>|B\<^bold>\<rangle>\<rfloor>" solve_direct oops
lemma dres_II_4_1_b_2:  "\<lfloor>C \<^bold>\<rightarrow> (A \<^bold>\<leftrightarrow> B)\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>O obd \<^bold>\<langle>A\<^bold>|C\<^bold>\<rangle> \<^bold>\<leftrightarrow> \<^bold>O obd \<^bold>\<langle>B\<^bold>|C\<^bold>\<rangle>\<rfloor>" using dC_6 by auto
lemma dobs_II_4_2_1: "\<lfloor>(\<^bold>O obd \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>a avd (A \<^bold>\<and> B) \<^bold>\<and> \<^bold>\<diamond>\<^sub>a avd (A \<^bold>\<and> \<^bold>\<not>B)) \<^bold>\<rightarrow> (\<^bold>O obd \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>a avd (A \<^bold>\<rightarrow> B) \<^bold>\<and> \<^bold>\<diamond>\<^sub>a avd (\<^bold>\<not>(A \<^bold>\<rightarrow> B)))\<rfloor>" by auto
(*lemma dobs_II_4_2_2: "\<lfloor>\<^bold>O obd \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<rightarrow> \<^bold>O obd \<^bold>\<langle>(A \<^bold>\<rightarrow> B)\<^bold>|\<^bold>\<top>\<^bold>\<rangle>\<rfloor>" C8*)
lemma dobs_II_4_2_3: "\<lfloor>(\<^bold>O obd \<^bold>\<langle>(A \<^bold>\<rightarrow> B)\<^bold>|\<^bold>\<top>\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<box>\<^sub>a avd \<^bold>\<top> \<^bold>\<and> \<^bold>\<diamond>\<^sub>a avd (A \<^bold>\<rightarrow> B) \<^bold>\<and> \<^bold>\<diamond>\<^sub>a avd (\<^bold>\<not>(A \<^bold>\<rightarrow> B))) \<^bold>\<rightarrow> \<^bold>O\<^sub>a obd avd (A \<^bold>\<rightarrow> B)\<rfloor>" solve_direct oops
lemma dobs_II_4_2_4: "\<lfloor>\<^bold>\<box>\<^sub>a avd \<^bold>\<top>\<rfloor>" by simp
lemma dobs_II_4_2_5: "\<lfloor>(\<^bold>O obd \<^bold>\<langle>(A \<^bold>\<rightarrow> B)\<^bold>|\<^bold>\<top>\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>a avd (A \<^bold>\<rightarrow> B) \<^bold>\<and> \<^bold>\<diamond>\<^sub>a avd (\<^bold>\<not>(A \<^bold>\<rightarrow> B))) \<^bold>\<rightarrow> \<^bold>O\<^sub>a obd avd (A \<^bold>\<rightarrow> B)\<rfloor>" by (smt (verit, best) dC_4) 
lemma dobs_II_4_2_6: "\<lfloor>(\<^bold>O obd \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>a avd (A \<^bold>\<and> B) \<^bold>\<and> \<^bold>\<diamond>\<^sub>a avd (A \<^bold>\<and> \<^bold>\<not>B)) \<^bold>\<rightarrow> \<^bold>O\<^sub>a obd avd (A \<^bold>\<rightarrow> B)\<rfloor>" by (simp add: dII_3_1)
lemma dobs_II_4_2_6_p: "\<lfloor>(\<^bold>O obd \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>p pvd (A \<^bold>\<and> B) \<^bold>\<and> \<^bold>\<diamond>\<^sub>p pvd (A \<^bold>\<and> \<^bold>\<not>B)) \<^bold>\<rightarrow> \<^bold>O\<^sub>p obd pvd (A \<^bold>\<rightarrow> B)\<rfloor>" by (simp add: dII_3_1)

lemma dOa_C: "\<lfloor>\<^bold>\<diamond>\<^sub>a avd (A \<^bold>\<and> B) \<^bold>\<and> \<^bold>O\<^sub>a obd avd A \<^bold>\<and> \<^bold>O\<^sub>a obd avd B \<^bold>\<rightarrow>  \<^bold>O\<^sub>a obd avd (A \<^bold>\<and> B)\<rfloor>" by (metis (full_types) dC_3)
lemma dOp_C: "\<lfloor>\<^bold>\<diamond>\<^sub>p pvd (A \<^bold>\<and> B) \<^bold>\<and> \<^bold>O\<^sub>p obd pvd A \<^bold>\<and> \<^bold>O\<^sub>p obd pvd B \<^bold>\<rightarrow>  \<^bold>O\<^sub>p obd pvd (A \<^bold>\<and> B)\<rfloor>" by (metis (full_types) dC_3)
lemma dOa_DD: "\<lfloor>(\<^bold>O\<^sub>a obd avd A \<^bold>\<and> \<^bold>O obd \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>a avd (A \<^bold>\<and> B)) \<^bold>\<rightarrow> \<^bold>O\<^sub>a obd avd (A \<^bold>\<and> B)\<rfloor>" using axd_5b axd_5c dobs_II_4_2_6 by smt 
declare [[smt_timeout=300]]
lemma dOp_DD: "\<lfloor>(\<^bold>O\<^sub>p obd pvd A \<^bold>\<and> \<^bold>O obd \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>p pvd (A \<^bold>\<and> B)) \<^bold>\<rightarrow> \<^bold>O\<^sub>p obd pvd (A \<^bold>\<and> B)\<rfloor>" using axd_5b axd_5c dobs_II_4_2_6_p by smt

end
