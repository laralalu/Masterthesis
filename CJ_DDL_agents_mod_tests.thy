theory CJ_DDL_agents_mod_tests imports DDL_agents_mod           (* Christoph Benzmüller, Ali Farjami, Xavier Parent, 2020  *)
begin (* Some Tests on the Meta-Theory of DDL*)
lemma True nitpick [satisfy,user_axioms,expect=genuine] oops  (* Consistency confirmed by Nitpick *)  

(* Observation II-2-1 *)
lemma dax_5b': "ob_g a X Y \<longleftrightarrow> ob_g a X (\<lambda>z. X z \<and> Y z)" by (smt (verit, ccfv_SIG) axg_5b)
lemma dax_5b'': "ob_g a X Y \<longleftrightarrow> ob_g a X (\<lambda>z. Y z \<and> X z)" by (simp add: axg_5b)

(* Characterisation of "\<^bold>O" *)
lemma dC_2: "\<lfloor>\<^bold>O a \<^bold>\<langle>A\<^bold>|B\<^bold>\<rangle> \<^bold>\<rightarrow> \<^bold>\<diamond>(B \<^bold>\<and> A)\<rfloor>" by (metis axg_5a axg_5b)
lemma dC_3: "\<lfloor>(\<^bold>\<diamond>(A \<^bold>\<and> B \<^bold>\<and> C) \<^bold>\<and> \<^bold>O a \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>O a \<^bold>\<langle>C\<^bold>|A\<^bold>\<rangle> ) \<^bold>\<rightarrow> \<^bold>O a \<^bold>\<langle>(B \<^bold>\<and> C)\<^bold>|A\<^bold>\<rangle>\<rfloor>" by (metis axg_5c)
lemma dC_4: "\<lfloor>(\<^bold>\<box>(A \<^bold>\<rightarrow> B) \<^bold>\<and> (\<^bold>\<diamond>(A \<^bold>\<and> C)) \<^bold>\<and> \<^bold>O a \<^bold>\<langle>C\<^bold>|B\<^bold>\<rangle>) \<^bold>\<rightarrow> \<^bold>O a \<^bold>\<langle>C\<^bold>|A\<^bold>\<rangle>\<rfloor>" using axg_5e by blast
lemma dC_5: "\<lfloor>\<^bold>\<box>(A \<^bold>\<leftrightarrow> B) \<^bold>\<rightarrow> (\<^bold>O a \<^bold>\<langle>C\<^bold>|A\<^bold>\<rangle> \<^bold>\<leftrightarrow> \<^bold>O a \<^bold>\<langle>C\<^bold>|B\<^bold>\<rangle>)\<rfloor>"  by presburger
lemma dC_6: "\<lfloor>\<^bold>\<box>(C \<^bold>\<rightarrow> (A \<^bold>\<leftrightarrow> B)) \<^bold>\<rightarrow> (\<^bold>O a \<^bold>\<langle>A\<^bold>|C\<^bold>\<rangle> \<^bold>\<leftrightarrow> \<^bold>O a \<^bold>\<langle>B\<^bold>|C\<^bold>\<rangle>)\<rfloor>" by (smt (verit, del_insts) axg_5b)
lemma dC_7: "\<lfloor>\<^bold>O a \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>O a \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>)\<rfloor>"  by simp
(*lemma dC_8: "\<lfloor>\<^bold>O a \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<rightarrow> \<^bold>O a \<^bold>\<langle>(A \<^bold>\<rightarrow> B)\<^bold>|\<^bold>\<top>\<^bold>\<rangle>\<rfloor>" 
 proof -   
  have  "\<forall>X Y Z. (ob_g a X Y \<and> (\<forall>w. X w  \<longrightarrow> Z w)) \<longrightarrow> ob_g a Z (\<lambda>w. (Z w \<and> \<not>X w) \<or> Y w)" by (smt axg_5d  axg_5b axg_5b)
  thus ?thesis using axg_5b by fastforce qed*)

(* Relationship between "\<^bold>O\<^sub>a,\<^bold>O\<^sub>p,\<^bold>\<box>\<^sub>a,\<^bold>\<box>\<^sub>p" *)
lemma dC_13_a: "\<lfloor>\<^bold>\<box>\<^sub>a a A \<^bold>\<rightarrow> (\<^bold>\<not>\<^bold>O\<^sub>a a A \<^bold>\<and> \<^bold>\<not>\<^bold>O\<^sub>a a (\<^bold>\<not>A))\<rfloor>" using dC_2 by auto
lemma dC_13_b: "\<lfloor>\<^bold>\<box>\<^sub>p a A \<^bold>\<rightarrow> (\<^bold>\<not>\<^bold>O\<^sub>p a A \<^bold>\<and> \<^bold>\<not>\<^bold>O\<^sub>p a (\<^bold>\<not>A))\<rfloor>" using dC_2 by blast
lemma dC_14_a: "\<lfloor>\<^bold>\<box>\<^sub>a a (A \<^bold>\<leftrightarrow> B) \<^bold>\<rightarrow> (\<^bold>O\<^sub>a a A \<^bold>\<leftrightarrow> \<^bold>O\<^sub>a a B)\<rfloor>" using dC_6 by blast
lemma dC_14_b: "\<lfloor>\<^bold>\<box>\<^sub>p a (A \<^bold>\<leftrightarrow> B) \<^bold>\<rightarrow> (\<^bold>O\<^sub>p a A \<^bold>\<leftrightarrow> \<^bold>O\<^sub>p a B)\<rfloor>" using dC_6 by blast

(* Relationship between "\<^bold>O\<^sub>,\<^bold>O\<^sub>a,\<^bold>O\<^sub>p,\<^bold>\<box>\<^sub>a,\<^bold>\<box>\<^sub>p" *)
lemma dC_15_a: "\<lfloor>(\<^bold>O a \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<box>\<^sub>a a A \<^bold>\<and> \<^bold>\<diamond>\<^sub>a a B \<^bold>\<and> \<^bold>\<diamond>\<^sub>a a (\<^bold>\<not>B)) \<^bold>\<rightarrow> \<^bold>O\<^sub>a a B\<rfloor>" using dC_4 by blast
lemma dC_15_b: "\<lfloor>(\<^bold>O a \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<box>\<^sub>p a A \<^bold>\<and> \<^bold>\<diamond>\<^sub>p a B \<^bold>\<and> \<^bold>\<diamond>\<^sub>p a (\<^bold>\<not>B)) \<^bold>\<rightarrow> \<^bold>O\<^sub>p a B\<rfloor>" using dC_4 by blast

(* Soundness and consistency *)
lemma dII_3_1: "((\<lfloor>\<^bold>O a \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>\<rfloor>) \<and> (\<exists>x. Z(x) \<and> A(x) \<and> B(x))) \<longrightarrow> ob_g a (Z)(A \<^bold>\<rightarrow> B)" 
  proof 
    assume "(\<lfloor>\<^bold>O a \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>\<rfloor>) \<and> (\<exists>x. Z(x) \<and> A(x) \<and> B(x))"
     hence "ob_g a (\<lambda>z. A z \<and> Z z) (\<lambda>z. A z \<and> Z z \<and> B z)" using axg_5e  axg_5b axg_5b axg_5d by smt
     hence "ob_g a (\<lambda>z. Z z \<and> A z) (\<lambda>z. Z z \<and> A z \<and> B z)" using axg_5e  axg_5b axg_5b axg_5d by smt
     hence "ob_g a Z (\<lambda>w. (Z w \<and> \<not>(Z w \<and> A w)) \<or> (Z w \<and> A w \<and> B w))" by (metis (mono_tags) axg_5d) 
     from this show  L19: "ob_g a(Z)(A \<^bold>\<rightarrow> B)" by (smt axg_5b) qed

(* Some theorems and derived (proof) rules *)
lemma dII_4_1: "\<lfloor>\<^bold>\<box>(A \<^bold>\<leftrightarrow> B) \<^bold>\<rightarrow> (C(A) \<^bold>\<leftrightarrow> C(B))\<rfloor>"  using ext by blast
lemma dobs_II_4_1_a  : "\<lfloor>A \<^bold>\<leftrightarrow> B\<rfloor> \<Longrightarrow> \<lfloor>C(A) \<^bold>\<leftrightarrow> C(B)\<rfloor>"  using ext by blast 
lemma dobs_II_4_1_b  : "\<lfloor>A \<^bold>\<leftrightarrow> B\<rfloor> \<Longrightarrow> \<lfloor>(\<^bold>\<diamond>(A \<^bold>\<and> C) \<^bold>\<and> \<^bold>O a \<^bold>\<langle>C\<^bold>|B\<^bold>\<rangle>) \<^bold>\<rightarrow> \<^bold>O a \<^bold>\<langle>C\<^bold>|A\<^bold>\<rangle>\<rfloor>"  by presburger
lemma dobs_II_4_1_c_1: "\<lfloor>\<^bold>\<diamond>(\<^bold>O a \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<box>(\<^bold>O a \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>))\<rfloor>"  by blast
lemma dobs_II_4_1_c_2: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<box>(\<^bold>O a \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>)) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>O a \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>)\<rfloor>"  by auto
lemma dobs_II_4_1_c_3: "\<lfloor>\<^bold>\<diamond>(\<^bold>O a \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>O a \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>)\<rfloor>" by simp
lemma dobs_II_4_1_c_4: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<not>(\<^bold>O a \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<not>(\<^bold>O a \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>))\<rfloor>"  by blast
lemma dres_II_4_1_a_1: "\<lfloor>\<^bold>\<not>(\<^bold>O a \<^bold>\<langle>\<^bold>\<bottom>\<^bold>|A\<^bold>\<rangle>)\<rfloor>"  by (simp add: axg_5a)  
lemma dres_II_4_1_a_2: "\<lfloor>(\<^bold>\<diamond>\<^sub>p a (A \<^bold>\<and> B \<^bold>\<and> C) \<^bold>\<and> \<^bold>O a \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>O a \<^bold>\<langle>C\<^bold>|A\<^bold>\<rangle>) \<^bold>\<rightarrow> \<^bold>O a \<^bold>\<langle>(B \<^bold>\<and> C)\<^bold>|A\<^bold>\<rangle>\<rfloor>"  by (metis dC_3)
lemma dres_II_4_1_a_3: "\<lfloor>\<^bold>O a \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<rightarrow> \<^bold>O a \<^bold>\<langle>B\<^bold>|(A \<^bold>\<and> B)\<^bold>\<rangle>\<rfloor>"  by (smt (verit) dC_2 dC_4)
lemma dres_II_4_1_a_4: "\<lfloor>\<^bold>\<diamond>\<^sub>p a (\<^bold>O a \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle>) \<^bold>\<rightarrow> \<^bold>\<box>\<^sub>p a (\<^bold>O a \<^bold>\<langle>B\<^bold>|(A \<^bold>\<and> B)\<^bold>\<rangle>)\<rfloor>" by (simp add: dres_II_4_1_a_3)
lemma dres_II_4_1_a_5: "\<lfloor>(\<^bold>\<diamond>\<^sub>p a (A \<^bold>\<and> B \<^bold>\<and> C) \<^bold>\<and> \<^bold>O a \<^bold>\<langle>C\<^bold>|A\<^bold>\<rangle>) \<^bold>\<rightarrow> \<^bold>O a \<^bold>\<langle>C\<^bold>|(A \<^bold>\<and> B)\<^bold>\<rangle>\<rfloor>" by (smt (verit) axg_5e)
lemma dres_II_4_1_b_1:  "\<lfloor>A \<^bold>\<leftrightarrow> B\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>O a \<^bold>\<langle>C\<^bold>|A\<^bold>\<rangle> \<^bold>\<leftrightarrow> \<^bold>O a \<^bold>\<langle>C\<^bold>|B\<^bold>\<rangle>\<rfloor>" solve_direct oops
lemma dres_II_4_1_b_2:  "\<lfloor>C \<^bold>\<rightarrow> (A \<^bold>\<leftrightarrow> B)\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>O a \<^bold>\<langle>A\<^bold>|C\<^bold>\<rangle> \<^bold>\<leftrightarrow> \<^bold>O a \<^bold>\<langle>B\<^bold>|C\<^bold>\<rangle>\<rfloor>" using dC_6 by auto
lemma dobs_II_4_2_1: "\<lfloor>(\<^bold>O a \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>a a (A \<^bold>\<and> B) \<^bold>\<and> \<^bold>\<diamond>\<^sub>a a (A \<^bold>\<and> \<^bold>\<not>B)) \<^bold>\<rightarrow> (\<^bold>O a \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>a a (A \<^bold>\<rightarrow> B) \<^bold>\<and> \<^bold>\<diamond>\<^sub>a a (\<^bold>\<not>(A \<^bold>\<rightarrow> B)))\<rfloor>" by auto
(*lemma dobs_II_4_2_2: "\<lfloor>\<^bold>O obd \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<rightarrow> \<^bold>O obd \<^bold>\<langle>(A \<^bold>\<rightarrow> B)\<^bold>|\<^bold>\<top>\<^bold>\<rangle>\<rfloor>" C8*)
lemma dobs_II_4_2_3: "\<lfloor>(\<^bold>O a \<^bold>\<langle>(A \<^bold>\<rightarrow> B)\<^bold>|\<^bold>\<top>\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<box>\<^sub>a a \<^bold>\<top> \<^bold>\<and> \<^bold>\<diamond>\<^sub>a a (A \<^bold>\<rightarrow> B) \<^bold>\<and> \<^bold>\<diamond>\<^sub>a a (\<^bold>\<not>(A \<^bold>\<rightarrow> B))) \<^bold>\<rightarrow> \<^bold>O\<^sub>a a (A \<^bold>\<rightarrow> B)\<rfloor>" solve_direct oops
lemma dobs_II_4_2_4: "\<lfloor>\<^bold>\<box>\<^sub>a a \<^bold>\<top>\<rfloor>" by simp
lemma dobs_II_4_2_5: "\<lfloor>(\<^bold>O a \<^bold>\<langle>(A \<^bold>\<rightarrow> B)\<^bold>|\<^bold>\<top>\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>a a (A \<^bold>\<rightarrow> B) \<^bold>\<and> \<^bold>\<diamond>\<^sub>a a (\<^bold>\<not>(A \<^bold>\<rightarrow> B))) \<^bold>\<rightarrow> \<^bold>O\<^sub>a a (A \<^bold>\<rightarrow> B)\<rfloor>" by (smt (verit, best) dC_4) 
lemma dobs_II_4_2_6: "\<lfloor>(\<^bold>O a \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>a a (A \<^bold>\<and> B) \<^bold>\<and> \<^bold>\<diamond>\<^sub>a a (A \<^bold>\<and> \<^bold>\<not>B)) \<^bold>\<rightarrow> \<^bold>O\<^sub>a a (A \<^bold>\<rightarrow> B)\<rfloor>" by (simp add: dII_3_1)
lemma dobs_II_4_2_6_p: "\<lfloor>(\<^bold>O a \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>p a (A \<^bold>\<and> B) \<^bold>\<and> \<^bold>\<diamond>\<^sub>p a (A \<^bold>\<and> \<^bold>\<not>B)) \<^bold>\<rightarrow> \<^bold>O\<^sub>p a (A \<^bold>\<rightarrow> B)\<rfloor>" by (simp add: dII_3_1)

lemma dOa_C: "\<lfloor>\<^bold>\<diamond>\<^sub>a a (A \<^bold>\<and> B) \<^bold>\<and> \<^bold>O\<^sub>a a A \<^bold>\<and> \<^bold>O\<^sub>a a B \<^bold>\<rightarrow>  \<^bold>O\<^sub>a a (A \<^bold>\<and> B)\<rfloor>" by (metis (full_types) dC_3)
lemma dOp_C: "\<lfloor>\<^bold>\<diamond>\<^sub>p a (A \<^bold>\<and> B) \<^bold>\<and> \<^bold>O\<^sub>p a A \<^bold>\<and> \<^bold>O\<^sub>p a B \<^bold>\<rightarrow>  \<^bold>O\<^sub>p a (A \<^bold>\<and> B)\<rfloor>" by (metis (full_types) dC_3)
lemma dOa_DD: "\<lfloor>(\<^bold>O\<^sub>a a A \<^bold>\<and> \<^bold>O a \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>a a (A \<^bold>\<and> B)) \<^bold>\<rightarrow> \<^bold>O\<^sub>a a (A \<^bold>\<and> B)\<rfloor>" using axg_5b axg_5c dobs_II_4_2_6 by smt 
declare [[smt_timeout=300]]
lemma dOp_DD: "\<lfloor>(\<^bold>O\<^sub>p a A \<^bold>\<and> \<^bold>O a \<^bold>\<langle>B\<^bold>|A\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>p a (A \<^bold>\<and> B)) \<^bold>\<rightarrow> \<^bold>O\<^sub>p a (A \<^bold>\<and> B)\<rfloor>" using axg_5b axg_5c dobs_II_4_2_6_p by smt

end
