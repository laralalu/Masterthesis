theory "high-risk-3-3-26-SDL"
  imports 
  SDL_agents
begin

(*agent b = importers*)

(*DDL structure*)
consts 
l::aiSys
system_in_conformity::"aiSys\<Rightarrow>\<sigma>"
not_on_market::"aiSys\<Rightarrow>\<sigma>"

axiomatization where
F1: "\<lfloor>\<^bold>\<forall>x::aiSys. \<^bold>\<circle>b<stit b (system_in_conformity x)>\<rfloor>" and 
A1: "\<lfloor>\<^bold>\<forall>x::aiSys. \<^bold>\<not>(stit b (system_in_conformity x)) \<^bold>\<rightarrow> \<^bold>\<circle>b<(stit b (not_on_market x))>\<rfloor>" and
(*implicit: If the system is in conformity, the importer is obligated to not see to it that the system is not placed
on the market*)
A2: "\<lfloor>\<^bold>\<forall>x::aiSys. \<^bold>\<circle>b<(stit b (system_in_conformity x)) \<^bold>\<rightarrow> (\<^bold>\<not>(stit b (not_on_market x)))>\<rfloor>" and
Situation: "\<lfloor>\<^bold>\<not>(stit b (system_in_conformity l))\<rfloor>\<^sub>l"

(***Some Experiments***) 
lemma True nitpick [satisfy, user_axioms] oops (*Consistency-check: Nitpick finds no model*)
lemma False using A1 A2 F1 Situation serialityb by blast 

(*both can be proven \<rightarrow> contradiction*)
lemma "\<lfloor>\<^bold>\<circle>b<(stit b (not_on_market l))>\<rfloor>\<^sub>l" using A1 Situation by auto
lemma "\<lfloor>\<^bold>\<circle>b<\<^bold>\<not>(stit b (not_on_market l))>\<rfloor>\<^sub>l" using F1 A2 by blast

(*Notes:
- timely dimension cannot be expressed
- ideally, a stit operator with meaning would be needed*)
end