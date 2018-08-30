theory RegExp
imports Main 
begin

datatype 'a rexp = Empty                         ("<>")
                 | Atom 'a                       ("\<lfloor>_\<rfloor>" 65)
                 | Alt  "('a rexp)" "('a rexp)"  (infixr "||" 55)
                 | Conc "('a rexp)" "('a rexp)"  (infixr "~~" 60)
                 | Star "('a rexp)"              ("\<lbrace>(_)\<rbrace>\<^sup>*" [0]100)          

definition rep1 :: "'a rexp \<Rightarrow> 'a rexp" ("\<lbrace>(_)\<rbrace>\<^sup>+")
  where "\<lbrace>A\<rbrace>\<^sup>+ \<equiv>  A ~~ \<lbrace>A\<rbrace>\<^sup>*"
    
definition opt :: "'a rexp \<Rightarrow> 'a rexp" ("\<lbrakk>(_)\<rbrakk>")
   where "\<lbrakk>A\<rbrakk> \<equiv>  A || <>"
                   
value "Star (Conc(Alt (Atom(CHR ''a'')) (Atom(CHR ''b''))) (Atom(CHR ''c'')))"
text{* or better equivalently: *}
value "\<lbrace>(\<lfloor>CHR ''a''\<rfloor> || \<lfloor>CHR ''b''\<rfloor>) ~~ \<lfloor>CHR ''c''\<rfloor>\<rbrace>\<^sup>*"


section{* Definition of a semantic function: the ``language'' of the regular expression *}

text{* In the following, we give a semantics for our regular expressions, which so far have
just been a term language (i.e. abstract syntax). The semantics is a ``denotational semantics'',
i.e. we give a direct meaning for regular expressions in some universe of ``denotations''. 

This universe of denotations is in our concrete case: *}

type_synonym 'a lang = "'a list set"

inductive_set star :: "'a lang \<Rightarrow> 'a lang"
              for A:: "'a lang"
where   NilI  : "[] \<in> star A"
     |  ConsI : "[| a\<in>A; as \<in> star A |] ==> a@as \<in> star A"


lemma NilI : "[] \<in> star A"
by(rule NilI)


lemma ConsI : "a\<in>A \<Longrightarrow>  as \<in> star A \<Longrightarrow>  a@as \<in> star A"
apply(rule ConsI)
apply(assumption)
by(assumption)

lemma epsilonExists: "star {[]} = {[]}"
apply(rule Set.set_eqI)
apply(rule iffI)
apply(erule star.induct)
apply(auto intro: NilI )
done

lemma epsilonAlt: "star {} = {[]}"
apply(rule Set.set_eqI)
apply(rule iffI)
apply(erule star.induct, simp,simp)
apply(auto intro: NilI )
done




text{* ... and of course, we have the consequence : *}

lemma epsilon': "star (star {[]}) = {[]}"
by(simp add: epsilonExists)

lemma epsilon'': "star (star ((star {[]}))) = {[]}"
by(simp add: epsilonExists)



text{* Now the denotational semantics for regular expression can be defined on a post-card: *}

fun              L :: "'a rexp => 'a lang"
where L_Emp :   "L Empty      = {}"
     |L_Atom:   "L (\<lfloor>a\<rfloor>)      = {[a]}"
     |L_Un:     "L (el || er)  = (L el) \<union> (L er)"
     |L_Conc:   "L (el ~~ er)  = {xs@ys | xs ys. xs \<in> L el \<and> ys \<in> L er}"
     |L_Star:   "L (Star e)   = star(L e)"


fun              L\<^sub>s\<^sub>u\<^sub>b :: "'a::order rexp => 'a lang"
where L\<^sub>s\<^sub>u\<^sub>b_Emp :   "L\<^sub>s\<^sub>u\<^sub>b Empty       = {}"
     |L\<^sub>s\<^sub>u\<^sub>b_Atom:   "L\<^sub>s\<^sub>u\<^sub>b (\<lfloor>a\<rfloor>)       = {z . \<forall>x. x \<le> a \<and> z=[x]}"
     |L\<^sub>s\<^sub>u\<^sub>b_Un:     "L\<^sub>s\<^sub>u\<^sub>b (el || er)  = (L\<^sub>s\<^sub>u\<^sub>b el) \<union> (L\<^sub>s\<^sub>u\<^sub>b er)"
     |L\<^sub>s\<^sub>u\<^sub>b_Conc:   "L\<^sub>s\<^sub>u\<^sub>b (el ~~ er)  = {xs@ys | xs ys. xs \<in> L\<^sub>s\<^sub>u\<^sub>b el \<and> ys \<in> L\<^sub>s\<^sub>u\<^sub>b er}"
     |L\<^sub>s\<^sub>u\<^sub>b_Star:   "L\<^sub>s\<^sub>u\<^sub>b (Star e)    = star(L\<^sub>s\<^sub>u\<^sub>b e)"


schematic_goal WeCompute: "L(Star ((\<lfloor>CHR ''a''\<rfloor> || \<lfloor>CHR ''b''\<rfloor>) ~~ \<lfloor>CHR ''c''\<rfloor>)) = ?X"
by simp

thm WeCompute


text{* Well, an attempt to evaluate this turns out not to work too well ... *} 


text{* Now let's reconsider our `obvious lemma' from above, this time by stating that
       the alternative-operator produces \emph{semantically} equivalent ewpressions. *}  



lemma alt_commute' : "L((A::'a rexp) || B) = L(B || A)"  
by auto


lemma mt_seq' : "L(Empty ~~ Empty) = {}"
by simp


lemma eps : "L (Star Empty) = {[]}"
by (simp add: epsilonAlt)

  
no_notation Atom ("\<lfloor>_\<rfloor>")  


end
