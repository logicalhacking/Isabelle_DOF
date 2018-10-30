theory RegExp
imports "Functional-Automata.Execute"
begin

term Atom
value "Star (Times(Plus (Atom(CHR ''a'')) (Atom(CHR ''b''))) (Atom(CHR ''c'')))"

notation Star  ("\<lbrace>(_)\<rbrace>\<^sup>*" [0]100)
notation Plus  (infixr "||" 55)
notation Times (infixr "~~" 60)
notation Atom  ("\<lfloor>_\<rfloor>" 65)

(*
datatype 'a rexp = Empty                         ("<>")
                 | Atom 'a                       ("\<lfloor>_\<rfloor>" 65)
                 | Alt  "('a rexp)" "('a rexp)"  (infixr "||" 55)
                 | Conc "('a rexp)" "('a rexp)"  (infixr "~~" 60)
                 | Star "('a rexp)"              ("\<lbrace>(_)\<rbrace>\<^sup>*" [0]100)          
*)

definition rep1 :: "'a rexp \<Rightarrow> 'a rexp" ("\<lbrace>(_)\<rbrace>\<^sup>+")
  where "\<lbrace>A\<rbrace>\<^sup>+ \<equiv>  A ~~ \<lbrace>A\<rbrace>\<^sup>*"
    
definition opt :: "'a rexp \<Rightarrow> 'a rexp" ("\<lbrakk>(_)\<rbrakk>")
   where "\<lbrakk>A\<rbrakk> \<equiv>  A || Zero"
                   
value "Star (Conc(Alt (Atom(CHR ''a'')) (Atom(CHR ''b''))) (Atom(CHR ''c'')))"
text{* or better equivalently: *}
value "\<lbrace>(\<lfloor>CHR ''a''\<rfloor> || \<lfloor>CHR ''b''\<rfloor>) ~~ \<lfloor>CHR ''c''\<rfloor>\<rbrace>\<^sup>*"

section{* Definition of a semantic function: the ``language'' of the regular expression *}
text\<open> This is just a reminder - already defined in @{theory Regular_Exp} as @{term lang}.\<close>

text{* In the following, we give a semantics for our regular expressions, which so far have
just been a term language (i.e. abstract syntax). The semantics is a ``denotational semantics'',
i.e. we give a direct meaning for regular expressions in some universe of ``denotations''. 

This universe of denotations is in our concrete case: *}


text{* Now the denotational semantics for regular expression can be defined on a post-card: *}

fun              L :: "'a rexp => 'a lang"
  where L_Emp :   "L Zero        = {}"
       |L_One:    "L One = {[]}"
       |L_Atom:   "L (\<lfloor>a\<rfloor>)       = {[a]}"
       |L_Un:     "L (el || er)  = (L el) \<union> (L er)"
       |L_Conc:   "L (el ~~ er)  = {xs@ys | xs ys. xs \<in> L el \<and> ys \<in> L er}"
       |L_Star:   "L (Star e)    = Regular_Set.star(L e)"


text\<open>A more useful definition is the \<close>
fun       L\<^sub>s\<^sub>u\<^sub>b :: "'a::order rexp => 'a lang"
  where   L\<^sub>s\<^sub>u\<^sub>b_Emp:    "L\<^sub>s\<^sub>u\<^sub>b Zero        = {}"
         |L\<^sub>s\<^sub>u\<^sub>b_One:    "L\<^sub>s\<^sub>u\<^sub>b One         = {[]}"
         |L\<^sub>s\<^sub>u\<^sub>b_Atom:   "L\<^sub>s\<^sub>u\<^sub>b (\<lfloor>a\<rfloor>)       = {z . \<forall>x. x \<le> a \<and> z=[x]}"
         |L\<^sub>s\<^sub>u\<^sub>b_Un:     "L\<^sub>s\<^sub>u\<^sub>b (el || er)  = (L\<^sub>s\<^sub>u\<^sub>b el) \<union> (L\<^sub>s\<^sub>u\<^sub>b er)"
         |L\<^sub>s\<^sub>u\<^sub>b_Conc:   "L\<^sub>s\<^sub>u\<^sub>b (el ~~ er)  = {xs@ys | xs ys. xs \<in> L\<^sub>s\<^sub>u\<^sub>b el \<and> ys \<in> L\<^sub>s\<^sub>u\<^sub>b er}"
         |L\<^sub>s\<^sub>u\<^sub>b_Star:   "L\<^sub>s\<^sub>u\<^sub>b (Star e)    = Regular_Set.star(L\<^sub>s\<^sub>u\<^sub>b e)"

(* reminder from execute *)
value "NA.accepts (rexp2na example_expression) [0,1,1,0,0,1]"

value "DA.accepts (na2da (rexp2na example_expression)) [0,1,1,0,0,1]"
  
no_notation Atom ("\<lfloor>_\<rfloor>")  


end
