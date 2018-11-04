theory RegExpInterface
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
   where "\<lbrakk>A\<rbrakk> \<equiv>  A || One"
                   
value "Star (Conc(Alt (Atom(CHR ''a'')) (Atom(CHR ''b''))) (Atom(CHR ''c'')))"
text{* or better equivalently: *}
value "\<lbrace>(\<lfloor>CHR ''a''\<rfloor> || \<lfloor>CHR ''b''\<rfloor>) ~~ \<lfloor>CHR ''c''\<rfloor>\<rbrace>\<^sup>*"

section{* Definition of a semantic function: the ``language'' of the regular expression *}
text\<open> This is just a reminder - already defined in @{theory Regular_Exp} as @{term lang}.\<close>

text{* In the following, we give a semantics for our regular expressions, which so far have
just been a term language (i.e. abstract syntax). The semantics is a ``denotational semantics'',
i.e. we give a direct meaning for regular expressions in some universe of ``denotations''. 

This universe of denotations is in our concrete case: *}

definition enabled :: "('a,'\<sigma> set)da  \<Rightarrow> '\<sigma> set \<Rightarrow> 'a list \<Rightarrow>  'a list" 
  where   "enabled A \<sigma> = filter (\<lambda>x. next A x \<sigma> \<noteq> {}) "

text{* Now the denotational semantics for regular expression can be defined on a post-card: *}

fun              L :: "'a rexp => 'a lang"
  where L_Emp :   "L Zero        = {}"
       |L_One:    "L One         = {[]}"
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


definition XX where "XX = (rexp2na example_expression)"
definition YY where "YY = na2da(rexp2na example_expression)"
(* reminder from execute *)
value "NA.accepts (rexp2na example_expression) [0,1,1,0,0,1]"
value "DA.accepts (na2da (rexp2na example_expression)) [0,1,1,0,0,1]"

definition zero where "zero = (0::nat)"
definition one where "one = (1::nat)"

typ "'a set"


export_code  zero one Suc Int.nat  nat_of_integer int_of_integer  
             Zero One     Atom     Plus  Times  Star      
             rexp2na      na2da    enabled
             NA.accepts   DA.accepts  

             example_expression

             in SML
                                 
      
      module_name RegExpChecker file "RegExpChecker.sml"

SML_file "RegExpChecker.sml"

ML\<open> 
use "RegExpChecker.sml";

structure RegExpInterface : sig
    type automaton
    type env 
    val  alphabet: term list -> env
    val  conv    : term -> env -> int RegExpChecker.rexp (* for debugging *)
    val  rexp_term2da: term  -> env -> automaton
    val  enabled : automaton -> env -> string list
    val  next    : automaton -> env -> string -> automaton
    val  final   : automaton -> bool
    val  accepts : automaton -> env -> string list -> bool
  end
 =
struct
local open RegExpChecker in

  type state = bool list RegExpChecker.set
  type env = string list

  type automaton = state * ((Int.int -> state -> state) * (state -> bool))

  val add_atom = fold_aterms (fn Const(c as(_,Type(@{type_name "rexp"},_)))=> insert (op=) c |_=>I);
  fun alphabet termS  =  rev(map fst (fold add_atom termS []));

  fun conv (Const(@{const_name "Regular_Exp.rexp.Zero"},_)) _ = Zero
     |conv (Const(@{const_name "Regular_Exp.rexp.One"},_)) _ = Onea 
     |conv (Const(@{const_name "Regular_Exp.rexp.Times"},_) $ X $ Y) env = Times(conv X env, conv Y env)
     |conv (Const(@{const_name "Regular_Exp.rexp.Plus"},_) $ X $ Y) env = Plus(conv X env, conv Y env)
     |conv (Const(@{const_name "Regular_Exp.rexp.Star"},_) $ X) env = Star(conv X env)
     |conv (Const(@{const_name "RegExpInterface.opt"},_) $ X) env = Plus(conv X env, Onea)
     |conv (Const(@{const_name "RegExpInterface.rep1"},_) $ X) env = Times(conv X env, Star(conv X env))
     |conv (Const (s, Type(@{type_name "rexp"},_))) env = 
               let val n = find_index (fn x => x = s) env 
                   val _ = if n<0 then error"conversion error of regexp."  else ()
               in  Atom(n) end
     |conv S _ = error("conversion error of regexp:" ^ (Syntax.string_of_term (@{context})S))

   val eq_int = {equal = curry(op =) : Int.int -> Int.int -> bool};
   val eq_bool_list = {equal = curry(op =) : bool list  -> bool list  -> bool};

   fun rexp_term2da term env = let val rexp = conv term env;
                                   val nda = RegExpChecker.rexp2na eq_int rexp;
                                   val da = RegExpChecker.na2da eq_bool_list nda;
                               in  da end;


   (* here comes the main interface of the module: 
      - "enabled" gives the part of the alphabet "env" for which the automatan does not
        go into a final state
      - next provides an automata transformation that produces an automaton that
        recognizes the rest of a word after a *)
   fun enabled (da as (state,(_,_))) env  = 
                              let val inds = RegExpChecker.enabled da state (0 upto (length env - 1))
                              in  map (fn i => nth env i) inds end

   fun next  (current_state, (step,fin)) env a =
                              let val index = find_index (fn x => x = a) env   
                              in  if index < 0 then error"undefined id for monitor"
                                  else (step index current_state,(step,fin))
                              end

   fun final (current_state, (_,fin)) = fin current_state

   fun accepts da env word = let fun index a = find_index (fn x => x = a) env   
                                 val indexL = map index word
                                 val _ = if forall (fn x => x >= 0) indexL then ()
                                         else error"undefined id for monitor"
                             in  RegExpChecker.accepts da indexL end

end; (* local *)
end  (* struct *)
\<close>


no_notation Atom ("\<lfloor>_\<rfloor>")  


end
