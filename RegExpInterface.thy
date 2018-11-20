chapter\<open>The High-Level Interface to the Automata-Library\<close>

theory RegExpInterface
imports "Functional-Automata.Execute"
begin

text\<open> The implementation of the monitoring concept follows the following design decisions:
\<^enum> We re-use generated code from the AFP submissions @{theory Regular_Set} and 
  @{theory Automata}, converted by the code-generator into executable SML code
  (ports to future Isabelle versions should just reuse future versions of these)
\<^enum> Monitor-Expressions are regular expressions (in some adapted syntax) 
  over Document Class identifiers; they denote the language of all possible document object
  instances belonging to these classes
\<^enum> Instead of expanding the sub-class relation (and building the product automaton of all 
  monitor expressions), we convert the monitor expressions into automata over class-id's
  executed in parallel, in order to avoid blowup.
\<^enum> For efficiency reasons, the class-ids were internally abstracted to integers; the
  encoding table is called environment \<^verbatim>\<open>env\<close>.
\<^enum> For reusability reasons, we did NOT abstract the internal state representation in the
  deterministic automata construction (lists of lists of bits - sic !) by replacing them
  by unique keys via a suitable coding-table; rather, we opted for keeping the automatas small
  (no products, no subclass-expansion).
\<close>

section\<open>Monitor Syntax over RegExp - constructs\<close>

notation Star  ("\<lbrace>(_)\<rbrace>\<^sup>*" [0]100)
notation Plus  (infixr "||" 55)
notation Times (infixr "~~" 60)
notation Atom  ("\<lfloor>_\<rfloor>" 65)

definition rep1 :: "'a rexp \<Rightarrow> 'a rexp" ("\<lbrace>(_)\<rbrace>\<^sup>+")
  where "\<lbrace>A\<rbrace>\<^sup>+ \<equiv>  A ~~ \<lbrace>A\<rbrace>\<^sup>*"
    
definition opt :: "'a rexp \<Rightarrow> 'a rexp" ("\<lbrakk>(_)\<rbrakk>")
   where "\<lbrakk>A\<rbrakk> \<equiv>  A || One"
                   
value "Star (Conc(Alt (Atom(CHR ''a'')) (Atom(CHR ''b''))) (Atom(CHR ''c'')))"
text{* or better equivalently: *}
value "\<lbrace>(\<lfloor>CHR ''a''\<rfloor> || \<lfloor>CHR ''b''\<rfloor>) ~~ \<lfloor>CHR ''c''\<rfloor>\<rbrace>\<^sup>*"

section{* Some Standard and Derived Semantics *}
text\<open> This is just a reminder - already defined in @{theory Regular_Exp} as @{term lang}.\<close>

text{* In the following, we give a semantics for our regular expressions, which so far have
just been a term language (i.e. abstract syntax). The semantics is a ``denotational semantics'',
i.e. we give a direct meaning for regular expressions in some universe of ``denotations''. 

This universe of denotations is in our concrete case: *}

text{* Now the denotational semantics for regular expression can be defined on a post-card: *}

fun       L :: "'a rexp => 'a lang"
  where   L_Emp :   "L Zero        = {}"
         |L_One:    "L One         = {[]}"
         |L_Atom:   "L (\<lfloor>a\<rfloor>)       = {[a]}"
         |L_Un:     "L (el || er)  = (L el) \<union> (L er)"
         |L_Conc:   "L (el ~~ er)  = {xs@ys | xs ys. xs \<in> L el \<and> ys \<in> L er}"
         |L_Star:   "L (Star e)    = Regular_Set.star(L e)"


text\<open>A more useful definition is the sub-language - definition\<close>
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


section\<open>HOL - Adaptions and Export to SML\<close>

definition enabled :: "('a,'\<sigma> set)da  \<Rightarrow> '\<sigma> set \<Rightarrow> 'a list \<Rightarrow>  'a list" 
  where   "enabled A \<sigma> = filter (\<lambda>x. next A x \<sigma> \<noteq> {}) "


definition zero where "zero = (0::nat)"
definition one where "one = (1::nat)"


export_code  zero one Suc Int.nat  nat_of_integer int_of_integer  (* for debugging *)
             example_expression                                   (* for debugging *)

             Zero One     Atom     Plus  Times  Star              (* regexp abstract syntax *)

             rexp2na      na2da    enabled                        (* low-level automata interface *)
             NA.accepts   DA.accepts  

             in SML  module_name RegExpChecker 
                     file "RegExpChecker.sml"                     (* writing it to a file *)
                                                                  
(* potentially susceptible to race conditions ... *)                                                                 
SML_file "RegExpChecker.sml"                                      (* reads and eval generated file  
                                                                     into SML toplevel  *)
SML_export \<open>structure RegExpChecker = RegExpChecker\<close>              (* copies from SML toplevel into 
                                                                     Isabelle/ML toplevel *)

section\<open>The Abstract Interface For Monitor Expressions\<close>
text\<open>Here comes the hic : The reflection of the HOL-Automata module into an SML module 
with an abstract interface hiding some generation artefacts like the internal states 
of the deterministic automata ...\<close>

ML\<open> 

structure RegExpInterface : sig
    type automaton
    type env 
    type cid
    val  alphabet    : term list -> env
    val  ext_alphabet: env -> term list -> env
    val  conv        : term -> env -> int RegExpChecker.rexp (* for debugging *)
    val  rexp_term2da: env -> term -> automaton
    val  enabled     : automaton -> env -> cid list  
    val  next        : automaton -> env -> cid -> automaton
    val  final       : automaton -> bool
    val  accepts     : automaton -> env -> cid list -> bool
  end
 =
struct
local open RegExpChecker in

  type state = bool list RegExpChecker.set
  type env = string list
  type cid = string

  type automaton = state * ((Int.int -> state -> state) * (state -> bool))

  val add_atom = fold_aterms (fn Const(c as(_,Type(@{type_name "rexp"},_)))=> insert (op=) c |_=>I);
  fun alphabet termS  =  rev(map fst (fold add_atom termS []));
  fun ext_alphabet env termS  =  
         let val res = rev(map fst (fold add_atom termS [])) @ env;
             val _ = if has_duplicates  (op=) res
                     then error("reject and accept alphabets must be disjoint!")
                     else ()
         in res end;

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

   fun rexp_term2da env term = let val rexp = conv term env;
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
