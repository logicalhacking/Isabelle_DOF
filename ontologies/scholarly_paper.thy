section{* An example ontology for a scholarly paper*}

theory scholarly_paper
   imports "../Isa_COL"
begin

doc_class title =
   short_title :: "string option"  <=  "None"
    
doc_class subtitle =
   abbrev :: "string option"       <=  "None"
   
-- \<open>adding a contribution list and checking that it is cited as well in tech as in conclusion. ? \<close>

doc_class author =
   email       :: "string"
   orcid       :: "string"
   affiliation :: "string"

doc_class abstract =
   keywordlist        :: "string list"   <= "[]" 
   principal_theorems :: "thm list"

doc_class text_section = 
   main_author :: "author option"  <=  None
   fixme_list  :: "string list"    <=  "[]" 
   
doc_class introduction = text_section +
   comment :: string
   claims  :: "thm list"

doc_class technical = text_section +
   definition_list :: "string list" <=  "[]"
   formal_results  :: "thm list"
   
text{* A very rough formatting style could be modeled as follows:*}   

   
doc_class example    = text_section +
   comment :: "string"

doc_class "conclusion" = text_section +
   main_author :: "author option"  <=  None
   
doc_class related_work = "conclusion" +
   main_author :: "author option"  <=  None

doc_class bibliography =
   style :: "string option"  <=  "Some ''LNCS''"

text\<open> Besides subtyping, there is another relation between
doc_classes: a class can be a \<^emph>\<open>monitor\<close> to other ones,
which is expressed by occurrence in the where clause.
While sub-classing refers to data-inheritance of attributes,
a monitor captures structural constraints -- the order --
in which instances of monitored classes may occur.

The control of monitors is done by the commands:
\<^item> \<^verbatim>\<open> monitor <oid::class_type, <attributes-defs> > \<close>
\<^item> \<^verbatim>\<open> close_monitor <oid[::class_type],<attributes-updates>> \<close>

where the automaton of the monitor class is expected
to be in a final state.

Monitors can be nested.

Classes neither directly or  indirectly (via inheritance)
mentioned in the monitor clause are \<^emph>\<open>independent\<close> from
the monitor and may occur freely, \ie{} in arbitrary order.n \<close>


text \<open>underlying idea: a monitor class automatically receives a  
    \<^verbatim>\<open>trace\<close> attribute in which a list of observed class-ids is maintained.
    The \<^verbatim>\<open>trace\<close> is a \<^emph>\<open>`predefined id`\<close> like \<^verbatim>\<open>main\<close> in C. It can be accessed
    like any other attribute of a class instance, \ie{} a document item.\<close>

doc_class article = 
   style_id :: string                <= "''LNCS''"
   version  :: "(int \<times> int \<times> int)"  <= "(0,0,0)"
   where "(title       ~~ 
           \<lbrakk>subtitle\<rbrakk>   ~~
           \<lbrace>author\<rbrace>\<^sup>+   ~~ 
           abstract     ~~
           introduction ~~ 
           \<lbrace>technical || example\<rbrace>\<^sup>+ ~~ 
           conclusion   ~~  
           bibliography)"

gen_sty_template


ML\<open>
val term = @{term "(title       ~~ 
                   \<lbrakk>subtitle\<rbrakk>    ~~
                   \<lbrace>author\<rbrace>\<^sup>+     ~~ 
                   abstract     ~~
                   introduction ~~ 
                   \<lbrace>technical || example\<rbrace>\<^sup>+ ~~ 
                   conclusion   ~~  
                   bibliography)"}

\<close>


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
     |conv (Const (s, @{typ "doc_class rexp"})) env = 
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
ML\<open>
val alpha = (RegExpInterface.alphabet [term]);
val DA as (init,(next,fin)) = RegExpInterface.rexp_term2da term (RegExpInterface.alphabet [term]) ;
RegExpChecker.accepts DA [0,2,3,4,5,6,7,8];


val S0 = init
val E1 = RegExpChecker.enabled DA S0 [0,1,2,3,4,5,6,7,8];
val S1 = next 0 init;
val E2 = RegExpChecker.enabled DA S1 [0,1,2,3,4,5,6,7,8];
val S2 = next 2 S1; (* uffz. it works. *)
val E3 = RegExpChecker.enabled DA S2 [0,1,2,3,4,5,6,7,8];
val S3 = next 3 S2; (* uffz. it works. *)
\<close>

ML\<open>
RegExpInterface.enabled DA alpha;
val DA' = RegExpInterface.next DA alpha "scholarly_paper.title";
RegExpInterface.enabled DA' alpha;
val DA'' = RegExpInterface.next DA' alpha "scholarly_paper.author";
RegExpInterface.enabled DA'' alpha;
\<close>

end

