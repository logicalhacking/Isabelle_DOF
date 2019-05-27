(*<*)
theory MyCommentedIsabelle
(*  imports "Isabelle_DOF.technical_report" *)
  imports "../../../ontologies/technical_report"
begin
 

open_monitor*[this::report] 
(*>*)

title*[tit::title]\<open>An Account with my Personal, Ecclectic Comments on the Isabelle Architecture\<close> 
subtitle*[stit::subtitle]\<open>Version : Isabelle 2017\<close>
text*[bu::author,     
      email       = "''wolff@lri.fr''",
      affiliation = "''Universit\\'e Paris-Saclay, Paris, France''"]\<open>Burkhart Wolff\<close>
    

text*[abs::abstract,
      keywordlist="[''LCF-Architecture'',''Isabelle'',''SML'',''PIDE'',''Tactic Programming'']"]\<open>
While Isabelle is mostly known as part of Isabelle/HOL (an interactive 
theorem prover), it actually provides a system framework for developing a wide
spectrum of applications. A particular strength of the Isabelle framework is the 
combination of text editing, formal verification, and code generation. 

This is a programming-tutorial of Isabelle and Isabelle/HOL, a complementary
text to the unfortunately somewhat outdated "The Isabelle Cookbook" in
\url{https://nms.kcl.ac.uk/christian.urban/Cookbook/}. The reader is encouraged
not only to consider the generated .pdf, but also consult the loadable version in Isabelle/jedit
in order to make experiments on the running code. 

This text is written itself in Isabelle/Isar using a specific document ontology
for technical reports. It is intended to be a "living document", i.e. it is not only
used for generating a static, conventional .pdf, but also for direct interactive 
exploration in Isabelle/jedit. This way, types, intermediate results of computations and
checks can be repeated by the reader who is invited to interact with this document.
Moreover, the textual parts have been enriched with a maximum of formal content
which makes this text re-checkable at each load and easier maintainable.
\<close>

chapter*[intro::introduction]\<open> Introduction  \<close>    


chapter*[t1::technical]\<open> SML and Fundamental SML libraries  \<close>    

section*[t11::technical] "ML, Text and Antiquotations"

text\<open>Isabelle is written in SML, the "Standard Meta-Language", which is
is an impure functional programming language allowing, in principle, mutable variables and side-effects. 
The following Isabelle/Isar commands allow for accessing the underlying SML interpreter
of Isabelle directly. In the example, a mutable variable X is declared, defined to 0 and updated; 
and finally re-evaluated leading to output: \<close>

ML\<open> val X = Unsynchronized.ref 0;
    X:= !X + 1;
    X
  \<close>

text\<open>However, since Isabelle is a platform involving parallel execution, concurrent computing, and,
as an interactive environment, involves backtracking / re-evaluation as a consequence of user-
interaction, imperative programming is discouraged and nearly never used in the entire Isabelle
code-base. The preferred programming style is purely functional: \<close>

ML\<open> fun fac x = if x = 0 then 1 else x * fac(x-1) ;
    fac 10;
  \<close>
(* or *) 
ML\<open> type state = {  a : int,   b : string}
    fun incr_state ({a, b}:state) =  {a=a+1, b=b}
  \<close>

text\<open> The faculty function is defined and executed; the (sub)-interpreter in Isar
works in the conventional read-execute-print loop for each statement separated by a ";".
Functions, types, data-types etc. can be grouped to modules (called \<^emph>\<open>structures\<close>) which can
be constrained to interfaces (called \<^emph>\<open>signatures\<close>) and even be parametric structures
(called \<^emph>\<open>functors\<close>). \<close>

text\<open> The Isabelle/Isar interpreter (called \<^emph>\<open>toplevel\<close> ) is extensible; by a mixture of SML
and Isar-commands, domain-specific components can be developed and integrated into the system 
on the fly. Actually, the Isabelle system code-base consists mainly of SML and \<^verbatim>\<open>.thy\<close>-files 
containing such mixtures of Isar commands and SML. \<close>

text\<open> Besides the ML-command used in the above examples, there are a number of commands 
representing text-elements in Isabelle/Isar; text commands can be interleaved arbitraryly
with other commands. Text in text-commands may use LaTeX and is used for type-setting 
documentations in a kind of literate programming style. \<close>

text\<open>So: the text command for:\<close>

text\<open>\<^emph>\<open>This is a text.\<close>\<close>

text\<open>... is represented in an \<^verbatim>\<open>.thy\<close> file by:\<close>

text\<open>\verb+text\<open>\<^emph>\<open>This is a text.\<close>\<close>+\<close>

text\<open>and desplayed in the Isabelle/jedit front-end at the sceen by:\<close>

figure*[fig2::figure, relative_width="100",src="''figures/text-element''"]
        \<open>A text-element as presented in Isabelle/jedit. \<close>

text\<open> text-commands, ML- commands (and in principle any other command) can be seen as 
\<^emph>\<open>quotations\<close> over the underlying SML environment (similar to OCaml or Haskell).
Linking these different sorts of quotations with each other and the underlying SML-envirnment
is supported via \<^emph>\<open>antiquotations\<close>'s. Generally speaking, antiquotations are a programming technique 
to specify expressions or patterns in a quotation, parsed in the context of the enclosing expression 
or pattern where the quotation is.

The way an antiquotation is specified depends on the quotation expander: typically a specific 
character and an identifier, or specific parentheses and a complete expression or pattern.\<close>

text\<open> In Isabelle documentations, antiquotation's were heavily used to enrich literate explanations
and documentations by "formal content", i.e. machine-checked, typed references
to all sorts of entities in the context of the interpreting environment. 
Formal content allows for coping with sources that rapidly evolve and were developed by 
distributed teams as is typical in open-source developments. 
A paradigmatic example for antiquotation in Texts and Program snippets is here:
\<close>

text\<open> @{footnote \<open>sdf\<close>}, @{file "$ISABELLE_HOME/src/Pure/ROOT.ML"}\<close> 
ML\<open>    val x = @{thm refl};
       val y = @{term "A \<longrightarrow> B"}
       val y = @{typ  "'a list"}
  \<close>

text\<open>... which we will describe in more detail later. \<close> 

text\<open>In a way, literate specification attempting to maximize its formal content is a way to
ensure "Agile Development" in a (theory)-document development, at least for its objectives, 
albeit not for its popular methods and processes like SCRUM. \<close>

paragraph\<open>
     A maximum of formal content inside text documentation also ensures the 
     consistency of this present text with the underlying Isabelle version.\<close>

section\<open>The Isabelle/Pure bootstrap\<close>

text\<open>It is instructive to study the fundamental bootstrapping sequence of the Isabelle system;
     it is written in the Isar format and gives an idea of the global module dependencies: 
     @{file "$ISABELLE_HOME/src/Pure/ROOT.ML"}. Loading this file 
     (for example by hovering over this hyperlink in the antiquotation holding control or
     command key in Isabelle/jedit and activating it) allows the Isabelle IDE 
     to support hyperlinking \<^emph>\<open>inside\<close> the Isabelle source.\<close>

text\<open>The bootstrapping sequence is also reflected in the following diagram: \<close>

figure*[architecture::figure,relative_width="100",src="''figures/isabelle-architecture''"]\<open> 
     The system architecture of Isabelle (left-hand side) and the 
     asynchronous communication between the Isabelle system and 
     the IDE (right-hand side). \<close>


section*[t12::technical] "Elements of the SML library";  
text\<open>Elements of the @{file "$ISABELLE_HOME/src/Pure/General/basics.ML"} SML library
are basic exceptions. Note that exceptions should be catched individually, uncatched exceptions 
except those generated by the specific "error" function are discouraged in Isabelle
source programming since they might produce races. Finally, a number of commonly
used "squigglish" combinators is listed:
\<close>
ML\<open>
 Bind      : exn;
 Chr       : exn;
 Div       : exn;
 Domain    : exn;
 Fail      : string -> exn;
 Match     : exn;
 Overflow  : exn;
 Size      : exn;
 Span      : exn;
 Subscript : exn;

 exnName : exn -> string ; (* -- very interesting to query an unknown exception  *)
 exnMessage : exn -> string ;
\<close>

ML\<open>
op ! : 'a Unsynchronized.ref -> 'a;
op := : ('a Unsynchronized.ref * 'a) -> unit;

op #> :  ('a -> 'b) * ('b -> 'c) -> 'a -> 'c; (* reversed function composition *)
op o : (('b -> 'c) * ('a -> 'b)) -> 'a -> 'c;
op |-- : ('a -> 'b * 'c) * ('c -> 'd * 'e) -> 'a -> 'd * 'e;
op --| : ('a -> 'b * 'c) * ('c -> 'd * 'e) -> 'a -> 'b * 'e;
op -- : ('a -> 'b * 'c) * ('c -> 'd * 'e) -> 'a -> ('b * 'd) * 'e;
op ? : bool * ('a -> 'a) -> 'a -> 'a;
ignore: 'a -> unit;
op before : ('a * unit) -> 'a;
I: 'a -> 'a;
K: 'a -> 'b -> 'a
\<close> 

text\<open>Some basic examples for the programming style using these combinators can be found in the
 "The Isabelle Cookbook" section 2.3.\<close>

text\<open>An omnipresent data-structure in the Isabelle SML sources are tables
implemented in @{file "$ISABELLE_HOME/src/Pure/General/table.ML"}. These 
generic tables are presented in an efficient purely functional implementation using
balanced 2-3 trees. Key operations are:\<close>
ML\<open>
signature TABLE_reduced =
sig
  type key
  type 'a table
  exception DUP of key
  exception SAME
  exception UNDEF of key
  val empty: 'a table
  val dest: 'a table -> (key * 'a) list
  val keys: 'a table -> key list
  val lookup_key: 'a table -> key -> (key * 'a) option
  val lookup: 'a table -> key -> 'a option
  val defined: 'a table -> key -> bool
  val update: key * 'a -> 'a table -> 'a table
  (* ... *)
end
\<close>
text\<open>... where \<^verbatim>\<open>key\<close> is usually just a synonym for string.\<close>

chapter*[t2::technical] \<open>  Prover Architecture \<close>

section*[t21::technical] \<open>  The Nano-Kernel: Contexts,  (Theory)-Contexts, (Proof)-Contexts \<close>

text\<open> What I call the 'Nano-Kernel' in Isabelle can also be seen as an acyclic theory graph.
The meat of it can be found in the file @{file "$ISABELLE_HOME/src/Pure/context.ML"}. 
My notion is a bit criticisable since this component, which provides the type of @{ML_type theory}
and @{ML_type Proof.context},  is not that Nano after all.
However, these type are pretty empty place-holders at that level and the content of
@{file  "$ISABELLE_HOME/src/Pure/theory.ML"} is registered much later.
The sources themselves mention it as "Fundamental Structure".
In principle, theories and proof contexts could be REGISTERED as user data inside contexts.
The chosen specialization is therefore an acceptable meddling of the abstraction "Nano-Kernel"
and its application context: Isabelle.

Makarius himself says about this structure:

"Generic theory contexts with unique identity, arbitrarily typed data,
monotonic development graph and history support.  Generic proof
contexts with arbitrarily typed data."

In my words: a context is essentially a container with
\<^item> an id
\<^item> a list of parents (so: the graph structure)
\<^item> a time stamp and
\<^item> a sub-context relation (which uses a combination of the id and the time-stamp to
  establish this relation very fast whenever needed; it plays a crucial role for the
  context transfer in the kernel.


A context comes in form of three 'flavours':
\<^item> theories : @{ML_type theory}'s, containing a syntax and axioms, but also
             user-defined data and configuration information.
\<^item> Proof-Contexts:  @{ML_type Proof.context} 
             containing theories but also additional information if Isar goes into prove-mode.
             In general a richer structure than theories coping also with fixes, facts, goals,
             in order to support the structured Isar proof-style.
\<^item> Generic:  @{ML_type Context.generic }, i.e. the sum of both.

All context have to be seen as mutable; so there are usually transformations defined on them
which are possible as long as a particular protocol (\<^verbatim>\<open>begin_thy\<close> - \<^verbatim>\<open>end_thy\<close> etc) are respected.

Contexts come with type user-defined data which is mutable through the entire lifetime of
a context.
\<close>  

subsection*[t212::technical]\<open> Mechanism 1 : Core Interface. \<close>
text\<open>To be found in @{file  "$ISABELLE_HOME/src/Pure/context.ML"}:\<close>
  
ML\<open>
Context.parents_of: theory -> theory list;
Context.ancestors_of: theory -> theory list;
Context.proper_subthy : theory * theory -> bool;
Context.Proof: Proof.context -> Context.generic; (*constructor*)
Context.proof_of : Context.generic -> Proof.context;
Context.certificate_theory_id : Context.certificate -> Context.theory_id;
Context.theory_name : theory -> string;
Context.map_theory: (theory -> theory) -> Context.generic -> Context.generic;
\<close>


text\<open>ML structure @{ML_structure Proof_Context}:\<close>
ML\<open>
 Proof_Context.init_global: theory -> Proof.context;
 Context.Proof: Proof.context -> Context.generic; (* the path to a generic Context *)
 Proof_Context.get_global: theory -> string -> Proof.context
\<close>


subsection*[t213::example]\<open>Mechanism 2 : global arbitrary data structure that is attached to the global and
   local Isabelle context $\theta$ \<close>
ML \<open>

datatype X = mt
val init = mt;
val ext = I
fun merge (X,Y) = mt

structure Data = Generic_Data
(
  type T = X
  val empty  = init
  val extend = ext
  val merge  = merge
);  


 Data.get : Context.generic -> Data.T;
 Data.put : Data.T -> Context.generic -> Context.generic;
 Data.map : (Data.T -> Data.T) -> Context.generic -> Context.generic;
 (* there are variants to do this on theories ... *)
\<close>


section\<open>  The LCF-Kernel: terms, types, theories, proof\_contexts, thms \<close>  
text\<open>The classical LCF-style \<^emph>\<open>kernel\<close> is about 
\<^enum> Types and terms of a typed $\lambda$-Calculus including constant symbols,
  free variables, $\lambda$-binder and application,
\<^enum> An infrastructure to define types and terms, a \<^emph>\<open>signature\<close>,
  that also assigns to constant symbols types
\<^enum> An abstract type of \<^emph>\<open>theorem\<close> and logical operations on them
\<^enum> (Isabelle specific): a notion of \<^emph>\<open>theory\<close>, i.e. a container 
  providing a signature and set (list) of theorems.   
\<close>


subsection\<open> Terms and Types \<close>
text \<open>A basic data-structure of the kernel is @{file "$ISABELLE_HOME/src/Pure/term.ML"} \<close>  
ML\<open> open Term;
signature TERM' = sig
  (* ... *)
  type indexname = string * int
  type class = string
  type sort = class list
  type arity = string * sort list * sort
  datatype typ =
    Type  of string * typ list |
    TFree of string * sort |
    TVar  of indexname * sort
  datatype term =
    Const of string * typ |
    Free of string * typ |
    Var of indexname * typ |
    Bound of int |
    Abs of string * typ * term |
    $ of term * term
  exception TYPE of string * typ list * term list
  exception TERM of string * term list
  (* ... *)
end
\<close>

text\<open>This core-data structure of the Isabelle Kernel is accessible in the Isabelle/ML environment
and serves as basis for programmed extensions concerning syntax, type-checking, and advanced
tactic programming over kernel primitives and higher API's. There are a number of anti-quotations
giving support for this task; since @{ML Const}-names are long-names revealing information
of the potentially evolving library structure, the use of anti-quotations leads to a safer programming
style of tactics and became therefore standard in the entire Isabelle code-base.
\<close>

text\<open>The following examples show how term- and type-level antiquotations are used and that
     they can both be used for term-construction as well as term-destruction (pattern-matching):\<close>

ML\<open> val Const ("HOL.implies", @{typ "bool \<Rightarrow> bool \<Rightarrow> bool"}) 
              $ Free ("A", @{typ "bool"}) 
              $ Free ("B", @{typ "bool"}) 
        = @{term "A \<longrightarrow> B"};

 val "HOL.bool" = @{type_name "bool"};

 (* three ways to write type bool:@ *)
 val Type("fun",[s,Type("fun",[@{typ "bool"},Type(@{type_name "bool"},[])])]) = @{typ "bool \<Rightarrow> bool \<Rightarrow> bool"};
 
\<close>

text\<open>Note that the SML interpreter is configured that he will actually print a type
     \<^verbatim>\<open>Type("HOL.bool",[])\<close> just as \<^verbatim>\<open>"bool": typ\<close>, so a compact notation looking
     pretty much like a string. This can be confusing at times.\<close>

text\<open>Note, furthermore, that there is a programming API for the HOL-instance of Isabelle:
it is contained in @{file  "$ISABELLE_HOME/src/HOL/Tools/hologic.ML"}. It offers for many
operators of the HOL logic specific constructors and destructors:
\<close>

ML\<open>
HOLogic.boolT : typ;
HOLogic.mk_Trueprop: term -> term;
HOLogic.dest_Trueprop: term -> term;
HOLogic.Trueprop_conv: conv -> conv;
HOLogic.mk_setT: typ -> typ;
HOLogic.dest_setT: typ -> typ;
HOLogic.Collect_const: typ -> term;
HOLogic.mk_Collect: string * typ * term -> term;
HOLogic.mk_mem: term * term -> term;
HOLogic.dest_mem: term -> term * term;
HOLogic.mk_set: typ -> term list -> term;
HOLogic.conj_intr: Proof.context -> thm -> thm -> thm;
HOLogic.conj_elim: Proof.context -> thm -> thm * thm;
HOLogic.conj_elims: Proof.context -> thm -> thm list;
HOLogic.conj: term;
HOLogic.disj: term;
HOLogic.imp: term;
HOLogic.Not: term;
HOLogic.mk_not: term -> term;
HOLogic.mk_conj: term * term -> term;
HOLogic.dest_conj: term -> term list;
HOLogic.conjuncts: term -> term list;
(* ... *)
\<close>



subsection\<open> Type-Certification (=checking that a type annotation is consistent) \<close>

ML\<open> Type.typ_instance: Type.tsig -> typ * typ -> bool (* raises  TYPE_MATCH *) \<close>
text\<open> there is a joker type that can be added as place-holder during term construction.
       Jokers can be eliminated by the type inference. \<close>
  
ML\<open>  Term.dummyT : typ \<close>

ML\<open>
Sign.typ_instance: theory -> typ * typ -> bool;
Sign.typ_match: theory -> typ * typ -> Type.tyenv -> Type.tyenv;
Sign.typ_unify: theory -> typ * typ -> Type.tyenv * int -> Type.tyenv * int;
Sign.const_type: theory -> string -> typ option;
Sign.certify_term: theory -> term -> term * typ * int;   (* core routine for CERTIFICATION of types*)
Sign.cert_term: theory -> term -> term;                  (* short-cut for the latter *)
Sign.tsig_of: theory -> Type.tsig                        (* projects the type signature *)
\<close>
text\<open> 
@{ML "Sign.typ_match"} etc. is actually an abstract wrapper on the structure 
@{ML_structure "Type"} 
which contains the heart of the type inference. 
It also contains the type substitution type  @{ML_type "Type.tyenv"} which is
is actually a type synonym for @{ML_type "(sort * typ) Vartab.table"} 
which in itself is a synonym for @{ML_type "'a Symtab.table"}, so 
possesses the usual @{ML "Symtab.empty"} and  @{ML "Symtab.dest"} operations. \<close>  

text\<open>Note that @{emph \<open>polymorphic variables\<close>} are treated like constant symbols 
in the type inference; thus, the following test, that one type is an instance of the
other, yields false:
\<close>
ML\<open>
val ty = @{typ "'a option"};
val ty' = @{typ "int option"};

val Type("List.list",[S]) = @{typ "('a) list"}; (* decomposition example *)

val false = Sign.typ_instance @{theory}(ty', ty);
\<close>
text\<open>In order to make the type inference work, one has to consider @{emph \<open>schematic\<close>} 
type variables, which are more and more hidden from the Isar interface. Consequently,
the typ antiquotation above will not work for schematic type variables and we have
to construct them by hand on the SML level: \<close>
ML\<open> 
val t_schematic = Type("List.list",[TVar(("'a",0),@{sort "HOL.type"})]);
\<close>
text\<open> MIND THE "'" !!!\<close>
text \<open>On this basis, the following @{ML_type "Type.tyenv"} is constructed: \<close>
ML\<open>
val tyenv = Sign.typ_match ( @{theory}) 
               (t_schematic, @{typ "int list"})
               (Vartab.empty);            
val  [(("'a", 0), (["HOL.type"], @{typ "int"}))] = Vartab.dest tyenv;
\<close>

text\<open> Type generalization --- the conversion between free type variables and schematic 
type variables ---  is apparently no longer part of the standard API (there is a slightly 
more general replacement in @{ML "Term_Subst.generalizeT_same"}, however). Here is a way to
overcome this by a self-baked generalization function:\<close>  

ML\<open>
val generalize_typ = Term.map_type_tfree (fn (str,sort)=> Term.TVar((str,0),sort));
val generalize_term = Term.map_types generalize_typ;
val true = Sign.typ_instance @{theory} (ty', generalize_typ ty)
\<close>
text\<open>... or more general variants thereof that are parameterized by the indexes for schematic
type variables instead of assuming just @{ML "0"}. \<close>

text\<open> Example:\<close> 
ML\<open>val t = generalize_term @{term "[]"}\<close>

text
\<open>Now we turn to the crucial issue of type-instantiation and with a given type environment
@{ML "tyenv"}. For this purpose, one has to switch to the low-level interface 
@{ML_structure "Term_Subst"}. 
\<close>

ML\<open>
Term_Subst.map_types_same : (typ -> typ) -> term -> term;
Term_Subst.map_aterms_same : (term -> term) -> term -> term;
Term_Subst.instantiate: ((indexname * sort) * typ) list * ((indexname * typ) * term) list -> term -> term;
Term_Subst.instantiateT: ((indexname * sort) * typ) list -> typ -> typ;
Term_Subst.generalizeT: string list -> int -> typ -> typ;
                        (* this is the standard type generalisation function !!!
                           only type-frees in the string-list were taken into account. *)
Term_Subst.generalize: string list * string list -> int -> term -> term
                        (* this is the standard term generalisation function !!!
                           only type-frees and frees in the string-lists were taken 
                           into account. *)
\<close>

text \<open>Apparently, a bizarre conversion between the old-style interface and 
the new-style @{ML "tyenv"} is necessary. See the following example.\<close>
ML\<open>
val S = Vartab.dest tyenv;
val S' = (map (fn (s,(t,u)) => ((s,t),u)) S) : ((indexname * sort) * typ) list;
         (* it took me quite some time to find out that these two type representations,
            obscured by a number of type-synonyms, where actually identical. *)
val ty = t_schematic;
val ty' = Term_Subst.instantiateT S' t_schematic;
val t = (generalize_term @{term "[]"});

val t' = Term_Subst.map_types_same (Term_Subst.instantiateT S') (t)
(* or alternatively : *)
val t'' = Term.map_types (Term_Subst.instantiateT S') (t)
\<close>

subsection\<open> Type-Inference (= inferring consistent type information if possible) \<close>

text\<open> Type inference eliminates also joker-types such as @{ML dummyT} and produces
       instances for schematic type variables where necessary. In the case of success,
       it produces a certifiable term. \<close>  
ML\<open>  
Type_Infer_Context.infer_types: Proof.context -> term list -> term list  
\<close>
  
subsection\<open> thy and the signature interface\<close>  
ML\<open>
Sign.tsig_of: theory -> Type.tsig;
Sign.syn_of : theory -> Syntax.syntax;
Sign.of_sort : theory -> typ * sort -> bool ;
\<close>

subsection\<open> Thm's and the LCF-Style, "Mikro"-Kernel \<close>  
text\<open> 
  The basic constructors and operations on theorems@{file "$ISABELLE_HOME/src/Pure/thm.ML"},
  a set of derived (Pure) inferences can be found in @{file "$ISABELLE_HOME/src/Pure/drule.ML"}.

  The main types provided by structure \<^verbatim>\<open>thm\<close> are certified types @{ML_type ctyp}, 
  certified terms @{ML_type cterm}, @{ML_type thm} as well as conversions @{ML_type conv}.
\<close>

ML\<open>
signature BASIC_THM =
sig
  type ctyp
  type cterm
  exception CTERM of string * cterm list
  type thm
  type conv = cterm -> thm
  exception THM of string * int * thm list
end;
\<close>

text\<open>Certification of types and terms on the kernel-level is done by the generators:\<close>
ML\<open>
  Thm.global_ctyp_of: theory -> typ -> ctyp;
  Thm.ctyp_of: Proof.context -> typ -> ctyp;
  Thm.global_cterm_of: theory -> term -> cterm;
  Thm.cterm_of: Proof.context -> term -> cterm;
\<close>
text\<open>... which perform type-checking in the given theory context in order to make a type
     or term "admissible" for the kernel.\<close>

text\<open> We come now to the very heart of the LCF-Kernel of Isabelle, which 
     provides the fundamental inference rules of Isabelle/Pure. 

   Besides a number of destructors on @{ML_type thm}'s,
  the abstract data-type \<^verbatim>\<open>thm\<close> is used for logical objects of the form 
  $\Gamma \vdash_\theta \phi$, where $\Gamma$ represents a set of local assumptions,
  $\theta$ the "theory" or more precisely the global context in which a formula $\phi$ 
  has been constructed just by applying the following operations representing 
  logical inference rules:

\<close>
ML\<open>
  (*inference rules*)
  Thm.assume: cterm -> thm;
  Thm.implies_intr: cterm -> thm -> thm;
  Thm.implies_elim: thm -> thm -> thm;
  Thm.forall_intr: cterm -> thm -> thm;
  Thm.forall_elim: cterm -> thm -> thm;

  Thm.transfer : theory -> thm -> thm;

  Thm.generalize: string list * string list -> int -> thm -> thm;
  Thm.instantiate: ((indexname*sort)*ctyp)list * ((indexname*typ)*cterm) list -> thm -> thm;
\<close>
text\<open>  They reflect the Pure logic depicted in a number of presentations such as 
  M. Wenzel, \<^emph>\<open>Parallel Proof Checking in Isabelle/Isar\<close>, PLMMS 2009, or simiular papers.
  Notated as logical inference rules, these operations were presented as follows:
\<close>

side_by_side_figure*["text-elements"::side_by_side_figure,anchor="''fig-kernel1''",
                      caption="''Pure Kernel Inference Rules I ''",relative_width="48",
                      src="''figures/pure-inferences-I''",anchor2="''fig-kernel2''",
                      caption2="''Pure Kernel Inference Rules II''",relative_width2="47",
                      src2="''figures/pure-inferences-II''"]\<open>  \<close>

(*
figure*[kir1::figure,relative_width="100",src="''figures/pure-inferences-I''"]
       \<open> Pure Kernel Inference Rules I.\<close>
figure*[kir2::figure,relative_width="100",src="''figures/pure-inferences-II''"]
       \<open> Pure Kernel Inference Rules II. \<close>
 *)

text\<open>Note that the transfer rule:
\[
\begin{prooftree}
 \Gamma \vdash_\theta \phi            \qquad \qquad       \theta \sqsubseteq \theta'
\justifies
 \Gamma \vdash_{\theta'} \phi  \qquad \qquad
\end{prooftree}
\]
which is a consequence of explicit theories  characteristic for Isabelle's LCF-kernel design
and a remarkable difference to its sisters HOL-Light and HOL4; instead of transfer, these systems
reconstruct proofs in an enlarged global context instead of taking the result and converting it.\<close>

text\<open>Besides the meta-logical (Pure) implication $\_\Longrightarrow \_$, the Kernel axiomatizes
also a Pure-Equality $\_ \equiv \_ $ used for definitions of constant symbols: \<close>
ML\<open>
  Thm.reflexive: cterm -> thm;
  Thm.symmetric: thm -> thm;
  Thm.transitive: thm -> thm -> thm;
\<close>
text\<open>The operation:\<close>
ML\<open>  Thm.trivial: cterm -> thm; \<close>
text\<open>... produces the elementary tautologies of the form @{prop "A \<Longrightarrow> A"},
  an operation used to start a backward-style proof.\<close>

text\<open>The elementary conversions are:\<close>
ML\<open>
  Thm.beta_conversion: bool -> conv;
  Thm.eta_conversion: conv;
  Thm.eta_long_conversion: conv;
\<close>

text\<open>On the level of @{ML_structure "Drule"}, a number of higher-level operations is established, 
     which is in part accessible by a number of forward-reasoning notations on Isar-level.\<close>
ML\<open>
  op RSN: thm * (int * thm) -> thm;
  op RS: thm * thm -> thm;
  op RLN: thm list * (int * thm list) -> thm list;
  op RL: thm list * thm list -> thm list;
  op MRS: thm list * thm -> thm;
  op OF: thm * thm list -> thm;
  op COMP: thm * thm -> thm;
\<close>


subsection\<open> Theories \<close>

text \<open> This structure yields the datatype \verb*thy* which becomes the content of 
\verb*Context.theory*. In a way, the LCF-Kernel registers itself into the Nano-Kernel,
which inspired me (bu) to this naming. 

\<close>
ML\<open>

(* intern Theory.Thy; 

datatype thy = Thy of
 {pos: Position.T,
  id: serial,
  axioms: term Name_Space.table,
  defs: Defs.T,
  wrappers: wrapper list * wrapper list};

*)

Theory.check: {long: bool} -> Proof.context -> string * Position.T -> theory;

Theory.local_setup: (Proof.context -> Proof.context) -> unit;
Theory.setup: (theory -> theory) -> unit;  (* The thing to extend the table of "command"s with parser - callbacks. *)
Theory.get_markup: theory -> Markup.T;
Theory.axiom_table: theory -> term Name_Space.table;
Theory.axiom_space: theory -> Name_Space.T;
Theory.axioms_of: theory -> (string * term) list;
Theory.all_axioms_of: theory -> (string * term) list;
Theory.defs_of: theory -> Defs.T;
Theory.at_begin: (theory -> theory option) -> theory -> theory;
Theory.at_end: (theory -> theory option) -> theory -> theory;
Theory.begin_theory: string * Position.T -> theory list -> theory;
Theory.end_theory: theory -> theory;

\<close>


section\<open>Backward Proofs: Tactics, Tacticals and Goal-States\<close>

text\<open>At this point, we leave the Pure-Kernel and start to describe the first layer on top
of it, involving support for specific styles of reasoning and automation of reasoning.\<close>

text\<open> \<^verbatim>\<open>tactic\<close>'s are in principle \<^emph>\<open>relations\<close> on theorems @{ML_type "thm"}; this gives a natural way 
to represent the fact that HO-Unification (and therefore the mechanism of rule-instantiation) 
are non-deterministic in principle. Heuristics may choose particular preferences between 
the theorems in the range of this relation, but the Isabelle Design accepts this fundamental 
fact reflected at this point in the prover architecture. 
This potentially infinite relation is implemented by a function of theorems to lazy lists 
over theorems, which gives both sufficient structure for heuristic
considerations as well as a nice algebra, called  \<^verbatim>\<open>TACTICAL\<close>'s, providing a bottom element
@{ML "no_tac"} (the function that always fails), the top-element @{ML "all_tac"}
 (the function that never fails), sequential composition @{ML "op THEN"}, (serialized) 
non-deterministic composition @{ML "op ORELSE"}, conditionals, repetitions over lists, etc.
The following is an excerpt of @{file "~~/src/Pure/tactical.ML"}:
\<close>

ML\<open>
signature TACTICAL =
sig
  type tactic = thm -> thm Seq.seq

  val all_tac: tactic
  val no_tac: tactic
  val COND: (thm -> bool) -> tactic -> tactic -> tactic

  val THEN: tactic * tactic -> tactic
  val ORELSE: tactic * tactic -> tactic
  val THEN': ('a -> tactic) * ('a -> tactic) -> 'a -> tactic
  val ORELSE': ('a -> tactic) * ('a -> tactic) -> 'a -> tactic

  val TRY: tactic -> tactic
  val EVERY: tactic list -> tactic
  val EVERY': ('a -> tactic) list -> 'a -> tactic
  val FIRST: tactic list -> tactic
  (* ... *)
end
\<close>

text\<open>The next layer in the architecture describes @{ML_type \<open>tactic\<close>}'s, i.e. basic operations on 
theorems  in a backward reasoning style (bottom up development of proof-trees). An initial goal-state 
for some property @{term A} --- the \<^emph>\<open>goal\<close> --- is constructed via the kernel 
@{ML "Thm.trivial"}-operation into  @{term "A \<Longrightarrow> A"}, and tactics either refine the premises 
--- the \<^emph>\<open>subgoals\<close> the of this meta-implication --- 
producing more and more of them or eliminate them in subsequent goal-states. Subgoals of the form  
@{term "B\<^sub>1 \<Longrightarrow> B\<^sub>2 \<Longrightarrow> A \<Longrightarrow> B\<^sub>3 \<Longrightarrow> B\<^sub>4 \<Longrightarrow> A"} can be eliminated via 
the @{ML Tactic.assume_tac} - tactic, 
and a subgoal @{term C\<^sub>m} can be refined via the theorem
@{term "E\<^sub>1 \<Longrightarrow> E\<^sub>2 \<Longrightarrow> E\<^sub>3 \<Longrightarrow> C\<^sub>m"} the @{ML Tactic.resolve_tac} - tactic to new subgoals
@{term "E\<^sub>1"},@{term "E\<^sub>2"}, @{term "E\<^sub>3"}. In case that a theorem used for resolution
has no premise @{term "E\<^sub>i"}, the subgoal  @{term C\<^sub>m} is also eliminated ("closed").

The following abstract of the most commonly used @{ML_type \<open>tactic\<close>}'s drawn from
@{file "~~/src/Pure/tactic.ML"} looks as follows:
\<close>

ML\<open>
  (* ... *)
  assume_tac: Proof.context -> int -> tactic;
  compose_tac: Proof.context -> (bool * thm * int) -> int -> tactic;
  resolve_tac: Proof.context -> thm list -> int -> tactic;
  eresolve_tac: Proof.context -> thm list -> int -> tactic;
  forward_tac: Proof.context -> thm list -> int -> tactic;
  dresolve_tac: Proof.context -> thm list -> int -> tactic;
  rotate_tac: int -> int -> tactic;
  defer_tac: int -> tactic;
  prefer_tac: int -> tactic;
  (* ... *)
\<close>
text\<open>Note that "applying a rule" is a fairly complex operation in the Extended Isabelle Kernel,
i.e. the tactic layer. It involves at least four phases, interfacing a theorem
coming from the global context $\theta$ (=theory), be it axiom or derived, into a given goal-state.
\<^item> \<^emph>\<open>generalization\<close>. All free variables in the theorem were replaced by schematic variables.
  For example, @{term "x + y = y + x"} is converted into 
  @{emph \<open>?x + ?y = ?y + ?x\<close> }. 
  By the way, type variables were treated equally.
\<^item> \<^emph>\<open>lifting over assumptions\<close>. If a subgoal is of the form: 
  @{term "B\<^sub>1 \<Longrightarrow> B\<^sub>2 \<Longrightarrow> A"} and we have a theorem @{term "D\<^sub>1 \<Longrightarrow> D\<^sub>2 \<Longrightarrow> A"}, then before
  applying the theorem, the premisses were \<^emph>\<open>lifted\<close> resulting in the logical refinement:
  @{term "(B\<^sub>1 \<Longrightarrow> B\<^sub>2 \<Longrightarrow> D\<^sub>1) \<Longrightarrow> (B\<^sub>1 \<Longrightarrow> B\<^sub>2 \<Longrightarrow> D\<^sub>2) \<Longrightarrow> A"}. Now, @{ML "resolve_tac"}, for example,
  will replace the subgoal @{term "B\<^sub>1 \<Longrightarrow> B\<^sub>2 \<Longrightarrow> A"} by the subgoals 
  @{term "B\<^sub>1 \<Longrightarrow> B\<^sub>2 \<Longrightarrow> D\<^sub>1"}  and  @{term "B\<^sub>1 \<Longrightarrow> B\<^sub>2 \<Longrightarrow> D\<^sub>2"}. Of course, if the theorem wouldn't
  have assumptions @{term "D\<^sub>1"} and @{term "D\<^sub>2"}, the subgoal @{term "A"} would be replaced by 
  \<^bold>\<open>nothing\<close>, i.e. deleted.
\<^item> \<^emph>\<open>lifting over parameters\<close>. If a subgoal is meta-quantified like in:
  @{term "\<And> x y z. A x y z"}, then a theorem like  @{term "D\<^sub>1 \<Longrightarrow> D\<^sub>2 \<Longrightarrow> A"} is \<^emph>\<open>lifted\<close>  
  to @{term "\<And> x y z. D\<^sub>1' \<Longrightarrow> D\<^sub>2' \<Longrightarrow> A'"}, too. Since free variables occurring in @{term "D\<^sub>1"}, 
  @{term "D\<^sub>2"} and @{term "A"} have been replaced by schematic variables (see phase one),
  they must be replaced by parameterized schematic variables, i. e. a kind of skolem function.
  For example, @{emph \<open>?x + ?y = ?y + ?x\<close> } would be lifted to 
  @{emph \<open>!!  x y z. ?x x y z + ?y x y z = ?y x y z + ?x x y z\<close>}. This way, the lifted theorem
  can be instantiated by the parameters  @{term "x y z"} representing "fresh free variables"
  used for this sub-proof. This mechanism implements their logically correct bookkeeping via
  kernel primitives.
\<^item> \<^emph>\<open>Higher-order unification (of schematic type and term variables)\<close>.
  Finally, for all these schematic variables, a solution must be found.
  In the case of @{ML resolve_tac}, the conclusion of the (doubly lifted) theorem must
  be equal to the conclusion of the subgoal, so @{term A} must be $\alpha/\beta$-equivalent to
  @{term A'} in the example above, which is established by a higher-order unification
  process. It is a bit unfortunate that for implementation efficiency reasons, a very substantial
  part of the code for HO-unification is in the kernel module @{ML_type "thm"}, which makes this
  critical component of the architecture larger than necessary.  
\<close>

text\<open>In a way, the two lifting processes represent an implementation of the conversion between
Gentzen Natural Deduction (to which Isabelle/Pure is geared) reasoning and 
Gentzen Sequent Deduction.\<close>


section\<open>The classical goal package\<close>

ML\<open> open Goal;
Goal.prove_internal : Proof.context -> cterm list -> cterm -> (thm list -> tactic) -> thm;

Goal.prove_global :  theory -> string list -> term list -> term -> 
                   ({context: Proof.context, prems: thm list} -> tactic) -> thm
\<close>

section\<open>The Isar Engine\<close>

text\<open>The main structure of the Isar-engine is @{ ML_structure Toplevel} and provides and
internal @{ ML_type state} with the necessary infrastructure --- 
i.e. the operations to pack and unpack theories and Proof.contexts  --- on it:
\<close>
ML\<open> 

 Toplevel.theory_toplevel: theory -> Toplevel.state;
 Toplevel.toplevel: Toplevel.state;
 Toplevel.is_toplevel: Toplevel.state -> bool;
 Toplevel.is_theory: Toplevel.state -> bool;
 Toplevel.is_proof: Toplevel.state -> bool;
 Toplevel.is_skipped_proof: Toplevel.state -> bool;
 Toplevel.level: Toplevel.state -> int;
 Toplevel.context_of: Toplevel.state -> Proof.context;
 Toplevel.generic_theory_of: Toplevel.state -> generic_theory;
 Toplevel.theory_of: Toplevel.state -> theory;
 Toplevel.proof_of: Toplevel.state -> Proof.state;
 Toplevel.presentation_context: Toplevel.state -> Proof.context;

\<close>
  
subsection \<open>Transaction Management in the Isar-Engine : The Toplevel \<close>
  
ML\<open>

Toplevel.exit: Toplevel.transition -> Toplevel.transition;
Toplevel.keep: (Toplevel.state -> unit) -> Toplevel.transition -> Toplevel.transition;
Toplevel.keep': (bool -> Toplevel.state -> unit) -> Toplevel.transition -> Toplevel.transition;
Toplevel.ignored: Position.T -> Toplevel.transition;
Toplevel.generic_theory: (generic_theory -> generic_theory) -> Toplevel.transition -> Toplevel.transition;
Toplevel.theory': (bool -> theory -> theory) -> Toplevel.transition -> Toplevel.transition;
Toplevel.theory: (theory -> theory) -> Toplevel.transition -> Toplevel.transition;

Toplevel.present_local_theory:
(xstring * Position.T) option ->
     (Toplevel.state -> unit) -> Toplevel.transition -> Toplevel.transition;
(* where text treatment and antiquotation parsing happens *)


(*fun document_command markdown (loc, txt) =
  Toplevel.keep (fn state =>
    (case loc of
      NONE => ignore (output_text state markdown txt)
    | SOME (_, pos) =>
        error ("Illegal target specification -- not a theory context" ^ Position.here pos))) o
  Toplevel.present_local_theory loc (fn state => ignore (output_text state markdown txt)); *)

(* Isar Toplevel Steuerung *)
Toplevel.keep :  (Toplevel.state -> unit) -> Toplevel.transition -> Toplevel.transition;
    (* val keep' = add_trans o Keep;
       fun keep f = add_trans (Keep (fn _ => f));
     *)

Toplevel.present_local_theory : (xstring * Position.T) option -> (Toplevel.state -> unit) ->
    Toplevel.transition -> Toplevel.transition;
    (* fun present_local_theory target = present_transaction (fn int =>
           (fn Theory (gthy, _) =>
                   let val (finish, lthy) = Named_Target.switch target gthy;
                   in Theory (finish lthy, SOME lthy) end
           | _ => raise UNDEF));

       fun present_transaction f g = add_trans (Transaction (f, g));
       fun transaction f = present_transaction f (K ());
    *)

Toplevel.theory : (theory -> theory) -> Toplevel.transition -> Toplevel.transition; 
   (* fun theory' f = transaction (fn int =>
                (fn Theory (Context.Theory thy, _) =>
                      let val thy' = thy
                                     |> Sign.new_group
                                     |> f int
                                     |> Sign.reset_group;
                      in Theory (Context.Theory thy', NONE) end
                | _ => raise UNDEF));

      fun theory f = theory' (K f); *)

\<close>  
  
  
ML\<open>


(* Isar Toplevel Steuerung *)
Toplevel.keep :  (Toplevel.state -> unit) -> Toplevel.transition -> Toplevel.transition;
    (* val keep' = add_trans o Keep;
       fun keep f = add_trans (Keep (fn _ => f));
     *)

Toplevel.present_local_theory : (xstring * Position.T) option -> (Toplevel.state -> unit) ->
    Toplevel.transition -> Toplevel.transition;
    (* fun present_local_theory target = present_transaction (fn int =>
           (fn Theory (gthy, _) =>
                   let val (finish, lthy) = Named_Target.switch target gthy;
                   in Theory (finish lthy, SOME lthy) end
           | _ => raise UNDEF));

       fun present_transaction f g = add_trans (Transaction (f, g));
       fun transaction f = present_transaction f (K ());
    *)

Toplevel.theory : (theory -> theory) -> Toplevel.transition -> Toplevel.transition; 
   (* fun theory' f = transaction (fn int =>
                (fn Theory (Context.Theory thy, _) =>
                      let val thy' = thy
                                     |> Sign.new_group
                                     |> f int
                                     |> Sign.reset_group;
                      in Theory (Context.Theory thy', NONE) end
                | _ => raise UNDEF));

      fun theory f = theory' (K f); *)


\<close>
  
  
subsection\<open> Configuration flags of fixed type in the Isar-engine. \<close>
text\<open>The toplevel also provides an infrastructure for managing configuration options 
for system components. Based on a sum-type @{ML_type Config.value } 
with the alternatives \<^verbatim>\<open> Bool of bool | Int of int | Real of real | String of string\<close>
and building the parametric configuration types @{ML_type "'a Config.T" } and the
instance  \<^verbatim>\<open>type raw = value T\<close>, for all registered configurations the protocol:
\<close>
ML\<open>
 Config.get: Proof.context -> 'a Config.T -> 'a;
 Config.map: 'a Config.T -> ('a -> 'a) -> Proof.context -> Proof.context;
 Config.put: 'a Config.T -> 'a -> Proof.context -> Proof.context;
 Config.get_global: theory -> 'a Config.T -> 'a;
 Config.map_global: 'a Config.T -> ('a -> 'a) -> theory -> theory;
 Config.put_global: 'a Config.T -> 'a -> theory -> theory;
\<close>
text\<open>... etc. is defined.\<close>

text\<open>Example registration of an config attribute XS232: \<close>
ML\<open>
val (XS232, XS232_setup)
     = Attrib.config_bool \<^binding>\<open>XS232\<close> (K false);

val _ = Theory.setup XS232_setup;
\<close>

(* or: just command:

setup\<open>XS232_setup\<close>

*)

text\<open>Another mechanism are global synchronised variables:\<close>
ML\<open> (* For example *)
           
val C = Synchronized.var "Pretty.modes" "latEEex"; 
(* Synchronized: a mechanism to bookkeep global
   variables with synchronization mechanism included *)
Synchronized.value C;
\<close>  
  
chapter\<open>Front-End \<close>  
text\<open>In the following chapter, we turn to the right part of the system architecture 
shown in @{docitem \<open>architecture\<close>}: 
The PIDE ("Prover-IDE") layer consisting of a part written in SML and another in SCALA. 
Roughly speaking, PIDE implements "continuous build - continuous check" - functionality
over a textual, albeit generic document model. It transforms user modifications
of text elements in an instance of this model into increments (edits) and communicates
them to the Isabelle system. The latter reacts by the creation of a multitude of light-weight
reevaluation threads resulting in an asynchronous stream of markup that is used to annotate text
elements. Such markup is used to highlight, e.g., variables
or keywords with specific colors, to hyper-linking bound variables to their defining occurrences,
or to annotate type-information to terms which becomes displayed by specific
user-gestures on demand (hovering), etc. 
Note that PIDE is not an editor, it is the framework that 
coordinates these asynchronous information streams and optimizes it to a certain
extent (outdated markup referring to modified text is dropped, and 
corresponding re-calculations are oriented to the user focus, for example). 
Four concrete editors --- also called PIDE applications --- have been implemented:
\<^enum>an Eclipse plugin (developped by an Edinburg-group, based on an very old PIDE version),
\<^enum>a Visual-Studio Code plugin (developed by Makarius Wenzel), 
 currently based on a fairly old PIDE version, 
\<^enum>clide, a web-client supporting javascript and HTML5
 (developed by a group at University Bremen, based on a very old PIDE version), and 
\<^enum>the most commonly used: the plugin in JEdit - Editor,
 (developed by Makarius Wenzel, current PIDE version.)
\<close>

text\<open>The document model forsees a number of text files, which are organized in form of an acyclic graph. Such graphs can be 
grouped into \<^emph>\<open>sessions\<close> and "frozen" to binaries in order to avoid long compilation 
times. Text files have an abstract name serving as identity (the mapping to file-paths 
in an underlying file-system is done in an own build management).
The primary format of the text files is \<^verbatim>\<open>.thy\<close> (historically for: theory),
secondary formats can be \<^verbatim>\<open>.sty\<close>,\<^verbatim>\<open>.tex\<close>, \<^verbatim>\<open>.png\<close>, \<^verbatim>\<open>.pdf\<close>, or other files processed 
by Isabelle and listed in a configuration processed by the build system.
\<close>
figure*[fig3::figure, relative_width="100",src="''figures/document-model''"]
        \<open>A Theory-Graph in the Document Model\<close>
text\<open>A \<^verbatim>\<open>.thy\<close> file consists of a \<^emph>\<open>header\<close>, a \<^emph>\<open>context-definition\<close> and 
a \<^emph>\<open>body\<close> consisting of a sequence of \<^emph>\<open>commands\<close>. Even the header consists of
a sequence of commands used for introductory text elements not depending on any context
information (so: practically excluding any form of text antiquotation (see above)).
The context-definition contains an \<^emph>\<open>import\<close> and a \<^emph>\<open>keyword\<close> section;  
for example:
\begin{verbatim}
theory Isa_DOF                (* Isabelle Document Ontology Framework *)
  imports  Main  
           RegExpInterface    (* Interface to functional regular automata for monitoring *)
           Assert
           
  keywords "+=" ":=" "accepts" "rejects"
\end{verbatim}
where \<^verbatim>\<open>Isa_DOF\<close> is the abstract name of the text-file, \<^verbatim>\<open>Main\<close> etc. refer to imported
text files (recall that the import relation must be acyclic). \<^emph>\<open>keyword\<close>s are used to separate 
commands form each other;
predefined commands allow for the dynamic creation of new commands similarly 
to the definition of new functions in an interpreter shell (or: toplevel, see above.).
A command starts with a pre-declared keyword and specific syntax of this command;
the declaration of a keyword is only allowed in the same \<^verbatim>\<open>.thy\<close>-file where the
the corresponding new command is defined. The semantics of the command is expressed
in ML and consists of a @{ML_type "Toplevel.transition -> Toplevel.transition"}
function. Thus, the Isar-toplevel supports the generic document model 
and allows for user-programmed extensions.
\<close>

text\<open>Isabelle \<^verbatim>\<open>.thy\<close>-files were processed by two types of parsers:
\<^enum> the "outer-syntax" (i.e. the syntax for commands) is processed 
  by a lexer-library and parser combinators built on top, and
\<^enum> the "inner-syntax" (i.e. the syntax for @{term \<open>\<Lambda>\<close>} - terms) 
  with an evolved, eight-layer parsing and pretty-printing process.
\<close>


section\<open>Basics: string, bstring and xstring\<close>
text\<open>@{ML_type "string"} is the basic library type from the SML library
in structure @{ML_structure "String"}. Many Isabelle operations produce
or require formats thereof introduced as type synonyms 
@{ML_type "bstring"} (defined in structure @{ML_structure "Binding"}
and @{ML_type "xstring"} (defined in structure @{ML_structure "Name_Space"}.
Unfortunately, the abstraction is not tight and combinations with 
elementary routines might produce quite crappy results.
\<close>

ML\<open>val b = Binding.name_of@{binding "here"}\<close>
text\<open>... produces the system output \verb+val it = "here": bstring+,
     but note that it is misleading to believe it is just a string.
\<close>

ML\<open>String.explode b\<close> (* is harmless, but  *)
ML\<open>String.explode(Binding.name_of
(Binding.conglomerate[Binding.qualified_name "X.x",
              @{binding "here"}]  ))\<close>
(* Somehow it is possible to smuggle markup into bstrings; and this leads 
   ML\<open>(((String.explode(!ODL_Command_Parser.SPY6))))\<close>
   to something like 
   val it = [#"\^E", #"\^F", #"i", #"n", #"p", #"u", #"t", #"\^F", #"d", #"e", #"l", #"i", #"m", #"i", #"t", #"e", #"d", #"=", #"f", #"a", ...]: char list
*)

text\<open> However, there is an own XML parser for this format. See Section Markup. 
\<close>
ML\<open> fun dark_matter x = XML.content_of (YXML.parse_body x)\<close>

(* MORE TO COME *)

section\<open>Positions\<close>
text\<open>A basic data-structure relevant for PIDE are \<^emph>\<open>positions\<close>; beyond the usual line- and column
information they can represent ranges, list of ranges, and the name of the atomic sub-document
in which they are contained. In the command:\<close>
ML\<open>
val pos = @{here};
val markup = Position.here pos;
writeln ("And a link to the declaration of 'here' is "^markup)
\<close> 
(* \<^here>  *)
text\<open> ... uses the antiquotation @{ML "@{here}"} to infer from the system lexer the actual position
of itself in the global document, converts it to markup (a string-representation of it) and sends
it via the usual @{ML "writeln"} to the interface. \<close>

figure*[hyplinkout::figure,relative_width="40",src="''figures/markup-demo''"]
\<open>Output with hyperlinked position.\<close>

text\<open>@{docitem \<open>hyplinkout\<close>} shows the produced output where the little house-like symbol in the 
display is hyperlinked to the position of @{ML "@{here}"} in the ML sample above.\<close>

section\<open>Markup and Low-level Markup Reporting\<close>
text\<open>The structures @{ML_structure Markup} and @{ML_structure Properties} represent the basic 
annotation data which is part of the protocol sent from Isabelle to the frontend.
They are qualified as "quasi-abstract", which means they are intended to be an abstraction of 
the serialized, textual presentation of the protocol. Markups are structurally a pair of a key
and properties; @{ML_structure Markup} provides a number of of such \<^emph>\<open>key\<close>s for annotation classes
such as "constant", "fixed", "cartouche", some of them quite obscure. Here is a code sample
from \<^theory_text>\<open>Isabelle_DOF\<close>. A markup must be tagged with an id; this is done by the @{ML serial}-function
discussed earlier.\<close>
ML\<open> 
local 
  
val docclassN = "doc_class";    

(* derived from: theory_markup; def for "defining occurrence" (true) in contrast to
   "referring occurence" (false). *) 
fun docclass_markup def name id pos =
  if id = 0 then Markup.empty
  else           Markup.properties (Position.entity_properties_of def id pos)
                                   (Markup.entity docclassN name);   

in

fun report_defining_occurrence pos cid =
           let val id = serial ()
               val markup_of_cid = docclass_markup true cid id pos
           in  Position.report pos markup_of_cid end;

end
\<close>

text\<open>The @\<open>ML report_defining_occurrence\<close>-function above takes a position and a "cid" parsed
in the Front-End, converts this into markup together with a unique number identifying this
markup, and sends this as a report to the Front-End. \<close>


section\<open>Environment Structured Reporting\<close>

text\<open> @{ML_type "'a Name_Space.table"} \<close>

section\<open> Parsing issues \<close>  

text\<open> Parsing combinators represent the ground building blocks of both generic input engines
as well as the specific Isar framework. They are implemented in the  structure \verb+Token+ 
providing core type \verb+Token.T+. 
\<close>
ML\<open> open Token\<close>  

ML\<open>

(* Provided types : *)
(*
  type 'a parser = T list -> 'a * T list
  type 'a context_parser = Context.generic * T list -> 'a * (Context.generic * T list)
*)

(* conversion between these two : *)

fun parser2contextparser pars (ctxt, toks) = let val (a, toks') = pars toks
                                             in  (a,(ctxt, toks')) end;
val _ = parser2contextparser : 'a parser -> 'a context_parser;

(* bah, is the same as Scan.lift *)
val _ = Scan.lift Args.cartouche_input : Input.source context_parser;

Token.is_command;
Token.content_of; (* textueller kern eines Tokens. *)

\<close>

text\<open> Tokens and Bindings \<close>  


ML\<open>
val H = @{binding here}; (* There are "bindings" consisting of a text-span and a position, 
                    where \<dieresis>positions\<dieresis> are absolute references to a file *)                                  

Binding.make: bstring * Position.T -> binding;
Binding.pos_of @{binding erzerzer};
Position.here: Position.T -> string;
(* Bindings *)
ML\<open>val X = @{here};\<close>  

\<close>  

subsection \<open>Input streams. \<close>  
ML\<open>  
  Input.source_explode : Input.source -> Symbol_Pos.T list;
     (* conclusion: Input.source_explode converts " f @{thm refl}" 
        into: 
        [(" ", {offset=14, id=-2769}), ("f", {offset=15, id=-2769}), (" ", {offset=16, id=-2769}),
        ("@", {offset=17, id=-2769}), ("{", {offset=18, id=-2769}), ("t", {offset=19, id=-2769}),
        ("h", {offset=20, id=-2769}), ("m", {offset=21, id=-2769}), (" ", {offset=22, id=-2769}),
        ("r", {offset=23, id=-2769}), ("e", {offset=24, id=-2769}), ("f", {offset=25, id=-2769}),
        ("l", {offset=26, id=-2769}), ("}", {offset=27, id=-2769})]
     *)\<close> 
  
subsection \<open>Scanning and combinator parsing. \<close> 
text\<open>Is used on two levels: 
\<^enum> outer syntax, that is the syntax in which Isar-commands are written, and 
\<^enum> inner-syntax, that is the syntax in which lambda-terms, and in particular HOL-terms were written.
\<close>
text\<open> A constant problem for newbies is this distinction, which makes it necessary that
  the " ... " quotes have to be used when switching to inner-syntax, except when only one literal
  is expected when an inner-syntax term is expected. 
\<close>

ML\<open>
Scan.peek  : ('a -> 'b -> 'c * 'd) -> 'a * 'b -> 'c * ('a * 'd);
Scan.optional: ('a -> 'b * 'a) -> 'b -> 'a -> 'b * 'a;
Scan.option: ('a -> 'b * 'a) -> 'a -> 'b option * 'a;
Scan.repeat: ('a -> 'b * 'a) -> 'a -> 'b list * 'a;
Scan.lift  : ('a -> 'b * 'c) -> 'd * 'a -> 'b * ('d * 'c);
Scan.lift (Parse.position Args.cartouche_input);
\<close>
  
text\<open> "parsers" are actually  interpreters; an 'a parser is a function that parses
   an input stream and computes(=evaluates, computes) it into 'a. 
   Since the semantics of an Isabelle command is a transition => transition 
   or theory $\Rightarrow$ theory  function, i.e. a global system transition.
   parsers of that type can be constructed and be bound as call-back functions
   to a table in the Toplevel-structure of Isar.

   The type 'a parser is already defined in the structure Token.
\<close>
  
text\<open> Syntax operations : Interface for parsing, type-checking, "reading" 
                       (both) and pretty-printing.
   Note that this is a late-binding interface, i.e. a collection of "hooks".
   The real work is done ... see below. 
   
   Encapsulates the data structure "syntax" --- the table with const symbols, 
   print and ast translations, ... The latter is accessible, e.g. from a Proof
   context via @{ML Proof_Context.syn_of}.
\<close>
  
ML\<open>
Parse.nat: int parser;  
Parse.int: int parser;
Parse.enum_positions: string -> 'a parser -> ('a list * Position.T list) parser;
Parse.enum: string -> 'a parser -> 'a list parser;
Parse.input: 'a parser -> Input.source parser;

Parse.enum : string -> 'a parser -> 'a list parser;
Parse.!!! : (T list -> 'a) -> T list -> 'a;
Parse.position: 'a parser -> ('a * Position.T) parser;

(* Examples *)                                     
Parse.position Args.cartouche_input;
\<close>

text\<open> Inner Syntax Parsing combinators for elementary Isabelle Lexems\<close>  
ML\<open>
Syntax.parse_sort : Proof.context -> string -> sort;
Syntax.parse_typ  : Proof.context -> string -> typ;
Syntax.parse_term : Proof.context -> string -> term;
Syntax.parse_prop : Proof.context -> string -> term;
Syntax.check_term : Proof.context -> term -> term;
Syntax.check_props: Proof.context -> term list -> term list;
Syntax.uncheck_sort: Proof.context -> sort -> sort;
Syntax.uncheck_typs: Proof.context -> typ list -> typ list;
Syntax.uncheck_terms: Proof.context -> term list -> term list;\<close>

text\<open>In contrast to mere parsing, the following operators provide also type-checking
     and internal reporting to PIDE --- see below. I did not find a mechanism to address
     the internal serial-numbers used for the PIDE protocol, however, rumours have it
     that such a thing exists. The variants \<^verbatim>\<open>_global\<close> work on theories instead on 
     @{ML_type "Proof.context"}s.\<close>

ML\<open>
Syntax.read_sort: Proof.context -> string -> sort;
Syntax.read_typ : Proof.context -> string -> typ;
Syntax.read_term: Proof.context -> string -> term;
Syntax.read_typs: Proof.context -> string list -> typ list;
Syntax.read_sort_global: theory -> string -> sort;
Syntax.read_typ_global: theory -> string -> typ;
Syntax.read_term_global: theory -> string -> term;
Syntax.read_prop_global: theory -> string -> term;
\<close>
text \<open>The following operations are concerned with the conversion of pretty-prints
and, from there, the generation of (non-layouted) strings.\<close>
ML\<open>
Syntax.pretty_term:Proof.context -> term -> Pretty.T;
Syntax.pretty_typ:Proof.context -> typ -> Pretty.T;
Syntax.pretty_sort:Proof.context -> sort -> Pretty.T;
Syntax.pretty_classrel: Proof.context -> class list -> Pretty.T;
Syntax.pretty_arity: Proof.context -> arity -> Pretty.T;
Syntax.string_of_term: Proof.context -> term -> string;
Syntax.string_of_typ: Proof.context -> typ -> string;
Syntax.lookup_const : Syntax.syntax -> string -> string option;
\<close>

ML\<open>
fun read_terms ctxt =
  grouped 10 Par_List.map_independent (Syntax.parse_term ctxt) #> Syntax.check_terms ctxt;
\<close>  

ML\<open>
(* More High-level, more Isar-specific Parsers *)
Args.name;
Args.const;
Args.cartouche_input: Input.source parser; 
Args.text_token: Token.T parser;

val Z = let val attribute = Parse.position Parse.name -- 
                            Scan.optional (Parse.$$$ "=" |-- Parse.!!! Parse.name) "";
        in (Scan.optional(Parse.$$$ "," |-- (Parse.enum "," attribute))) end ;
(* this leads to constructions like the following, where a parser for a *)



Thy_Output.antiquotation_pretty_source \<^binding>\<open>theory\<close> (Scan.lift (Parse.position Args.embedded));

Thy_Output.antiquotation_raw \<^binding>\<open>file\<close> (Scan.lift (Parse.position Parse.path))  ;

fn name => (Thy_Output.antiquotation_pretty_source name (Scan.lift (Parse.position Args.cartouche_input)));
\<close>


section\<open> The PIDE Framework \<close>  
subsection\<open> Markup \<close>  
text\<open> Markup Operations, and reporting. Diag in Isa\_DOF Foundations TR.
       Markup operation send via side-effect annotations to the GUI (precisely:
       to the PIDE Framework) that were used for hyperlinking applicating to binding
       occurrences, info for hovering, ... \<close>  
ML\<open>

(* Position.report is also a type consisting of a pair of a position and markup. *)
(* It would solve all my problems if I find a way to infer the defining Position.report
   from a type definition occurence ... *)

Position.report: Position.T -> Markup.T -> unit;
Position.reports: Position.report list -> unit; 
     (* ? ? ? I think this is the magic thing that sends reports to the GUI. *)
Markup.entity : string -> string -> Markup.T;
Markup.properties : Properties.T -> Markup.T -> Markup.T ;
Properties.get : Properties.T -> string -> string option;
Markup.enclose : Markup.T -> string -> string; 
     
(* example for setting a link, the def flag controls if it is a defining or a binding 
occurence of an item *)
fun theory_markup (def:bool) (name:string) (id:serial) (pos:Position.T) =
  if id = 0 then Markup.empty
  else
    Markup.properties (Position.entity_properties_of def id pos)
      (Markup.entity Markup.theoryN name);
Markup.theoryN : string;

serial();   (* A global, lock-guarded seriel counter used to produce unique identifiers,
               be it on the level of thy-internal states or as reference in markup in
               PIDE *)

(* From Theory:
fun check ctxt (name, pos) =
  let
    val thy = Proof_Context.theory_of ctxt;
    val thy' =
      Context.get_theory thy name
        handle ERROR msg =>
          let
            val completion =
              Completion.make (name, pos)
                (fn completed =>
                  map Context.theory_name (ancestors_of thy)
                  |> filter completed
                  |> sort_strings
                  |> map (fn a => (a, (Markup.theoryN, a))));
            val report = Markup.markup_report (Completion.reported_text completion);
          in error (msg ^ Position.here pos ^ report) end;
    val _ = Context_Position.report ctxt pos (get_markup thy');
  in thy' end;

fun init_markup (name, pos) thy =
  let
    val id = serial ();
    val _ = Position.report pos (theory_markup true name id pos);
  in map_thy (fn (_, _, axioms, defs, wrappers) => (pos, id, axioms, defs, wrappers)) thy end;

fun get_markup thy =
  let val {pos, id, ...} = rep_theory thy
  in theory_markup false (Context.theory_name thy) id pos end;


*)

(*
fun theory_markup def thy_name id pos =
  if id = 0 then Markup.empty
  else
    Markup.properties (Position.entity_properties_of def id pos)
      (Markup.entity Markup.theoryN thy_name);

fun get_markup thy =
  let val {pos, id, ...} = rep_theory thy
  in theory_markup false (Context.theory_name thy) id pos end;


fun init_markup (name, pos) thy =
  let
    val id = serial ();
    val _ = Position.report pos (theory_markup true name id pos);
  in map_thy (fn (_, _, axioms, defs, wrappers) => (pos, id, axioms, defs, wrappers)) thy end;


fun check ctxt (name, pos) =
  let
    val thy = Proof_Context.theory_of ctxt;
    val thy' =
      Context.get_theory thy name
        handle ERROR msg =>
          let
            val completion =
              Completion.make (name, pos)
                (fn completed =>
                  map Context.theory_name (ancestors_of thy)
                  |> filter completed
                  |> sort_strings
                  |> map (fn a => (a, (Markup.theoryN, a))));
            val report = Markup.markup_report (Completion.reported_text completion);
          in error (msg ^ Position.here pos ^ report) end;
    val _ = Context_Position.report ctxt pos (get_markup thy');
  in thy' end;


*)

\<close>

  
  
section \<open> Output: Very Low Level \<close>
ML\<open> 
Output.output; (* output is the  structure for the "hooks" with the target devices. *)
Output.output "bla_1:";
\<close>

section \<open> Output: LaTeX \<close>


ML\<open> open Thy_Output; 

 output_document: Proof.context -> {markdown: bool} -> Input.source -> Latex.text list;
 output_source: Proof.context -> string -> Latex.text list;
 present_thy: Options.T -> theory -> segment list -> Latex.text list;
 pretty_term: Proof.context -> term -> Pretty.T;
 pretty_thm: Proof.context -> thm -> Pretty.T;
 lines: Latex.text list -> Latex.text list;
 items: Latex.text list -> Latex.text list;
 isabelle: Proof.context -> Latex.text list -> Latex.text;
 isabelle_typewriter: Proof.context -> Latex.text list -> Latex.text;
 typewriter: Proof.context -> string -> Latex.text;
 verbatim: Proof.context -> string -> Latex.text;
 source: Proof.context -> Token.src -> Latex.text;
 pretty: Proof.context -> Pretty.T -> Latex.text;
 pretty_source: Proof.context -> Token.src -> Pretty.T -> Latex.text;
 pretty_items: Proof.context -> Pretty.T list -> Latex.text;
 pretty_items_source: Proof.context -> Token.src -> Pretty.T list -> Latex.text;
 antiquotation_pretty:
      binding -> 'a context_parser -> (Proof.context -> 'a -> Pretty.T) -> theory -> theory;
 antiquotation_pretty_source:
    binding -> 'a context_parser -> (Proof.context -> 'a -> Pretty.T) -> theory -> theory;
 antiquotation_raw:
    binding -> 'a context_parser -> (Proof.context -> 'a -> Latex.text) -> theory -> theory;
 antiquotation_verbatim:
      binding -> 'a context_parser -> (Proof.context -> 'a -> string) -> theory -> theory;

\<close>



ML\<open>
Syntax_Phases.reports_of_scope;
\<close>

(* STOP HERE JUNK ZONE :

(* Pretty.T, pretty-operations. *)  
ML\<open>

(* interesting piece for LaTeX Generation: 
fun verbatim_text ctxt =
  if Config.get ctxt display then
    split_lines #> map (prefix (Symbol.spaces (Config.get ctxt indent))) #> cat_lines #>
    Latex.output_ascii #> Latex.environment "isabellett"
  else
    split_lines #>
    map (Latex.output_ascii #> enclose "\\isatt{" "}") #>
    space_implode "\\isasep\\isanewline%\n";

(* From structure Thy_Output *)
fun pretty_const ctxt c =
  let
    val t = Const (c, Consts.type_scheme (Proof_Context.consts_of ctxt) c)
      handle TYPE (msg, _, _) => error msg;
    val ([t'], _) = Variable.import_terms true [t] ctxt;
  in pretty_term ctxt t' end;

  basic_entity @{binding const} (Args.const {proper = true, strict = false}) pretty_const #>

*)

Pretty.enclose : string -> string -> Pretty.T list -> Pretty.T; (* not to confuse with: String.enclose *)

(* At times, checks where attached to Pretty - functions and exceptions used to
   stop the execution/validation of a command *)
fun pretty_theory ctxt (name, pos) = (Theory.check ctxt (name, pos); Pretty.str name);
Pretty.enclose;
Pretty.str;
Pretty.mark_str;
Pretty.text "bla_d";

Pretty.quote; (* Pretty.T transformation adding " " *) 
Pretty.unformatted_string_of : Pretty.T -> string ;

Latex.output_ascii;
Latex.environment "isa" "bg";
Latex.output_ascii "a_b:c'é";
(* Note: *)
space_implode "sd &e sf dfg" ["qs","er","alpa"];


(*
fun pretty_command (cmd as (name, Command {comment, ...})) =
  Pretty.block
    (Pretty.marks_str
      ([Active.make_markup Markup.sendbackN {implicit = true, properties = [Markup.padding_line]},
        command_markup false cmd], name) :: Pretty.str ":" :: Pretty.brk 2 :: Pretty.text comment);
*)


\<close>  

ML\<open>
Thy_Output.output_text;
(* is:
fun output_text state {markdown} source =
  let
    val is_reported =
      (case try Toplevel.context_of state of
        SOME ctxt => Context_Position.is_visible ctxt
      | NONE => true);

    val pos = Input.pos_of source;
    val syms = Input.source_explode source;

    val _ =
      if is_reported then
        Position.report pos (Markup.language_document (Input.is_delimited source))
      else ();

    val output_antiquotes = map (eval_antiquote state) #> implode;

    fun output_line line =
      (if Markdown.line_is_item line then "\\item " else "") ^
        output_antiquotes (Markdown.line_content line);

    fun output_blocks blocks = space_implode "\n\n" (map output_block blocks)
    and output_block (Markdown.Par lines) = cat_lines (map output_line lines)
      | output_block (Markdown.List {kind, body, ...}) =
          Latex.environment (Markdown.print_kind kind) (output_blocks body);
  in
    if Toplevel.is_skipped_proof state then ""
    else if markdown andalso exists (Markdown.is_control o Symbol_Pos.symbol) syms
    then
      let
        val ants = Antiquote.parse pos syms;
        val reports = Antiquote.antiq_reports ants;
        val blocks = Markdown.read_antiquotes ants;
        val _ = if is_reported then Position.reports (reports @ Markdown.reports blocks) else ();
      in output_blocks blocks end
    else
      let
        val ants = Antiquote.parse pos (Symbol_Pos.trim_blanks syms);
        val reports = Antiquote.antiq_reports ants;
        val _ = if is_reported then Position.reports (reports @ Markdown.text_reports ants) else ();
      in output_antiquotes ants end
  end;
*)

\<close>  
  
  
ML\<open> 
Outer_Syntax.print_commands @{theory};

Outer_Syntax.command : Outer_Syntax.command_keyword -> string -> 
                           (Toplevel.transition -> Toplevel.transition) parser -> unit;
(* creates an implicit thy_setup with an entry for a call-back function, which happens
   to be a parser that must have as side-effect a Toplevel-transition-transition. 
   Registers "Toplevel.transition -> Toplevel.transition" parsers to the Isar interpreter.
   *)

(*Example: text is :
 
val _ =
  Outer_Syntax.command ("text", @{here}) "formal comment (primary style)"
    (Parse.opt_target -- Parse.document_source >> Thy_Output.document_command {markdown = true});
*)
 
(* not exported: Thy_Output.output_token; Ich glaub, da passierts ... *)
Thy_Output.present_thy;
\<close>  

text\<open> Even the parsers and type checkers stemming from the theory-structure are registered via
hooks (this can be confusing at times). Main phases of inner syntax processing, with standard 
implementations of parse/unparse operations were treated this way.
At the very very end in  @{file "~~/src/Pure/Syntax/syntax_phases.ML"}, it sets up the entire syntax engine 
(the hooks) via:
\<close>


(* 
val _ =
  Theory.setup
   (Syntax.install_operations
     {parse_sort = parse_sort,
      parse_typ = parse_typ,
      parse_term = parse_term false,
      parse_prop = parse_term true,
      unparse_sort = unparse_sort,
      unparse_typ = unparse_typ,
      unparse_term = unparse_term,
      check_typs = check_typs,
      check_terms = check_terms,
      check_props = check_props,
      uncheck_typs = uncheck_typs,
      uncheck_terms = uncheck_terms});
*)
  
text\<open> Thus, Syntax\_Phases does the actual work, including 
        markup generation and  generation of reports. Look at: \<close>
(*
fun check_typs ctxt raw_tys =
  let
    val (sorting_report, tys) = Proof_Context.prepare_sortsT ctxt raw_tys;
    val _ = if Context_Position.is_visible ctxt then Output.report sorting_report else ();
  in
    tys
    |> apply_typ_check ctxt
    |> Term_Sharing.typs (Proof_Context.theory_of ctxt)
  end;

which is the real implementation behind Syntax.check_typ

or:

fun check_terms ctxt raw_ts =
  let
    val (sorting_report, raw_ts') = Proof_Context.prepare_sorts ctxt raw_ts;
    val (ts, ps) = Type_Infer_Context.prepare_positions ctxt raw_ts';

    val tys = map (Logic.mk_type o snd) ps;
    val (ts', tys') = ts @ tys
      |> apply_term_check ctxt
      |> chop (length ts);
    val typing_report =
      fold2 (fn (pos, _) => fn ty =>
        if Position.is_reported pos then
          cons (Position.reported_text pos Markup.typing
            (Syntax.string_of_typ ctxt (Logic.dest_type ty)))
        else I) ps tys' [];

    val _ =
      if Context_Position.is_visible ctxt then Output.report (sorting_report @ typing_report)
      else ();
  in Term_Sharing.terms (Proof_Context.theory_of ctxt) ts' end;

which is the real implementation behind Syntax.check_term

As one can see, check-routines internally generate the markup.

*)  



Consts.the_const; (* T is a kind of signature ... *)
Variable.import_terms;
Vartab.update;

fun control_antiquotation name s1 s2 =
  Thy_Output.antiquotation name (Scan.lift Args.cartouche_input)
    (fn {state, ...} => enclose s1 s2 o Thy_Output.output_text state {markdown = false});

Output.output;

Syntax.read_input ;
Input.source_content;

(*
  basic_entity @{binding const} (Args.const {proper = true, strict = false}) pretty_const #>
*)




chapter\<open>LaTeX Document Generation\<close>  
text\<open>MORE TO COME\<close>

  
ML\<open> Thy_Output.document_command {markdown = true} \<close>  
(* Structures related to LaTeX Generation *)
ML\<open>  Latex.output_ascii;

      Latex.output_token
(* Hm, generierter output for
subsection*[Shaft_Encoder_characteristics]{ * Shaft Encoder Characteristics * } :

\begin{isamarkuptext}%
\isa{{\isacharbackslash}label{\isacharbraceleft}general{\isacharunderscore}hyps{\isacharbraceright}}%
\end{isamarkuptext}\isamarkuptrue%
\isacommand{subsection{\isacharasterisk}}\isamarkupfalse%
{\isacharbrackleft}Shaft{\isacharunderscore}Encoder{\isacharunderscore}characteristics{\isacharbrackright}{\isacharverbatimopen}\ Shaft\ Encoder\ Characteristics\ {\isacharverbatimclose}%

Generierter output for: text\<open>\label{sec:Shaft-Encoder-characteristics}\<close>

\begin{isamarkuptext}%
\label{sec:Shaft-Encoder-characteristics}%
\end{isamarkuptext}\isamarkuptrue%


*)


\<close>  
  
ML\<open>
Thy_Output.maybe_pretty_source : 
     (Proof.context -> 'a -> Pretty.T) -> Proof.context -> Token.src -> 'a list -> Pretty.T list;

Thy_Output.output: Proof.context -> Pretty.T list -> string;

 (* nuescht besonderes *)

fun document_antiq check_file ctxt (name, pos) =
  let
   (* val dir = master_directory (Proof_Context.theory_of ctxt); *)
   (* val _ = check_path check_file ctxt dir (name, pos); *)
  in
    space_explode "/" name
    |> map Latex.output_ascii
    |> space_implode (Latex.output_ascii "/" ^ "\\discretionary{}{}{}")
    |> enclose "\\isatt{" "}"
  end;

\<close>

ML\<open> 

Thy_Output.output_text: Toplevel.state -> {markdown: bool} -> Input.source -> string;
Thy_Output.document_command;

Thy_Output.document_command : {markdown: bool} -> (xstring * Position.T) option * Input.source ->
    Toplevel.transition -> Toplevel.transition;
    (*  fun document_command markdown (loc, txt) =
            Toplevel.keep (fn state =>
               (case loc of
                   NONE => ignore (output_text state markdown txt)
                         | SOME (_, pos) =>
                   error ("Illegal target specification -- not a theory context" ^ Position.here pos))) o
             Toplevel.present_local_theory loc (fn state => ignore (output_text state markdown txt));

    *)

Thy_Output.output_text : Toplevel.state -> {markdown: bool} -> Input.source -> string ; 
                         (* this is where antiquotation expansion happens : uses eval_antiquote *)


Thy_Output.document_command : {markdown: bool} -> (xstring * Position.T) option * Input.source ->
    Toplevel.transition -> Toplevel.transition;
    (*  fun document_command markdown (loc, txt) =
            Toplevel.keep (fn state =>
               (case loc of
                   NONE => ignore (output_text state markdown txt)
                         | SOME (_, pos) =>
                   error ("Illegal target specification -- not a theory context" ^ Position.here pos))) o
             Toplevel.present_local_theory loc (fn state => ignore (output_text state markdown txt));

    *)

Thy_Output.output_text : Toplevel.state -> {markdown: bool} -> Input.source -> string ; 
                         (* this is where antiquotation expansion happens : uses eval_antiquote *)

*)
(* stuff over global environment : *)
(*
ML\<open> Document.state();\<close>
ML\<open> Session.get_keywords(); (* this looks to be really session global. *)
    Outer_Syntax.command; \<close>
ML\<open> Thy_Header.get_keywords @{theory};(* this looks to be really theory global. *) \<close>
*)


section\<open>Inner Syntax\<close>
text\<open>MORE TO COME\<close>
ML\<open>Sign.add_trrules\<close>


section*[c::conclusion]\<open>Conclusion\<close>
text\<open>More to come\<close>
section*[bib::bibliography]\<open>Bibliography\<close>

(*<*)
close_monitor*[this] 
check_doc_global
(*>*)
end
