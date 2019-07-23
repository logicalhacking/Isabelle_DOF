(*<*)
theory TR_MyCommentedIsabelle
  imports "Isabelle_DOF.technical_report" 
   (*imports "../../../ontologies/technical_report"*)
begin
 

open_monitor*[this::report] 
(*>*)

title*[tit::title]\<open>My Personal, Ecclectic Isabelle Programming Manual\<close> 
subtitle*[stit::subtitle]\<open>Version : Isabelle 2019\<close>
text*[bu::author,     
      email       = "''wolff@lri.fr''",
      affiliation = "\<open>Université Paris-Saclay, LRI, France\<close>"]\<open>Burkhart Wolff\<close>
    

text*[abs::abstract,
      keywordlist="[''LCF-Architecture'',''Isabelle'',''SML'',''PIDE'',''Programming Guide'',
                    ''Tactic Programming'']"]\<open>
  While Isabelle is mostly known as part of Isabelle/HOL (an interactive 
  theorem prover), it actually provides a system framework for developing a wide
  spectrum of applications. A particular strength of the Isabelle framework is the 
  combination of text editing, formal verification, and code generation. 
  
  This is a programming-tutorial of Isabelle and Isabelle/HOL, a complementary
  text to the unfortunately somewhat outdated "The Isabelle Cookbook" in
  \url{https://nms.kcl.ac.uk/christian.urban/Cookbook/}. The reader is encouraged
  not only to consider the generated .pdf, but also consult the loadable version in Isabelle/jEdit
  @{cite "DBLP:journals/corr/Wenzel14"}in order to make experiments on the running code.
  
  This text is written itself in Isabelle/Isar using a specific document ontology
  for technical reports. It is intended to be a "living document", i.e. it is not only
  used for generating a static, conventional .pdf, but also for direct interactive 
  exploration in Isabelle/jedit. This way, types, intermediate results of computations and
  checks can be repeated by the reader who is invited to interact with this document.
  Moreover, the textual parts have been enriched with a maximum of formal content
  which makes this text re-checkable at each load and easier maintainable.
\<close>

chapter*[intro::introduction]\<open> Introduction  \<close>    

text\<open> While Isabelle @{cite "DBLP:books/sp/NipkowPW02"} is mostly known as part of Isabelle/HOL 
  (an interactive theorem prover), it actually provides a system framework for developing a wide 
  spectrum of applications. A particular strength of the Isabelle framework is the combination 
  of text editing, formal verification, and code generation. This is a programming-tutorial of 
  Isabelle and Isabelle/HOL, a complementary text to the unfortunately somewhat outdated 
  "The Isabelle Cookbook" in \<^url>\<open>https://nms.kcl.ac.uk/christian.urban/Cookbook/\<close>. The reader 
  is encouraged not only to consider the generated .pdf, but also consult the loadable version 
  in Isabelle/jedit in order to make experiments on the running code. This text is written 
  itself in Isabelle/Isar using a specific document ontology for technical reports. It is 
  intended to be a "living document", i.e. it is not only used for generating a static, 
  conventional .pdf, but also for direct interactive exploration in Isabelle/jedit. This way, 
  types, intermediate results of computations and checks can be repeated by the reader who is 
  invited to interact with this document. Moreover, the textual parts have been enriched with a 
  maximum of formal content which makes this text re-checkable at each load and easier 
  maintainable.\<close>

figure*[architecture::figure,relative_width="80",src="''figures/isabelle-architecture''"]\<open> 
     The system architecture of Isabelle (left-hand side) and the 
     asynchronous communication between the Isabelle system and 
     the IDE (right-hand side). \<close>

text\<open>This cookbook roughly follows the Isabelle system architecture shown in 
  @{figure "architecture"}, and, to be more precise, more or less in the bottom-up order.

  We start from the basic underlying SML platform over the Kernels to the tactical layer 
  and end with a discussion over the front-end technologies.
\<close>

chapter*[t1::technical]\<open> SML and Fundamental SML libraries  \<close>    

section*[t11::technical] "ML, Text and Antiquotations"

text\<open>Isabelle is written in SML, the "Standard Meta-Language", which is is an impure functional 
  programming language allowing, in principle, mutable variables and side-effects. 
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
  code-base @{cite "DBLP:conf/mkm/BarrasGHRTWW13"}.
  The preferred programming style is purely functional: \<close>

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
        \<open>A text-element as presented in Isabelle/jedit.\<close>

text\<open> text-commands, ML- commands (and in principle any other command) can be seen as 
  \<^emph>\<open>quotations\<close> over the underlying SML environment (similar to OCaml or Haskell).
  Linking these different sorts of quotations with each other and the underlying SML-envirnment
  is supported via \<^emph>\<open>antiquotations\<close>'s. Generally speaking, antiquotations are a programming 
  technique to specify expressions or patterns in a quotation, parsed in the context of the 
  enclosing expression or pattern where the quotation is. Another way to understand this concept:
  anti-quotations are "semantic macros" that produce a value for the surrounding context
  (ML, text, HOL, whatever) depending on local arguments and the underlying logical context.
  
  The way an antiquotation is specified depends on the quotation expander: typically a specific 
  character and an identifier, or specific parentheses and a complete expression or pattern.\<close>

text\<open> In Isabelle documentations, antiquotation's were heavily used to enrich literate explanations
  and documentations by "formal content", i.e. machine-checked, typed references
  to all sorts of entities in the context of the interpreting environment. 
  Formal content allows for coping with sources that rapidly evolve and were developed by 
  distributed teams as is typical in open-source developments. 
  A paradigmatic example for antiquotation in Texts and Program snippets is here:\<close>

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

text\<open>The bootstrapping sequence is also reflected in the following diagram @{figure "architecture"}.\<close>


section*[t12::technical] "Elements of the SML library";  
text\<open>Elements of the @{file "$ISABELLE_HOME/src/Pure/General/basics.ML"} SML library
  are basic exceptions. Note that exceptions should be catched individually, uncatched exceptions 
  except those generated by the specific "error" function are discouraged in Isabelle
  source programming since they might produce races. Finally, a number of commonly
  used "squigglish" combinators is listed:\<close>

ML\<open>   Bind      : exn;
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
      exnMessage : exn -> string ;\<close>

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


subsection*[t213::example]\<open>Mechanism 2 : Extending the Global Context $\theta$ by User Data \<close>

text\<open>A central mechanism for constructing user-defined data is by the \<^verbatim>\<open>Generic_Data\<close> SML functor.
  A plugin needing some data \<^verbatim>\<open>T\<close> and providing it with implementations for an 
  \<^verbatim>\<open>empty\<close>, and operations  \<^verbatim>\<open>merge\<close> and \<^verbatim>\<open>extend\<close>, can construct a lense with operations
  \<^verbatim>\<open>get\<close> and \<^verbatim>\<open>put\<close> that attach this data into the generic system context. Rather than using
  unsynchronized SML mutable variables, this is the mechanism to introduce component local
  data in Isabelle, which allows to manage this data for the necessary backtrack- and synchronization
  features in the pervasively parallel evaluation framework that Isabelle as a system represents.\<close>

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


section*[lcfk::technical]\<open>  The LCF-Kernel: terms, types, theories, proof\_contexts, thms \<close>  
text\<open>The classical LCF-style \<^emph>\<open>kernel\<close> is about 
\<^enum> Types and terms of a typed $\lambda$-Calculus including constant symbols,
  free variables, $\lambda$-binder and application,
\<^enum> An infrastructure to define types and terms, a \<^emph>\<open>signature\<close>,
  that also assigns to constant symbols types
\<^enum> An abstract type of \<^emph>\<open>theorem\<close> and logical operations on them
\<^enum> (Isabelle specific): a notion of \<^emph>\<open>theory\<close>, i.e. a container 
  providing a signature and set (list) of theorems.   
\<close>


subsection*[termstypes::technical]\<open> Terms and Types \<close>
text \<open>A basic data-structure of the kernel is @{file "$ISABELLE_HOME/src/Pure/term.ML"} \<close>  
ML\<open> (* open Term; *)
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
  operators of the HOL logic specific constructors and destructors:\<close>

ML\<open>
   HOLogic.boolT         : typ;
   HOLogic.mk_Trueprop   : term -> term; (* the embedder of bool to prop fundamenyal for HOL *)
   HOLogic.dest_Trueprop : term -> term; 
   HOLogic.Trueprop_conv : conv -> conv;
   HOLogic.mk_setT       : typ -> typ;   (* ML level type constructor set *)
   HOLogic.dest_setT     : typ -> typ;
   HOLogic.Collect_const : typ -> term;
   HOLogic.mk_Collect    : string * typ * term -> term;
   HOLogic.mk_mem        : term * term -> term;
   HOLogic.dest_mem      : term -> term * term;
   HOLogic.mk_set        : typ -> term list -> term;
   HOLogic.conj_intr     : Proof.context -> thm -> thm -> thm; (* some HOL-level derived-inferences *)
   HOLogic.conj_elim     : Proof.context -> thm -> thm * thm;
   HOLogic.conj_elims    : Proof.context -> thm -> thm list;
   HOLogic.conj          : term;         (* some ML level logical constructors *)
   HOLogic.disj          : term;
   HOLogic.imp           : term;
   HOLogic.Not           : term;
   HOLogic.mk_not        : term -> term;
   HOLogic.mk_conj       : term * term -> term;
   HOLogic.dest_conj     : term -> term list;
   HOLogic.conjuncts     : term -> term list;
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
  other, yields false:\<close>

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

ML\<open> val t_schematic = Type("List.list",[TVar(("'a",0),@{sort "HOL.type"})]); \<close>

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

text*[exo4::example]\<open> Example:\<close> 
ML\<open>val t = generalize_term @{term "[]"}\<close>

text\<open>Now we turn to the crucial issue of type-instantiation and with a given type environment
  @{ML "tyenv"}. For this purpose, one has to switch to the low-level interface 
  @{ML_structure "Term_Subst"}. \<close>

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

text\<open>A more abstract env for variable management in tactic proofs. A bit difficult to use
  outside the very closed-up tracks of conventional use...\<close>

ML\<open> Consts.the_const; (* T is a kind of signature ... *)
    Variable.import_terms;
    Vartab.update;\<close>

subsection*[t232::technical]\<open> Type-Inference (= inferring consistent type information if possible) \<close>

text\<open> Type inference eliminates also joker-types such as @{ML dummyT} and produces
       instances for schematic type variables where necessary. In the case of success,
       it produces a certifiable term. \<close>  
ML\<open>  Type_Infer_Context.infer_types: Proof.context -> term list -> term list \<close>

subsection*[t237::technical]\<open>Constructing Terms without Type-Inference\<close>
text\<open>Using @{ML "Type_Infer_Context.infer_types"} is not quite unproblematic: since the type
inference can construct types for largely underspecified terms, it may happen that under 
some circumstances, tactics and proof-attempts fail since just some internal term representation
was too general. A more defensive strategy is already sketched --- but neither explicitely 
mentioned nor worked out in the interface in @{ML_structure HOLogic}. The idea is to have
advanced term constructors that construct the right term from the leaves, which were by convention
fully type-annotated (so: this does not work for terms with dangling @(ML Bound)'s).

Operations like  @{ML "HOLogic.mk_prod"} or @{ML "HOLogic.mk_fst"}  or  @{ML "HOLogic.mk_eq"} do
exactly this by using an internal pure bottom-up type-inference  @{ML "fastype_of"}.
The following routines are written in the same style complement the existing API
@{ML_structure HOLogic}.
\<close>

ML\<open>
fun mk_None ty = let val none = \<^const_name>\<open>Option.option.None\<close>
                     val none_ty = ty --> Type(\<^type_name>\<open>option\<close>,[ty])
                in  Const(none, none_ty)
                end;
fun mk_Some t = let val some = \<^const_name>\<open>Option.option.Some\<close> 
                    val ty = fastype_of t
                    val some_ty = ty --> Type(\<^type_name>\<open>option\<close>,[ty])
                in  Const(some, some_ty) $  t
                end;

fun  mk_undefined (@{typ "unit"}) = Const (\<^const_name>\<open>Product_Type.Unity\<close>, \<^typ>\<open>unit\<close>)
    |mk_undefined t               = Const (\<^const_name>\<open>HOL.undefined\<close>, t)

fun meta_eq_const T = Const (\<^const_name>\<open>Pure.eq\<close>, T --> T --> propT);

fun mk_meta_eq (t, u) = meta_eq_const (fastype_of t) $ t $ u;

\<close>

subsection*[t233::technical]\<open> Theories and the Signature API\<close>  
ML\<open>
Sign.tsig_of : theory -> Type.tsig;
Sign.syn_of  : theory -> Syntax.syntax;
Sign.of_sort : theory -> typ * sort -> bool ;
\<close>

subsection*[t234::technical]\<open>Thm's and the LCF-Style, "Mikro"-Kernel \<close>  
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


subsection*[t235::technical]\<open> Theories \<close>

text \<open> This structure yields the datatype \verb*thy* which becomes the content of 
  \verb*Context.theory*. In a way, the LCF-Kernel registers itself into the Nano-Kernel,
  which inspired me (bu) to this naming. \<close>

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
Theory.end_theory: theory -> theory;\<close>

section*[t26::technical]\<open>Advanced Specification Constructs\<close>
text\<open>Isabelle is built around the idea that system components were built on top
of the kernel in order to give the user high-level specification constructs 
--- rather than inside as in the Coq kernel that foresees, for example, data-types
and primitive recursors already in the basic $\lambda$-term language.
Therefore, records, definitions, type-definitions, recursive function definitions
are supported by packages that belong to the \<^emph>\<open>components\<close> strata. 
With the exception of the @{ML "Specification.axiomatization"} construct, they
are all-together built as composition of conservative extensions.

The components are a bit scattered in the architecture. A relatively recent and
high-level component (more low-level components such as @{ML "Global_Theory.add_defs"}
exist) for definitions and axiomatizations is here:
\<close>


ML\<open>
local open Specification
  val _= definition: (binding * typ option * mixfix) option ->
        (binding * typ option * mixfix) list -> term list -> Attrib.binding * term ->
        local_theory -> (term * (string * thm)) * local_theory
  val _= definition': (binding * typ option * mixfix) option ->
        (binding * typ option * mixfix) list ->  term list -> Attrib.binding * term ->
        bool -> local_theory -> (term * (string * thm)) * local_theory
  val _= definition_cmd: (binding * string option * mixfix) option ->
        (binding * string option * mixfix) list -> string list -> Attrib.binding * string ->
         bool -> local_theory -> (term * (string * thm)) * local_theory
  val _= axiomatization: (binding * typ option * mixfix) list ->
        (binding * typ option * mixfix) list -> term list ->
        (Attrib.binding * term) list -> theory -> (term list * thm list) * theory
  val _= axiomatization_cmd: (binding * string option * mixfix) list ->
        (binding * string option * mixfix) list -> string list ->
        (Attrib.binding * string) list -> theory -> (term list * thm list) * theory
  val _= axiom: Attrib.binding * term -> theory -> thm * theory
  val _= abbreviation: Syntax.mode -> (binding * typ option * mixfix) option ->
        (binding * typ option * mixfix) list -> term -> bool -> local_theory -> local_theory
  val _= abbreviation_cmd: Syntax.mode -> (binding * string option * mixfix) option ->
        (binding * string option * mixfix) list -> string -> bool -> local_theory -> local_theory
in val _ = () end
\<close>

text\<open>Note that the interface is mostly based on @{ML_type "local_theory"}, which is a synonym to
@{ML_type "Proof.context"}. Need to lift this to a global system transition ?
Don't worry, @{ML "Named_Target.theory_map: (local_theory -> local_theory) -> theory -> theory"} 
does the trick.
\<close>

subsection*[t261::example]\<open>Example\<close>

text\<open>Suppose that we want do  \<open>definition I :: "'a \<Rightarrow> 'a" where "I x = x"\<close> at the ML-level.
We construct our defining equation and embed it as a @{typ "prop"} into Pure.
\<close>
ML\<open> val ty = @{typ "'a"}
    val term = HOLogic.mk_eq (Free("I",ty -->ty) $ Free("x", ty), Free("x", ty));
    val term_prop = HOLogic.mk_Trueprop term\<close>
text\<open>Recall the notes on defensive term construction wrt. typing in @{docitem "t237"}.
Then the trick is done by:\<close>

setup\<open>
let
fun mk_def name p  = 
    let val nameb =  Binding.make(name,p)
        val ty_global = ty --> ty
        val args = (((SOME(nameb,SOME ty_global,NoSyn),(Binding.empty_atts,term_prop)),[]),[])
        val cmd = (fn (((decl, spec), prems), params) =>
                        #2 oo Specification.definition' decl params prems spec)
    in cmd args true
    end;
in  Named_Target.theory_map (mk_def "I" @{here} )
end\<close>

thm I_def
text\<open>Voilà.\<close>

section*[t24::technical]\<open>Backward Proofs: Tactics, Tacticals and Goal-States\<close>

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
  The following is an excerpt of @{file "~~/src/Pure/tactical.ML"}:\<close>

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
  @{file "~~/src/Pure/tactic.ML"} looks as follows:\<close>

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


section*[goalp::technical]\<open>The classical goal package\<close>
text\<open>The main mechanism in Isabelle as an LCF-style system is to produce @{ML_type thm}'s 
  in backward-style via tactics as described in @{technical "t24"}. Given a context
  --- be it global as @{ML_type theory} or be it inside a proof-context as @{ML_type Proof.context},
  user-programmed verification of (type-checked) terms or just strings can be done via the 
  operations:\<close>


ML\<open>
Goal.prove_internal : Proof.context -> cterm list -> cterm -> (thm list -> tactic) -> thm;

Goal.prove_global :  theory -> string list -> term list -> term -> 
                   ({context: Proof.context, prems: thm list} -> tactic) -> thm;
(* ... and many more variants. *)
\<close>

subsection*[ex211::example]\<open>Proof Example\<close>

text\<open>The proof:\<close>

lemma "(10::int) + 2 = 12" by simp

text\<open>... represents itself at the SML interface as follows:\<close>

ML\<open>val tt = HOLogic.mk_Trueprop (Syntax.read_term @{context} "(10::int) + 2 = 12");
         (* read_term parses and type-checks its string argument;
            HOLogic.mk_Trueprop wraps the embedder from @{ML_type "bool"} to  
            @{ML_type "prop"} from Pure. *)

val thm1 = Goal.prove_global @{theory}                         (* global context *)
                             []                                (* name ? *)
                             []                                (* local assumption context *)
                             (tt)                              (* parsed goal *)
                             (fn _ => simp_tac  @{context} 1)  (* proof tactic *)\<close>               


section\<open>The Isar Engine\<close>

text\<open>The main structure of the Isar-engine is @{ ML_structure Toplevel} and provides and
internal @{ ML_type state} with the necessary infrastructure --- 
i.e. the operations to pack and unpack theories and Proof.contexts  --- on it:
\<close>
ML\<open> 
    Toplevel.theory_toplevel: theory -> Toplevel.state;
    Toplevel.init_toplevel: unit -> Toplevel.state;
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
    (* ... *) \<close>

text\<open> The extensibility of Isabelle as a system framework depends on a number of tables,
  into which various concepts commands, ML-antiquotations, text-antiquotations, cartouches, ...
  can be entered via a late-binding on the fly. 
 
  A paradigmatic example is the @{ML "Outer_Syntax.command"}-operation, which ---
  representing in itself a toplevel system transition --- allows to define a new 
  command section and bind its syntax and semantics at a specific keyword.
  Calling @{ML "Outer_Syntax.command"} 
  creates an implicit  @{ML Theory.setup}  with an entry for a call-back function, which happens
  to be a parser that must have as side-effect a Toplevel-transition-transition. 
  Registers @{ML_type "Toplevel.transition -> Toplevel.transition"} parsers to the 
  Isar interpreter.\<close>


ML\<open> Outer_Syntax.command : Outer_Syntax.command_keyword -> string -> 
                           (Toplevel.transition -> Toplevel.transition) parser -> unit;\<close>

text\<open>A paradigmatic example: "text" is defined by: \<close>

(* --- commented out since this code is not re-executable
val _ =
  Outer_Syntax.command ("text", @{here}) "formal comment (primary style)"
    (Parse.opt_target -- Parse.document_source >> Thy_Output.document_command {markdown = true});
*)
 

text\<open>Here are a few queries relevant for the global config of the isar engine:\<close>
ML\<open> Document.state();\<close>
ML\<open> Session.get_keywords(); (* this looks to be really session global. *) \<close>
ML\<open> Thy_Header.get_keywords @{theory};(* this looks to be really theory global. *) \<close>




subsection*[transmgt::technical] \<open>Transaction Management in the Isar-Engine : The Toplevel \<close>
  
ML\<open>Toplevel.exit: Toplevel.transition -> Toplevel.transition;
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
  
        fun theory f = theory' (K f); *)\<close>  
  
  
ML\<open>

(* Isar Toplevel Control *)
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
  
  
subsection*[conf::technical]\<open> Configuration flags of fixed type in the Isar-engine. \<close>
text\<open>The toplevel also provides an infrastructure for managing configuration options 
  for system components. Based on a sum-type @{ML_type Config.value } 
  with the alternatives \<^verbatim>\<open> Bool of bool | Int of int | Real of real | String of string\<close>
  and building the parametric configuration types @{ML_type "'a Config.T" } and the
  instance  \<^verbatim>\<open>type raw = value T\<close>, for all registered configurations the protocol:\<close>
ML\<open>
  Config.get: Proof.context -> 'a Config.T -> 'a;
  Config.map: 'a Config.T -> ('a -> 'a) -> Proof.context -> Proof.context;
  Config.put: 'a Config.T -> 'a -> Proof.context -> Proof.context;
  Config.get_global: theory -> 'a Config.T -> 'a;
  Config.map_global: 'a Config.T -> ('a -> 'a) -> theory -> theory;
  Config.put_global: 'a Config.T -> 'a -> theory -> theory;\<close>

text\<open>... etc. is defined.\<close>

text\<open>Example registration of an config attribute XS232: \<close>
ML\<open>
val (XS232, XS232_setup)
     = Attrib.config_bool \<^binding>\<open>XS232\<close> (K false);

val _ = Theory.setup XS232_setup;\<close>

(* or: just command:

setup\<open>XS232_setup\<close>

*)

text\<open>Another mechanism are global synchronised variables:\<close>
ML\<open> (* For example *)
           
  val C = Synchronized.var "Pretty.modes" "latEEex"; 
  (* Synchronized: a mechanism to bookkeep global
     variables with synchronization mechanism included *)
  Synchronized.value C;\<close>  
  
chapter*[frontend::technical]\<open>Front-End \<close>  
text\<open>In the following chapter, we turn to the right part of the system architecture 
  shown in @{docitem \<open>architecture\<close>}: 
  The PIDE ("Prover-IDE") layer @{cite "DBLP:conf/itp/Wenzel14"}
  consisting of a part written in SML and another in SCALA.
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
\<^enum> an Eclipse plugin (developped by an Edinburg-group, based on an very old PIDE version),
\<^enum> a Visual-Studio Code plugin (developed by Makarius Wenzel), 
  currently based on a fairly old PIDE version, 
\<^enum> clide, a web-client supporting javascript and HTML5
  (developed by a group at University Bremen, based on a very old PIDE version), and 
\<^enum> the most commonly used: the plugin in JEdit - Editor,
  (developed by Makarius Wenzel, current PIDE version.)\<close>

text\<open>The document model forsees a number of text files, which are organized in form of an 
  acyclic graph. Such graphs can be grouped into \<^emph>\<open>sessions\<close> and "frozen" to binaries in order 
  to avoid long compilation times. Text files have an abstract name serving as identity (the 
  mapping to file-paths in an underlying file-system is done in an own build management).
  The primary format of the text files is \<^verbatim>\<open>.thy\<close> (historically for: theory),
  secondary formats can be \<^verbatim>\<open>.sty\<close>,\<^verbatim>\<open>.tex\<close>, \<^verbatim>\<open>.png\<close>, \<^verbatim>\<open>.pdf\<close>, or other files processed 
  by Isabelle and listed in a configuration processed by the build system.\<close>

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
  and allows for user-programmed extensions.\<close>

text\<open>In the traditional literature, Isabelle \<^verbatim>\<open>.thy\<close>-files were 
  were said to be processed by processed by two types of parsers:
\<^enum> the "outer-syntax" (i.e. the syntax for commands) is processed 
  by a lexer-library and parser combinators built on top, and
\<^enum> the "inner-syntax" (i.e. the syntax for @{term \<open>\<Lambda>\<close>} - terms) 
  with an evolved, eight-layer parsing and pretty-printing process
  based on an Early-algorithm.
\<close>

text\<open>This picture is less and less true for a number of reasons:
\<^enum> With the advent of \<open>(\<open>)... (\<close>)\<close>, a mechanism for
  \<^emph>\<open>cascade-syntax\<close> came to the Isabelle platform that introduce a flexible means
  to change parsing contexts \<^emph>\<open>and\<close> parsing technologies. 
\<^enum> Inside the term-parser levels, the concept of \<^emph>\<open>cartouche\<close> can be used 
  to escape the parser and its underlying parsing technology.
\<^enum> Outside, in the traditional toplevel-parsers, the 
  \<open>(\<open>)... (\<close>)\<close> is becoming more and more enforced
  (some years ago, syntax like \<open>term{* ... *}\<close> was replaced by 
   syntax \<open>term(\<open>)... (\<close>)\<close>. This makes technical support of cascade syntax
   more and more easy.
\<^enum> The Lexer infra-structure is already rather generic; nothing prevents to
  add beside the lexer - configurations for ML-Parsers, Toplevel Command Syntax 
  parsers, mathematical notation parsers for $\lambda$-terms new pillars
  of parsing technologies, say, for parsing C or Rust or JavaScript inside 
  Isabelle.
\<close>


section\<open>Basics: string, bstring and xstring\<close>
text\<open>@{ML_type "string"} is the basic library type from the SML library
  in structure @{ML_structure "String"}. Many Isabelle operations produce
  or require formats thereof introduced as type synonyms 
  @{ML_type "bstring"} (defined in structure @{ML_structure "Binding"}
  and @{ML_type "xstring"} (defined in structure @{ML_structure "Name_Space"}.
  Unfortunately, the abstraction is not tight and combinations with 
  elementary routines might produce quite crappy results.\<close>

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
writeln ("And a link to the declaration of 'here' is "^markup)\<close> 

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
  annotation data which is part of the protocol sent from Isabelle to the front-end.
  They are qualified as "quasi-abstract", which means they are intended to be an abstraction of 
  the serialized, textual presentation of the protocol. Markups are structurally a pair of a key
  and properties; @{ML_structure Markup} provides a number of of such \<^emph>\<open>key\<close>s for annotation classes
  such as "constant", "fixed", "cartouche", some of them quite obscure. Here is a code sample
  from \<^theory_text>\<open>Isabelle_DOF\<close>. A markup must be tagged with an id; this is done by the @{ML serial}-function
  discussed earlier. Markup Operations, were used for hyperlinking applications to binding
  occurrences, info for hovering, infors for type ... \<close>  
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
\<close>



subsection\<open>A simple Example\<close>
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


subsection\<open>A Slightly more Complex Example\<close>

ML \<open>

fun markup_tvar def_name ps (name, id) =
  let 
    fun markup_elem name = (name, (name, []): Markup.T);
    val (tvarN, tvar) = markup_elem ((case def_name of SOME name => name | _ => "") ^ "'s nickname is");
    val entity = Markup.entity tvarN name
    val def = def_name = NONE
  in
    tvar ::
    (if def then I else cons (Markup.keyword_properties Markup.ML_keyword3))
      (map (fn pos => Markup.properties (Position.entity_properties_of def id pos) entity) ps)
  end

fun report [] _ _ = I
  | report ps markup x =
      let val ms = markup x
      in fold (fn p => fold (fn m => cons ((p, m), "")) ms) ps end
\<close>

ML \<open>
local
val data = \<comment> \<open>Derived from Yakoub's example ;-)\<close>

  [ (\<open>Frédéric 1er\<close>,  \<open>King of Naples\<close>)
  , (\<open>Frédéric II\<close>,   \<open>King of Sicily\<close>)
  , (\<open>Frédéric III\<close>,  \<open>the Handsome\<close>)
  , (\<open>Frédéric IV\<close>,   \<open>of the Empty Pockets\<close>)
  , (\<open>Frédéric V\<close>,    \<open>King of Denmark–Norway\<close>)
  , (\<open>Frédéric VI\<close>,   \<open>the Knight\<close>)
  , (\<open>Frédéric VII\<close>,  \<open>Count of Toggenburg\<close>)
  , (\<open>Frédéric VIII\<close>, \<open>Count of Zollern\<close>)
  , (\<open>Frédéric IX\<close>,   \<open>the Old\<close>)
  , (\<open>Frédéric X\<close>,    \<open>the Younger\<close>) ]

val (tab0, markup) =
  fold_map (fn (name, msg) => fn reports =>
             let val id = serial ()
                 val pos = [Input.pos_of name]
             in 
                ( (fst(Input.source_content msg), (name, pos, id))
                , report pos (markup_tvar NONE pos) (fst(Input.source_content name), id) reports)
             end)
           data
           []

val () = Position.reports_text markup
in
val tab = Symtab.make tab0
end
\<close>

ML \<open>
val _ =
  fold (fn input =>
        let
          val pos1' = Input.pos_of input
          fun ctnt name0  = fst(Input.source_content name0)
          val pos1 = [pos1']
          val msg1 = fst(Input.source_content input)
          val msg2 = "No persons were found to have such nickname"
        in
          case Symtab.lookup tab (fst(Input.source_content input)) of
            NONE => tap (fn _ => Output.information (msg2 ^ Position.here_list pos1))
                        (cons ((pos1', Markup.bad ()), ""))
          | SOME (name0, pos0, id) => report pos1 (markup_tvar (SOME (ctnt name0)) pos0) (msg1, id)
        end)
      [ \<open>the Knight\<close>   \<comment> \<open>Example of a correct retrieval (CTRL + Hovering shows what we are expecting)\<close>
      , \<open>the Handsome\<close> \<comment> \<open>Example of a correct retrieval (CTRL + Hovering shows what we are expecting)\<close>
      , \<open>the Spy\<close>      \<comment> \<open>Example of a failure to retrieve the person in \<^ML>\<open>tab\<close>\<close>
 ]
      []
  |> Position.reports_text
\<close>

text\<open>The pudding comes with the eating: \<close>

subsection\<open>Environment Structured Reporting\<close>

text\<open> The structure @{ML_structure \<open>Name_Space\<close>} offers an own infra-structure for names and
      manages the markup accordingly.  MORE TO COME\<close>
text\<open> @{ML_type "'a Name_Space.table"} \<close>


section\<open> The System Lexer and Token Issues\<close>
text\<open>Four syntactic contexts are predefined in Isabelle (others can be added): 
  the ML context, the text context, the Isar-command context and the teerm-context, referring
  to different needs of the Isabelle Framework as an extensible framework supporting incremental,
  partially programmable extensions and as a Framework geared towards Formal Proofs and therefore
  mathematical notations. The basic data-structure for the lexical treatment of these elemens
  are @{ML_structure "Token"}'s. \<close>

subsection\<open>Tokens\<close>

text\<open>The basic entity that lexers treat are \<^emph>\<open>tokens\<close>. defined in @{ML_structure "Token"}
  It provides a classification infrastructure, the references to positions and Markup 
  as well as way's to annotate tokens with (some) values they denote:\<close>

ML\<open>
local
  open Token 

  type dummy = Token.T
  type src = Token.T list
  type file = {src_path: Path.T, lines: string list, digest: SHA1.digest, pos: Position.T}

  type name_value = {name: string, kind: string, print: Proof.context -> Markup.T * xstring}


  val _ = Token.is_command : Token.T -> bool;
  val _ = Token.content_of : Token.T -> string; (* textueller kern eines Tokens. *)


  val _ = pos_of: T -> Position.T

(*
datatype kind =
    (*immediate source*)
    Command | Keyword | Ident | Long_Ident | Sym_Ident | Var | Type_Ident | Type_Var | Nat |
    Float | Space |
    (*delimited content*)
    String | Alt_String | Verbatim | Cartouche | Comment of Comment.kind option |
    (*special content*)
    Error of string | EOF

 datatype value =
    Source of src |
    Literal of bool * Markup.T |
    Name of name_value * morphism |
    Typ of typ |
    Term of term |
    Fact of string option * thm list |
    Attribute of morphism -> attribute |
    Declaration of declaration |
    Files of file Exn.result list


*)
in val _ = ()
end
\<close>



subsection\<open>A Lexer Configuration Example\<close>

ML\<open>
(* MORE TO COME *)
\<close>


section\<open> Combinator Parsing \<close>  
text\<open>Parsing Combinators go back to monadic programming as advocated by Wadler et. al, and has been 
  worked out @{cite "DBLP:journals/jfp/Hutton92"}. Parsing combinators are one of the two
  major parsing technologies of the Isabelle front-end, in particular for the outer-syntax used
  for the parsing of toplevel-commands. The core of the combinator library is 
  @{ML_structure \<open>Scan\<close>} providing the @{ML_type "'a parser"} which is a synonym for
  @{ML_type " Token.T list -> 'a * Token.T list"}. 
  
   "parsers" are actually  interpreters; an 'a parser is a function that parses
  an input stream and computes(=evaluates, computes) it into 'a. 
  Since the semantics of an Isabelle command is a transition => transition 
  or theory $\Rightarrow$ theory  function, i.e. a global system transition.
  parsers of that type can be constructed and be bound as call-back functions
  to a table in the Toplevel-structure of Isar.
  
  The library also provides a bunch of infix parsing combinators, notably:\<close>

ML\<open>
  val _ = op !! : ('a * message option -> message) -> ('a -> 'b) -> 'a -> 'b
               (*apply function*)
  val _ = op >> : ('a -> 'b * 'c) * ('b -> 'd) -> 'a -> 'd * 'c
  (*alternative*)
  val _ = op || : ('a -> 'b) * ('a -> 'b) -> 'a -> 'b
  (*sequential pairing*)
  val _ = op -- : ('a -> 'b * 'c) * ('c -> 'd * 'e) -> 'a -> ('b * 'd) * 'e
  (*dependent pairing*)
  val _ = op :-- : ('a -> 'b * 'c) * ('b -> 'c -> 'd * 'e) -> 'a -> ('b * 'd) * 'e
  (*projections*)
  val _ = op :|-- : ('a -> 'b * 'c) * ('b -> 'c -> 'd * 'e) -> 'a -> 'd * 'e
  val _ = op |-- : ('a -> 'b * 'c) * ('c -> 'd * 'e) -> 'a -> 'd * 'e
  val _ = op --| : ('a -> 'b * 'c) * ('c -> 'd * 'e) -> 'a -> 'b * 'e
  (*concatenation*)
  val _ = op ^^ : ('a -> string * 'b) * ('b -> string * 'c) -> 'a -> string * 'c
  val _ = op ::: : ('a -> 'b * 'c) * ('c -> 'b list * 'd) -> 'a -> 'b list * 'd
  val _ = op @@@ : ('a -> 'b list * 'c) * ('c -> 'b list * 'd) -> 'a -> 'b list * 'd
  (*one element literal*)
  val _ = op $$ : string -> string list -> string * string list
  val _ = op ~$$ : string -> string list -> string * string list
 \<close>

text\<open>Usually, combinators were used in one of these following instances:\<close>

ML\<open>

  type 'a parser = Token.T list -> 'a * Token.T list
  type 'a context_parser = Context.generic * Token.T list -> 'a * (Context.generic * Token.T list)


(* conversion between these two : *)

fun parser2contextparser pars (ctxt, toks) = let val (a, toks') = pars toks
                                             in  (a,(ctxt, toks')) end;
val _ = parser2contextparser : 'a parser -> 'a context_parser;

(* bah, is the same as Scan.lift *)
val _ = Scan.lift Args.cartouche_input : Input.source context_parser;\<close>

subsection\<open>Advanced Parser Library\<close>

text\<open>There are two parts. A general multi-purpose parsing combinator library is 
  found under @{ML_structure "Parse"}, providing basic functionality for parsing strings
  or integers. There is also an important combinator that reads the current position information
  out of the input stream:\<close>
ML\<open>
Parse.nat: int parser;  
Parse.int: int parser;
Parse.enum_positions: string -> 'a parser -> ('a list * Position.T list) parser;
Parse.enum: string -> 'a parser -> 'a list parser;
Parse.input: 'a parser -> Input.source parser;

Parse.enum : string -> 'a parser -> 'a list parser;
Parse.!!! : (Token.T list -> 'a) -> Token.T list -> 'a;
Parse.position: 'a parser -> ('a * Position.T) parser;

(* Examples *)                                     
Parse.position Args.cartouche_input;
\<close>

text\<open>The second part is much more high-level, and can be found under @{ML_structure Args}.
  In parts, these combinators are again based on more low-level combinators, in parts they serve as 
  an an interface to the underlying Earley-parser for mathematical notation used in types and terms.
  This is perhaps meant with the fairly cryptic comment:
  "Quasi-inner syntax based on outer tokens: concrete argument syntax of
  attributes, methods etc." at the beginning of this structure.\<close>

ML\<open>

local 

  open Args

  (* some more combinaotrs *)
  val _ =  symbolic: Token.T parser
  val _ =  $$$ : string -> string parser
  val _ =  maybe: 'a parser -> 'a option parser
  val _ =  name_token: Token.T parser


  (* common isar syntax *)
  val _ =  colon: string parser
  val _ =  query: string parser
  val _ =  bang: string parser
  val _ =  query_colon: string parser
  val _ =  bang_colon: string parser
  val _ =  parens: 'a parser -> 'a parser
  val _ =  bracks: 'a parser -> 'a parser
  val _ =  mode: string -> bool parser
  val _ =  name: string parser
  val _ =  name_position: (string * Position.T) parser
  val _ =  cartouche_inner_syntax: string parser
  val _ =  cartouche_input: Input.source parser
  val _ =  text_token: Token.T parser

  (* advanced string stuff *)
  val _ =  embedded_token: Token.T parser
  val _ =  embedded_inner_syntax: string parser
  val _ =  embedded_input: Input.source parser
  val _ =  embedded: string parser
  val _ =  embedded_position: (string * Position.T) parser
  val _ =  text_input: Input.source parser
  val _ =  text: string parser
  val _ =  binding: binding parser

  (* stuff related to INNER SYNTAX PARSING *)
  val _ =  alt_name: string parser
  val _ =  liberal_name: string parser
  val _ =  var: indexname parser
  val _ =  internal_source: Token.src parser
  val _ =  internal_name: Token.name_value parser
  val _ =  internal_typ: typ parser
  val _ =  internal_term: term parser
  val _ =  internal_fact: thm list parser
  val _ =  internal_attribute: (morphism -> attribute) parser
  val _ =  internal_declaration: declaration parser


  val _ =  named_source: (Token.T -> Token.src) -> Token.src parser
  val _ =  named_typ: (string -> typ) -> typ parser
  val _ =  named_term: (string -> term) -> term parser

  val _ =  text_declaration: (Input.source -> declaration) -> declaration parser
  val _ =  cartouche_declaration: (Input.source -> declaration) -> declaration parser
  val _ =  typ_abbrev: typ context_parser

  val _ =  typ: typ context_parser
  val _ =  term: term context_parser
  val _ =  term_pattern: term context_parser
  val _ =  term_abbrev: term context_parser

  (* syntax for some major Pure commands in Isar *)
  val _ =  prop: term context_parser
  val _ =  type_name: {proper: bool, strict: bool} -> string context_parser
  val _ =  const: {proper: bool, strict: bool} -> string context_parser
  val _ =  goal_spec: ((int -> tactic) -> tactic) context_parser
  val _ =  context: Proof.context context_parser   
  val _ =  theory: theory context_parser

in val _ = () end

\<close>


subsection\<open> Bindings \<close>  

text\<open> The structure @{ML_structure "Binding"} serves as 
  \<open>structured name bindings\<close>, as says the description, i.e. a mechanism to basically 
  associate an input string-fragment to its position. This concept is vital in all parsing processes
  and the interaction with PIDE.

  Key are two things:
\<^enum> the type-synonym @{ML_type "bstring"} which is synonym to @{ML_type "string"}
  and intended for "primitive names to be bound"
\<^enum> the projection @{ML "Binding.pos_of :  binding -> Position.T"} 
\<^enum> the constructor establishing a binding @{ML "Binding.make: bstring * Position.T -> binding"}

\<close>

text\<open>Since this is so common in interface programming, there are a number of antiquotations\<close>
ML\<open>
val H = @{binding here}; (* There are "bindings" consisting of a text-span and a position, 
                            where \<dieresis>positions\<dieresis> are absolute references to a file *)                                  

Binding.pos_of H;  (* clicking on "H" activates the hyperlink to the defining occ of "H" above *)
(*  {offset=23, end_offset=27, id=-17214}: Position.T *)

(* a modern way to construct a binding is by the following code antiquotation : *)
\<^binding>\<open>theory\<close>

\<close>  

subsection \<open>Input streams. \<close>  
text\<open>Reads as : Generic input with position information.\<close>

ML\<open>  
  Input.source_explode : Input.source -> Symbol_Pos.T list;
  Input.source_explode (Input.string " f @{thm refl}");
  
   (* If stemming from the input window, this can be s th like: 
      
        [(" ", {offset=14, id=-2769}), ("f", {offset=15, id=-2769}), (" ", {offset=16, id=-2769}),
        ("@", {offset=17, id=-2769}), ("{", {offset=18, id=-2769}), ("t", {offset=19, id=-2769}),
        ("h", {offset=20, id=-2769}), ("m", {offset=21, id=-2769}), (" ", {offset=22, id=-2769}),
        ("r", {offset=23, id=-2769}), ("e", {offset=24, id=-2769}), ("f", {offset=25, id=-2769}),
        ("l", {offset=26, id=-2769}), ("}", {offset=27, id=-2769})]
   *)

\<close>
  

section\<open>Term Parsing\<close>  

text\<open>The heart of the parsers for mathematical notation, based on an Earley parser that can cope
  with incremental changes of the grammar as required for sophisticated mathematical output, is hidden
  behind the API described in this section.\<close>
  
text\<open> Note that the naming underlies the following convention : 
   there are:
   \<^enum> "parser"s and type-"checker"s 
   \<^enum> "reader"s which do both together with pretty-printing
   
   This is encapsulated the data structure @{ML_structure Syntax} --- 
   the table with const symbols,  print and ast translations, ... The latter is accessible, e.g. 
   from a Proof context via @{ML Proof_Context.syn_of}.
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
 
text\<open>
  Note that @{ML "Syntax.install_operations"} is a late-binding interface, i.e. a collection of 
  "hooks" used to resolve an apparent architectural cycle.
  The real work is done in @{file "~~/src/Pure/Syntax/syntax_phases.ML"} 
  
  Even the parsers and type checkers stemming from the theory-structure are registered via
  hooks (this can be confusing at times). Main phases of inner syntax processing, with standard 
  implementations of parse/unparse operations were treated this way.
  At the very very end in  , it sets up the entire syntax engine 
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

subsection*[ex33::example] \<open>Example\<close>

ML\<open>
(* Recall the Arg-interface to the more high-level, more Isar-specific parsers: *)
Args.name           : string parser ;
Args.const          : {proper: bool, strict: bool} -> string context_parser;
Args.cartouche_input: Input.source parser; 
Args.text_token     : Token.T parser;


(* here follows the definition of the attribute parser : *)
val Z = let val attribute = Parse.position Parse.name -- 
                            Scan.optional (Parse.$$$ "=" |-- Parse.!!! Parse.name) "";
        in   (Scan.optional(Parse.$$$ "," |-- (Parse.enum "," attribute))) end ;


(* Here is the code to register the above parsers as text antiquotations into the Isabelle
   Framework: *)
Thy_Output.antiquotation_pretty_source \<^binding>\<open>theory\<close> (Scan.lift (Parse.position Args.embedded));

Thy_Output.antiquotation_raw \<^binding>\<open>file\<close> (Scan.lift (Parse.position Parse.path))  ;


(* where we have the registration of the action
   
        (Scan.lift (Parse.position Args.cartouche_input))))
    
   to be bound to the 
 
        name

   as a whole is a system transaction that, of course, has the type

        theory -> theory  : *)
(fn name => (Thy_Output.antiquotation_pretty_source name 
                                                   (Scan.lift (Parse.position Args.cartouche_input))))
  : binding -> (Proof.context -> Input.source * Position.T -> Pretty.T) -> theory -> theory;
\<close>

  
section \<open> Output: Very Low Level \<close>
text\<open> For re-directing the output channels, the structure @{ML_structure Output} may be relevant:\<close>

ML\<open> 
Output.output; (* output is the  structure for the "hooks" with the target devices. *)
Output.output "bla_1:";
\<close>

text\<open>It provides a number of hooks that can be used for redirection hacks ...\<close>

section \<open> Output: LaTeX \<close>
text\<open>The heart of the LaTeX generator is to be found in the structure @{ML_structure Thy_Output}.
  This is an own parsing and writing process, with the risc that a parsed file in the IDE parsing
  process can not be parsed for the LaTeX Generator. The reason is twofold:
\<^enum> The LaTeX Generator makes a rough attempt to mimic the LayOut if the thy-file; thus, its
  spacing is relevant.
\<^enum> there is a special bracket \<open>(*<*)\<close> ... \<open>(*>*)\<close> that allows to specify input that is checked by
  Isabelle, but excluded from the LaTeX generator (this is handled in an own sub-parser
  called @{ML "Document_Source.improper"} where also other forms of comment parsers are provided.

  Since Isabelle2018, an own AST is provided for the LaTeX syntax, analogously to 
  @{ML_structure "Pretty"}. Key functions of this structure @{ML_structure "Latex"} are:
\<close>

ML\<open>
local 

  open Latex

  type dummy = text

  val _ = string: string -> text;
  val _ = text: string * Position.T -> text

  val _ = output_text: text list -> string
  val _ = output_positions: Position.T -> text list -> string
  val _ = output_name: string -> string
  val _ = output_ascii: string -> string
  val _ = output_symbols: Symbol.symbol list -> string

  val _ = begin_delim: string -> string
  val _ = end_delim: string -> string
  val _ = begin_tag: string -> string
  val _ = end_tag: string -> string
  val _ = environment_block: string -> text list -> text
  val _ = environment: string -> string -> string

  val _ = block: text list -> text
  val _ = enclose_body: string -> string -> text list -> text list
  val _ = enclose_block: string -> string -> text list -> text

in val _ = ()
end;

Latex.output_ascii;
Latex.environment "isa" "bg";
Latex.output_ascii "a_b:c'é";
(* Note: *)
space_implode "sd &e sf dfg" ["qs","er","alpa"];

\<close>

text\<open>Here is an abstract of the main interface to @{ML_structure Thy_Output}:\<close>

ML\<open> 
 output_document: Proof.context -> {markdown: bool} -> Input.source -> Latex.text list;
 output_token: Proof.context -> Token.T -> Latex.text list;
 output_source: Proof.context -> string -> Latex.text list;
 present_thy: Options.T -> theory -> segment list -> Latex.text list;

 isabelle: Proof.context -> Latex.text list -> Latex.text;

 isabelle_typewriter: Proof.context -> Latex.text list -> Latex.text;

 typewriter: Proof.context -> string -> Latex.text;

 verbatim: Proof.context -> string -> Latex.text;

 source: Proof.context -> {embedded: bool} -> Token.src -> Latex.text;

 pretty: Proof.context -> Pretty.T -> Latex.text;
 pretty_source: Proof.context -> {embedded: bool} -> Token.src -> Pretty.T -> Latex.text;
 pretty_items: Proof.context -> Pretty.T list -> Latex.text;
 pretty_items_source: Proof.context -> {embedded: bool} -> Token.src -> Pretty.T list -> Latex.text;

(* finally a number of antiquotation registries : *)
 antiquotation_pretty:
      binding -> 'a context_parser -> (Proof.context -> 'a -> Pretty.T) -> theory -> theory;
 antiquotation_pretty_source:
    binding -> 'a context_parser -> (Proof.context -> 'a -> Pretty.T) -> theory -> theory;
 antiquotation_raw:
    binding -> 'a context_parser -> (Proof.context -> 'a -> Latex.text) -> theory -> theory;
 antiquotation_verbatim:
      binding -> 'a context_parser -> (Proof.context -> 'a -> string) -> theory -> theory;

\<close>


text\<open> Thus, @{ML_structure Syntax_Phases} does the actual work of markup generation, including 
        markup generation and  generation of reports. Look at the following snippet: \<close>
ML\<open>
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
\<close>  
  

section*[cartouches::technical]\<open>Inner Syntax Cartouches\<close>
text\<open> The cascade-syntax principle underlying recent isabelle versions requires a 
  particular mechanism, called "cartouche" by Makarius who was influenced by French 
  Wine and French culture when designing this.

  When parsing terms or types (via the Earley Parser), a standard mechanism for
  calling another parser inside the current process is needed that is bound to the 
  \<open>(\<open>)\<close> ... \<open>(\<close>)\<close> paranthesis'. \<close>

text\<open>The following example --- drawn from the Isabelle/DOF implementation --- allows
  to parse UTF8 - Unicode strings as alternative to @{term "''abc''"} HOL-strings.\<close>

ML\<open>\<comment> \<open>Dynamic setup of inner syntax cartouche\<close>


(*  Author:     Frédéric Tuong, Université Paris-Saclay *)
(*  Title:      HOL/ex/Cartouche_Examples.thy
    Author:     Makarius *)
  local
    fun mk_char (f_char, f_cons, _) (s, _) accu =
        fold
          (fn c => fn (accu, l) =>
            (f_char c accu, f_cons c l))
          (rev (map Char.ord (String.explode s)))
          accu;

    fun mk_string (_, _, f_nil) accu [] = (accu, f_nil)
      | mk_string f accu (s :: ss) = mk_char f s (mk_string f accu ss);
  in
    fun string_tr f f_mk accu content args =
      let fun err () = raise TERM ("string_tr", args) in
        (case args of
          [(c as Const (@{syntax_const "_constrain"}, _)) $ Free (s, _) $ p] =>
            (case Term_Position.decode_position p of
              SOME (pos, _) => c $ f (mk_string f_mk accu (content (s, pos))) $ p
            | NONE => err ())
        | _ => err ())
      end;
  end;
\<close>

syntax "_cartouche_string" :: "cartouche_position \<Rightarrow> _"  ("_")

ML\<open>
structure Cartouche_Grammar = struct
  fun list_comb_mk cst n c = list_comb (Syntax.const cst, String_Syntax.mk_bits_syntax n c)
  val nil1 = Syntax.const @{const_syntax String.empty_literal}
  fun cons1 c l = list_comb_mk @{const_syntax String.Literal} 7 c $ l

  val default =
    [ ( "char list"
      , ( Const (@{const_syntax Nil}, @{typ "char list"})
        , fn c => fn l => Syntax.const @{const_syntax Cons} $ list_comb_mk @{const_syntax Char} 8 c $ l
        , snd))
    , ( "String.literal", (nil1, cons1, snd))]
end
\<close>

ML\<open>
fun parse_translation_cartouche binding l f_integer accu =
  let val cartouche_type = Attrib.setup_config_string binding (K (fst (hd l)))
      (* if there is no type specified, by default we set the first element
         to be the default type of cartouches *) in
  fn ctxt =>
    let val cart_type = Config.get ctxt cartouche_type in
    case List.find (fn (s, _) => s = cart_type) l of
      NONE => error ("Unregistered return type for the cartouche: \"" ^ cart_type ^ "\"")
    | SOME (_, (nil0, cons, f)) =>
        string_tr f (f_integer, cons, nil0) accu (Symbol_Pos.cartouche_content o Symbol_Pos.explode)
    end
  end
\<close>

text\<open>The following registration of this cartouche for strings is fails because it has
  already been done in the surrounding Isabelle/DOF environment... \<close>
  (*
  parse_translation \<open>
    [( @{syntax_const "_cartouche_string"}
     , parse_translation_cartouche \<^binding>\<open>cartouche_type\<close> Cartouche_Grammar.default (K I) ())]
  \<close>
  *)

(* test for this cartouche... *) 
term  "\<open>A \<Longrightarrow> B\<close> = ''''"



chapter*[c::conclusion]\<open>Conclusion\<close>
text\<open> This interactive Isabelle Programming Cook-Book represents my current way 
  to view and explain Isabelle programming API's to students and collaborators. 
  It differs from the reference  manual in some places on purpose, since I believe 
  that a lot of internal Isabelle API's need a more conceptual view on what is happening 
  (even if this conceptual view is at times over-abstracting a little).
  It also offers a deliberately different abstraction  to the explanations in form of comments
  in the sources or in the Reference Manual.
  
  The descriptions of some sources may appear lengthy and repetitive and redundant - but this kind 
  of repetition not only give an idea of the chosen abstraction levels on some interfaces, but also
  represents --- since this is a "living document" (a notion I owe Simon Foster) --- a continuous check
  for each port of our material to  each more recent Isabelle version, where the first attempts
  to load it will fail, but give another source of information over the modifications of
  the system interface for parts relevant to our own development work.
  
  All hints and contributions of collegues and collaborators are greatly welcomed; all errors
  and the roughness of this presentation is entirely my fault.
\<close>
(*<*)

section*[bib::bibliography]\<open>Bibliography\<close>

close_monitor*[this] 
check_doc_global

end
(*>*)