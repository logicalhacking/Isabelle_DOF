(*************************************************************************
 * Copyright (C) 
 *               2019-2021 The University of Exeter 
 *               2018-2021 The University of Paris-Saclay
 *               2018      The University of Sheffield
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

(*<*)
theory TR_MyCommentedIsabelle
  imports "Isabelle_DOF.technical_report" 

begin

define_shortcut* isabelle \<rightleftharpoons> \<open>Isabelle/HOL\<close>

open_monitor*[this::report] 
(*>*)

title*[tit::title]\<open>My Personal, Eclectic Isabelle Programming Manual\<close> 
subtitle*[stit::subtitle]\<open>Version : Isabelle 2020\<close>
text*[bu::author,     
      email       = "''wolff@lri.fr''",
      affiliation = "\<open>Université Paris-Saclay, LRI, France\<close>"]\<open>Burkhart Wolff\<close>
    

text*[abs::abstract,
      keywordlist="[''LCF-Architecture'',''Isabelle'',''SML'',''PIDE'',''Programming Guide'',
                    ''Tactic Programming'']"]\<open>
  While Isabelle is mostly known as "logical framework" underlying \<^isabelle> and thus commonly
  understood as an interactive theorem prover, it actually provides a system framework for 
  developing a wide spectrum of applications. A particular strength of the Isabelle framework is 
  the  combination of document editing, formal verification, and code generation. 
  
  This is a programming-tutorial of \<^isabelle>, conceived as a complementary
  text to the unfortunately somewhat outdated "The Isabelle Cookbook" in
  \<^url>\<open>https://nms.kcl.ac.uk/christian.urban/Cookbook/\<close>. The reader is encouraged
  not only to consider the generated .pdf, but also consult the loadable version in Isabelle/jEdit
  @{cite "DBLP:journals/corr/Wenzel14"} in order to make experiments on the running code.
  
  This text is written itself in Isabelle/Isar using a specific document ontology
  for technical reports. It is intended to be a "living document", i.e. it is not only
  used for generating a static, conventional .pdf, but also for direct interactive 
  exploration in Isabelle/jEdit. This way, types, intermediate results of computations and
  checks can be repeated by the reader who is invited to interact with this document.
  Moreover, the textual parts have been enriched with a maximum of formal content
  which makes this text re-checkable at each load and easier maintainable.
\<close>

chapter*[intro::introduction]\<open> Introduction  \<close>    

text\<open> \<^vs>\<open>-0.5cm\<close> 
  While Isabelle @{cite "DBLP:books/sp/NipkowPW02"} is mostly known as part of Isabelle/HOL 
  (an interactive theorem prover), it actually provides a system framework for developing a wide 
  spectrum of applications. A particular strength of the Isabelle framework is the combination 
  of text editing, formal verification, and code generation. This is a programming-tutorial of 
  Isabelle and Isabelle/HOL, a complementary text to the unfortunately somewhat outdated 
  "The Isabelle Cookbook" in \<^url>\<open>https://nms.kcl.ac.uk/christian.urban/Cookbook/\<close>. 
  The present text is also complementary to the current version of 
  \<^url>\<open>https://isabelle.in.tum.de/dist/Isabelle2021/doc/isar-ref.pdf\<close>
  "The Isabelle/Isar Implementation" by Makarius Wenzel in that it focusses on subjects
  not covered there, or presents alternative explanations for which I believe, based on my 
  experiences with students and Phds, that they are helpful.
  For the present programming manual, the reader is encouraged not only to consider the generated 
  .pdf, but also consult the loadable version 
  in Isabelle/jedit in order to make experiments on the running code. This text is written 
  itself in Isabelle/Isar using a specific document ontology for technical reports. It is 
  intended to be a "living document", i.e. it is not only used for generating a static, 
  conventional .pdf, but also for direct interactive exploration in Isabelle/jEdit. This way, 
  types, intermediate results of computations and checks can be repeated by the reader who is 
  invited to interact with this document. Moreover, the textual parts have been enriched with a 
  maximum of formal content which makes this text re-checkable at each load and easier 
  maintainable. \<close>

figure*[architecture::figure,relative_width="70",src="''figures/isabelle-architecture''"]\<open> 
     The system architecture of Isabelle (left-hand side) and the  asynchronous communication 
     between the Isabelle system and the IDE (right-hand side). \<close>

text\<open>This programming tutorial roughly follows the Isabelle system architecture shown in 
  \<^figure>\<open>architecture\<close>, and, to be more precise, more or less in the bottom-up order.

  We start from the basic underlying SML platform over the Kernels to the tactical layer 
  and end with a discussion over the front-end technologies.  \<^vs>\<open>-1.0cm\<close>
\<close>

chapter*[t1::technical]\<open> SML and Fundamental SML libraries  \<close>    

section*[t11::technical] "ML, Text and Antiquotations"

text\<open>Isabelle is written in SML, the "Standard Meta-Language", which is an impure functional 
  programming language allowing, in principle, mutable variables and side effects. 
  The following Isabelle/Isar commands allow for accessing the underlying SML interpreter
  of Isabelle directly. In the example, a mutable variable X is declared, initialized to 0 and 
  updated; and finally re-evaluated leading to output: \<close>

ML\<open> 
    val X = Unsynchronized.ref 0;
    X:= !X + 1;
    X
  \<close>

text\<open>However, since Isabelle is a platform involving parallel execution, concurrent computing, and,
  as an interactive environment, involves backtracking / re-evaluation as a consequence of user-
  interaction, imperative programming is discouraged and nearly never used in the entire Isabelle
  code-base @{cite "DBLP:conf/mkm/BarrasGHRTWW13"}.
  The preferred programming style is purely functional: \<close>

ML\<open> 
    fun fac x = if x = 0 then 1 else x * fac(x-1) ;
    fac 10;
  \<close>
text\<open>or:\<close> 
ML\<open> 
    type state = {  a : int,   b : string}
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
  representing text-elements in Isabelle/Isar; text commands can be interleaved arbitrarily
  with other commands. Text in text-commands may use LaTeX and is used for type-setting 
  documentations in a kind of literate programming style. \<close>

text\<open>So: the text command for:\<close>

text\<open>\<^emph>\<open>This is a text.\<close>\<close>

text\<open>... is represented in the integrated source (the \<^verbatim>\<open>.thy\<close> file) by:\<close>

text\<open> \<open>*\<open>This is a text.\<close>\<close>\<close>

text\<open>and displayed in the Isabelle/jEdit front-end at the sceen by:\<close>

figure*[fig2::figure, relative_width="60", placement="pl_h", src="''figures/text-element''"]
        \<open>A text-element as presented in Isabelle/jEdit.\<close>

text\<open>The text-commands, ML-commands (and in principle any other command) can be seen as 
  \<^emph>\<open>quotations\<close> over the underlying SML environment (similar to OCaml or Haskell).
  Linking these different sorts of quotations with each other and the underlying SML-environment
  is supported via \<^emph>\<open>antiquotations\<close>'s. Generally speaking, antiquotations are a kind of semantic
  macro whose arguments were checked, interpreted and expanded using the underlying system
  state. This paves the way for a programming technique to specify expressions or patterns in an 
  anti-quotation in various contexts, be it in an ML fragment or a documentation fragment.
  Anti-quotations as "semantic macros" can produce a value for the surrounding context
  (ML, text, HOL, whatever) depending on local arguments and the underlying logical context.
  
  The way an antiquotation is specified depends on the quotation expander: typically, this is a 
  specific character and an identifier, or specific parentheses and a complete expression or 
  pattern.\<close>

text\<open> In Isabelle documentations, antiquotation's were heavily used to enrich literate explanations
  and documentations by "formal content", i.e. machine-checked, typed references
  to all sorts of entities in the context of the interpreting environment. 
  Formal content allows for coping with sources that rapidly evolve and were developed by 
  distributed teams as is typical in open-source developments. 

  A paradigmatic example for antiquotation in documentation text snippets and program snippets is here:
  \<^item> \<^theory_text>\<open>text\<open>@{footnote \<open>sdf\<close>}, @{file "$ISABELLE_HOME/src/Pure/ROOT.ML"}\<close>\<close>
  \<^item> @{theory_text [display]
     \<open> val x = @{thm refl};
       val _ = @{term "A \<longrightarrow> B"}
       val y = @{typ  "'a list"} 
     \<close>
    }
  \<close>

(*<*) (* example to execute: *)
text\<open> @{footnote \<open>sdf\<close>}, @{file "$ISABELLE_HOME/src/Pure/ROOT.ML"}\<close>
ML\<open>    
       val x = @{thm refl};
       val _ = @{term "A \<longrightarrow> B"}
       val y = @{typ  "'a list"}
  \<close>
(*>*)

text\<open>\<^vs>\<open>-1.0cm\<close>... which we will describe in more detail later. \<close> 

text\<open>In a way, anti-quotations implement a kind of 
  literate specification style in text, models, code, proofs, etc., which become alltogether
  elements of one global \<^emph>\<open>integrated document\<close> in which mutual dependencies can be machine-checked
  (i.e. \<open>formal\<close> in this sense).
  Attempting to maximize the \<open>formal content\<close> is a way to ensure "Agile Development" (AD) of an 
  integrated document development, in the sense that it allows to give immediate feedback
  with respect to changes which enable thus the popular AD-objective \<^emph>\<open>embrace change\<close>.
  Note that while we adhere to this objective, we do not depend or encourage popular AD methods 
  and processes such as SCRUM. \<close>

paragraph\<open>
  A maximum of formal content inside text documentation also ensures the 
  consistency of this present text with the underlying Isabelle version.\<close>

section\<open>The Isabelle/Pure bootstrap\<close>

text\<open>It is instructive to study the fundamental bootstrapping sequence of the Isabelle system;
  it is written in the Isar format and gives an idea of the global module dependencies: 
  \<^file>\<open>~~/src/Pure/ROOT.ML\<close>. Loading this file 
  (for example by hovering over this hyperlink in the antiquotation holding control or
  command key in Isabelle/jEdit and activating it) allows the Isabelle IDE 
  to support hyperlinking \<^emph>\<open>inside\<close> the Isabelle source.\<close>

text\<open>The bootstrapping sequence is also reflected in the following diagram @{figure "architecture"}.\<close>


section*[t12::technical] "Elements of the SML library"  
text\<open>Elements of the \<^file>\<open>~~/src/Pure/General/basics.ML\<close>  SML library
  are basic exceptions. Note that exceptions should be catched individually, uncatched exceptions 
  except those generated by the specific "error" function are discouraged in Isabelle
  source programming since they might produce races in the internal Isabelle evaluation.
  % TODO:
  % The following exceptions are defined in $ML_SOURCES/basis/General.sml
  % and in $ISABELLE_HOME/src/Pure/general/scan.ml
  % ans not in \<^file>\<open>~~/src/Pure/General/basics.ML\<close>
  
\<^item> \<^ML>\<open>Bind      : exn\<close> \<^vs>\<open>-0.3cm\<close>
\<^item> \<^ML>\<open>Chr       : exn\<close>  \<^vs>\<open>-0.3cm\<close>
\<^item> \<^ML>\<open>Div       : exn\<close> \<^vs>\<open>-0.3cm\<close>
\<^item> \<^ML>\<open>Domain    : exn\<close> \<^vs>\<open>-0.3cm\<close>
\<^item> \<^ML>\<open>Fail      : string -> exn\<close>,  \<^vs>\<open>-0.3cm\<close>
\<^item> \<^ML>\<open>Match     : exn\<close>, relevant for pattern matching  \<^vs>\<open>-0.3cm\<close>
\<^item> \<^ML>\<open>Overflow  : exn\<close> \<^vs>\<open>-0.3cm\<close>
\<^item> \<^ML>\<open>Size      : exn\<close> \<^vs>\<open>-0.3cm\<close>
\<^item> \<^ML>\<open>Span      : exn\<close> \<^vs>\<open>-0.3cm\<close>
\<^item> \<^ML>\<open>Subscript : exn\<close> \<^vs>\<open>-0.3cm\<close>
\<^item> \<^ML>\<open>exnName   : exn -> string\<close>, very interesting to query an unknown \<open>exception\<close>  \<^vs>\<open>-0.3cm\<close> 
\<^item> \<^ML>\<open>exnMessage: exn -> string\<close>  \<^vs>\<open>-0.3 cm\<close>
\<close> (* typesetting as table ? *)

text*[squiggols::technical]
\<open>\<^noindent> Finally, a number of commonly used "squigglish" combinators is listed:

\<^item> @{ML "op !  : 'a Unsynchronized.ref->'a"},  access operation on a program variable  \<^vs>\<open>-0.3cm\<close>
\<^item> @{ML "op := : ('a Unsynchronized.ref * 'a)->unit"}, update operation on program variable\<^vs>\<open>-0.3cm\<close>
\<^item> @{ML "op #> : ('a->'b) * ('b->'c)->'a->'c"}, a reversed function composition  \<^vs>\<open>-0.3cm\<close>
\<^item> @{ML "I: 'a -> 'a"}, the I combinator \<^vs>\<open>-0.3cm\<close>
\<^item> @{ML "K: 'a -> 'b -> 'a"}, the K combinator \<^vs>\<open>-0.3cm\<close>
\<^item> @{ML "op o  : (('b->'c) * ('a->'b))->'a->'c"}, function composition \<^vs>\<open>-0.3cm\<close>
\<^item> @{ML "op || : ('a->'b) * ('a->'b) -> 'a -> 'b"}, parse alternative \<^vs>\<open>-0.3cm\<close>
\<^item> @{ML "op -- : ('a->'b*'c) * ('c->'d*'e)->'a->('b*'d)*'e"}, parse pair \<^vs>\<open>-0.3cm\<close>
\<^item> @{ML "op |-- : ('a->'b*'c) * ('c->'d*'e)->'a->'d*'e"}, parse pair, forget right \<^vs>\<open>-0.3cm\<close>
\<^item> @{ML "op --| : ('a->'b*'c) * ('c->'d*'e)->'a->'b*'e"}, parse pair, forget left \<^vs>\<open>-0.3cm\<close>
\<^item> @{ML "op ?  : bool * ('a->'a)->'a->'a"}, if then else  \<^vs>\<open>-0.3cm\<close>
\<^item> @{ML "ignore   : 'a->unit"}, force execution, but ignore result \<^vs>\<open>-0.3cm\<close>
\<^item> @{ML "op before: ('a*unit) -> 'a"} \<^vs>\<open>-0.8cm\<close>
% TODO:
% Again the definitions of these operators span multiple files
% and not just \<^file>\<open>~~/src/Pure/General/basics.ML\<close>.
\<close>

text\<open>\<^noindent> Some basic examples for the programming style using these combinators can be found in the
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
  % NOTE:
  % Add the reference.

  In my words: a context is essentially a container with
  \<^item> an id
  \<^item> a list of parents (so: the graph structure)
  \<^item> a time stamp and
  \<^item> a sub-context relation (which uses a combination of the id and the time-stamp to
    establish this relation very fast whenever needed; it plays a crucial role for the
    context transfer in the kernel.
  
  
  A context comes in form of three 'flavours':
  \<^item> theories : \<^ML_type>\<open>theory\<close>'s, containing a syntax and axioms, but also
               user-defined data and configuration information.
  \<^item> Proof-Contexts: \<^ML_type>\<open>Proof.context\<close>  
               containing theories but also additional information if Isar goes into prove-mode.
               In general a richer structure than theories coping also with fixes, facts, goals,
               in order to support the structured Isar proof-style.
  \<^item> Generic:  \<^ML_type>\<open>Context.generic\<close>, i.e. the sum of both.
  
  All context have to be seen as mutable; so there are usually transformations defined on them
  which are possible as long as a particular protocol (\<^verbatim>\<open>begin_thy\<close> - \<^verbatim>\<open>end_thy\<close> etc) are respected.
  
  Contexts come with type user-defined data which is mutable through the entire lifetime of
  a context.
\<close>  

subsection*[t212::technical]\<open> Mechanism 1 : Core Interface. \<close>
text\<open>To be found in @{file  "$ISABELLE_HOME/src/Pure/context.ML"}:\<close>

text\<open>
\<^item> \<^ML>\<open>Context.parents_of: theory -> theory list\<close> gets the (direct) parent theories
\<^item> \<^ML>\<open>Context.ancestors_of: theory -> theory list\<close> gets the imported theories
\<^item> \<^ML>\<open>Context.proper_subthy : theory * theory -> bool\<close> subcontext test
\<^item> \<^ML>\<open>Context.Proof: Proof.context -> Context.generic \<close> A constructor embedding local contexts
\<^item> \<^ML>\<open>Context.proof_of : Context.generic -> Proof.context\<close> the inverse
\<^item> \<^ML>\<open>Context.theory_name : theory -> string\<close>
\<^item> \<^ML>\<open>Context.map_theory: (theory -> theory) -> Context.generic -> Context.generic\<close>
\<close>

text\<open>The structure \<^ML_structure>\<open>Proof_Context\<close> provides a key data-structures concerning contexts:

\<^item> \<^ML>\<open> Proof_Context.init_global: theory -> Proof.context\<close>
  embeds a global context into a local context
\<^item> \<^ML>\<open>  Context.Proof: Proof.context -> Context.generic \<close>
  the path to a generic Context, i.e. a sum-type of global and local contexts
  in order to simplify system interfaces
\<^item> \<^ML>\<open> Proof_Context.get_global: theory -> string -> Proof.context\<close>
\<close>


subsection*[t213::example]\<open>Mechanism 2 : Extending the Global Context \<open>\<theta>\<close> by User Data \<close>

text\<open>A central mechanism for constructing user-defined data is by the \<^ML_functor>\<open>Generic_Data\<close>-functor.
  A plugin needing some data \<^verbatim>\<open>T\<close> and providing it with implementations for an 
  \<^verbatim>\<open>empty\<close>, and operations  \<^verbatim>\<open>merge\<close> and \<^verbatim>\<open>extend\<close>, can construct a lense with operations
  \<^verbatim>\<open>get\<close> and \<^verbatim>\<open>put\<close> that attach this data into the generic system context. Rather than using
  unsynchronized SML mutable variables, this is the mechanism to introduce component local
  data in Isabelle, which allows to manage this data for the necessary backtrack and synchronization
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
\<close>
text\<open> This generates the result structure \<^ML_structure>\<open>Data\<close> by a functor instantiation 
with the functions:

\<^item> \<^ML>\<open> Data.get : Context.generic -> Data.T\<close>
\<^item> \<^ML>\<open> Data.put : Data.T -> Context.generic -> Context.generic\<close>
\<^item> \<^ML>\<open> Data.map : (Data.T -> Data.T) -> Context.generic -> Context.generic\<close>
\<^item> ... and other variants to do this on theories ...
\<close>


section*[lcfk::technical]\<open>The LCF-Kernel: \<^ML_type>\<open>term\<close>s, \<^ML_type>\<open>typ\<close>es,  \<^ML_type>\<open>theory\<close>s, 
                          \<^ML_type>\<open> Proof.context\<close>s,  \<^ML_type>\<open>thm\<close>s \<close>  
text\<open>The classical LCF-style \<^emph>\<open>kernel\<close> is about   
\<^enum> Types and terms of a typed \<open>\<lambda>\<close>-Calculus including constant symbols,
  free variables, \<open>\<lambda>\<close>-binder and application,
\<^enum> An infrastructure to define types and terms, a \<^emph>\<open>signature\<close> in structure  \<^ML_structure>\<open>Sign\<close>
  that also assigns to constant symbols types and concrete syntax managed in structure
  \<^ML_structure>\<open>Syntax\<close>
\<^enum> An abstract type  \<^ML_type>\<open>thm\<close> for \<^emph>\<open>theorem\<close> and logical operations on them
\<^enum> (Isabelle specific): a notion of \<^ML_type>\<open>theory\<close>, i.e. a container 
  providing a signature and set (list) of theorems.   
\<close>


subsection*[termstypes::technical]\<open> Terms and Types \<close>
text \<open>The basic data-structure  \<^ML_structure>\<open>Term\<close> of the kernel is contained in file
@{file "$ISABELLE_HOME/src/Pure/term.ML"}. At a glance, the highlights are summarized as follows: \<close>  
(* Methodologically doubtful: nothing guarantees that TERM' corresponds to what is Isabelle reality*)
ML\<open> 
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
    $ of term * term  (* the infix operator for the application *)
  exception TYPE of string * typ list * term list
  exception TERM of string * term list
  (* ... *)
end
\<close>

(* methodologically better: *)
text\<open>\<^noindent> Basic types introduced by structure  \<^ML_structure>\<open>Term\<close> are:

\<^item> \<^ML_type>\<open>Term.indexname\<close> which is a synonym to  \<^ML_type>\<open>string * int\<close>
\<^item> \<^ML_type>\<open>Term.class\<close> which is a synonym to  \<^ML_type>\<open>string\<close>
\<^item> \<^ML_type>\<open>Term.sort\<close> which is a synonym to  \<^ML_type>\<open>class list\<close>
\<^item> \<^ML_type>\<open>Term.arity\<close> which is a synonym to  \<^ML_type>\<open> string * sort list * sort\<close>

\<^item> \<^ML_type>\<open>Term.typ\<close> has the following constructors:
   \<^enum> \<^ML>\<open>Term.Type: string * typ list -> typ\<close> : The universal type constructor. Note that 
     \<open>Type("fun", [A,B])\<close> denotes the function space \<open>A \<Rightarrow> B\<close> at the ML level.
   \<^enum> \<^ML>\<open>Term.TFree: string * sort -> typ\<close> introduces free-type variables, pretty-printed
     by \<open>'a,'b,'c,...\<close>. In deduction, they are treated as constants.
   \<^enum> \<^ML>\<open>Term.TVar: indexname * sort -> typ\<close> introduces schematic type variables, pretty-printed
     by \<open>?'a,?'b,?'c,...\<close>. In deduction, they were instantiated by the unification process.

\<^item> \<^ML_type>\<open>Term.term\<close> implements the heart of a Curry-style typed \<open>\<lambda>\<close>-calculus. 
  It has the following constructors:
   \<^enum> \<^ML>\<open>Term.Const: string * typ -> term\<close> for \<^emph>\<open>constant symbols\<close>,
   \<^enum> \<^ML>\<open>Term.Free: string * typ -> term\<close> for \<^emph>\<open>free variable symbols\<close>,
   \<^enum> \<^ML>\<open>Term.Var: indexname * typ -> term\<close> for \<^emph>\<open>schematic variables\<close>, \<^eg>, \<open>?X\<close>, \<open>?Y\<close>, \<open>?Z\<close>, ... 
   \<^enum> \<^ML>\<open>Term.Bound: int -> term\<close> for bound variables encoded as deBruin indices,
   \<^enum> \<^ML>\<open>Term.Abs: string * typ * term -> term\<close> for the \<^emph>\<open>abstraction\<close>
   \<^enum> \<^ML>\<open>op $ : term * term -> term\<close> denotes the infix operator for the \<^emph>\<open>application\<close>

\<^item>  \<^ML_structure>\<open>Term\<close> provides also a number of core-exceptions relevant for type inference and
   term destruction: \<^ML>\<open>Term.TYPE: string * typ list * term list -> exn\<close> and
   \<^ML>\<open>Term.TERM: string * term list -> exn\<close>.
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

 (* three ways to write type bool: *)
 val Type("fun",[s,Type("fun",[@{typ "bool"},Type(@{type_name "bool"},[])])]) = @{typ "bool \<Rightarrow> bool \<Rightarrow> bool"};
 
\<close>
text\<open>
% NOTE:
% The quotes disappear in the pdf document output.

\<close>
text\<open>Note that the SML interpreter is configured that he will actually print a type
     \<^verbatim>\<open>Type("HOL.bool",[])\<close> just as \<^verbatim>\<open>"bool": typ\<close>, so a compact notation looking
     pretty much like a string. This can be confusing at times.\<close>

text\<open>Note, furthermore, that there is a programming API for the HOL-instance of Isabelle:
  it is contained in @{file  "$ISABELLE_HOME/src/HOL/Tools/hologic.ML"}. It offers many
  operators of the HOL logic specific constructors and destructors:\<close>

text*[T2::technical]\<open>
\<^enum>  \<^ML>\<open>HOLogic.boolT         : typ\<close> \<^vs>\<open>-0.2cm\<close>
\<^enum>  \<^ML>\<open>HOLogic.mk_Trueprop   : term -> term\<close>,  the embedder of bool to prop fundamental for HOL  \<^vs>\<open>-0.2cm\<close> 
\<^enum>  \<^ML>\<open>HOLogic.dest_Trueprop : term -> term\<close>  \<^vs>\<open>-0.2cm\<close>
\<^enum>  \<^ML>\<open>HOLogic.Trueprop_conv : conv -> conv\<close> \<^vs>\<open>-0.2cm\<close>
\<^enum>  \<^ML>\<open>HOLogic.mk_setT       : typ -> typ\<close>,  the ML level type constructor set  \<^vs>\<open>-0.2cm\<close>
\<^enum>  \<^ML>\<open>HOLogic.dest_setT     : typ -> typ\<close>,  the ML level type destructor for set  \<^vs>\<open>-0.2cm\<close>
\<^enum>  \<^ML>\<open>HOLogic.Collect_const : typ -> term\<close>  \<^vs>\<open>-0.2cm\<close>
\<^enum>  \<^ML>\<open>HOLogic.mk_Collect    : string * typ * term -> term\<close>  \<^vs>\<open>-0.2cm\<close>
\<^enum>  \<^ML>\<open>HOLogic.mk_mem        : term * term -> term\<close>  \<^vs>\<open>-0.2cm\<close>
\<^enum>  \<^ML>\<open>HOLogic.dest_mem      : term -> term * term\<close>  \<^vs>\<open>-0.2cm\<close>
\<^enum>  \<^ML>\<open>HOLogic.mk_set        : typ -> term list -> term\<close> \<^vs>\<open>-0.2cm\<close>
\<^enum>  \<^ML>\<open>HOLogic.conj_intr     : Proof.context -> thm -> thm -> thm\<close>, some HOL-level derived-inferences  \<^vs>\<open>-0.2cm\<close>
\<^enum>  \<^ML>\<open>HOLogic.conj_elim     : Proof.context -> thm -> thm * thm\<close>  \<^vs>\<open>-0.2cm\<close>
\<^enum>  \<^ML>\<open>HOLogic.conj_elims    : Proof.context -> thm -> thm list\<close>  \<^vs>\<open>-0.2cm\<close>
\<^enum>  \<^ML>\<open>HOLogic.conj          : term\<close> , some ML level logical constructors  \<^vs>\<open>-0.2cm\<close>
\<^enum>  \<^ML>\<open>HOLogic.disj          : term\<close>   \<^vs>\<open>-0.2cm\<close>
\<^enum>  \<^ML>\<open>HOLogic.imp           : term\<close>   \<^vs>\<open>-0.2cm\<close>
\<^enum>  \<^ML>\<open>HOLogic.Not           : term\<close>   \<^vs>\<open>-0.2cm\<close>
\<^enum>  \<^ML>\<open>HOLogic.mk_not        : term -> term\<close>  \<^vs>\<open>-0.2cm\<close>
\<^enum>  \<^ML>\<open>HOLogic.mk_conj       : term * term -> term\<close> \<^vs>\<open>-0.2cm\<close>
\<^enum>  \<^ML>\<open>HOLogic.dest_conj     : term -> term list\<close>   \<^vs>\<open>-0.2cm\<close>
\<^enum>  \<^ML>\<open>HOLogic.conjuncts     : term -> term list\<close>   \<^vs>\<open>-0.2cm\<close>
\<^enum>  ... 
\<close>

text*[T3::technical]\<open>In this style, extensions can be defined such as:\<close>

ML\<open>fun optionT t = Type(@{type_name "Option.option"},[t]); \<close>

subsection\<open> Type-Certification (=checking that a type annotation is consistent) \<close>

text\<open>
\<^enum>  \<^ML>\<open>Type.typ_instance: Type.tsig -> typ * typ -> bool (* raises  TYPE_MATCH *) \<close>
\<^enum>  \<^ML>\<open> Term.dummyT : typ \<close> is a joker type that can be added as place-holder during term 
   construction. Jokers can be eliminated by the type inference. \<close>
  

text*[T4::technical]\<open>
\<^enum>  \<^ML>\<open>Sign.typ_instance: theory -> typ * typ -> bool\<close>
\<^enum>  \<^ML>\<open>Sign.typ_match: theory -> typ * typ -> Type.tyenv -> Type.tyenv\<close>
\<^enum>  \<^ML>\<open>Sign.typ_unify: theory -> typ * typ -> Type.tyenv * int -> Type.tyenv * int\<close>
\<^enum>  \<^ML>\<open>Sign.const_type: theory -> string -> typ option\<close>
\<^enum>  \<^ML>\<open>Sign.certify_term: theory -> term -> term * typ * int\<close>, the function for CERTIFICATION of types
\<^enum>  \<^ML>\<open>Sign.cert_term: theory -> term -> term\<close>, short-cut for the latter
\<^enum>  \<^ML>\<open>Sign.tsig_of: theory -> Type.tsig\<close>, projects from a theory the type signature 
\<close>
text\<open> 
  \<^ML>\<open>Sign.typ_match\<close> etc. is actually an abstract wrapper on the structure 
  \<^ML_structure>\<open>Type\<close>  which contains the heart of the type inference. 
  It also contains the type substitution type \<^ML_type>\<open>Type.tyenv\<close> which is
  is actually a type synonym for \<^ML_type>\<open>(sort * typ) Vartab.table\<close> 
  which in itself is a synonym for \<^ML_type>\<open>'a Symtab.table\<close>, so 
  possesses the usual \<^ML>\<open>Symtab.empty\<close> and  \<^ML>\<open>Symtab.dest\<close> operations. \<close>  

text\<open>Note that \<^emph>\<open>polymorphic variables\<close> are treated like constant symbols 
  in the type inference; thus, the following test, that one type is an instance of the
  other, yields false:\<close>

subsubsection*[exo4::example]\<open> Example:\<close> 

ML\<open>
val ty = @{typ "'a option"};
val ty' = @{typ "int option"};

val Type("List.list",[S]) = @{typ "('a) list"}; (* decomposition example *)

val false = Sign.typ_instance @{theory}(ty', ty);
\<close>
text\<open>In order to make the type inference work, one has to consider \<^emph>\<open>schematic\<close> 
  type variables, which are more and more hidden from the Isar interface. Consequently,
  the typ antiquotation above will not work for schematic type variables and we have
  to construct them by hand on the SML level: \<close>

ML\<open> val t_schematic = Type("List.list",[TVar(("'a",0),@{sort "HOL.type"})]); \<close>

text\<open> MIND THE "'" !!! Ommitting it leads at times to VERY strange behaviour ...\<close>

text \<open>On this basis, the following \<^ML_type>\<open>Type.tyenv\<close> is constructed: \<close>
ML\<open>
val tyenv = Sign.typ_match ( @{theory}) 
               (t_schematic, @{typ "int list"})
               (Vartab.empty);            
val  [(("'a", 0), (["HOL.type"], @{typ "int"}))] = Vartab.dest tyenv;
\<close>

text\<open> Type generalization --- the conversion between free type variables and schematic 
  type variables ---  is apparently no longer part of the standard API (there is a slightly 
  more general replacement in \<^ML>\<open>Term_Subst.generalizeT_same\<close>, however). Here is a way to
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

text\<open>Now we turn to the crucial issue of type-instantiation and with a given type environment
  \<^ML>\<open>tyenv\<close>. For this purpose, one has to switch to the low-level interface 
  \<^ML_structure>\<open>Term_Subst\<close>. \<close>

subsection\<open>More operations on types\<close>

text\<open>
\<^item> \<^ML>\<open>Term_Subst.map_types_same : (typ -> typ) -> term -> term\<close>
\<^item> \<^ML>\<open>Term_Subst.map_aterms_same : (term -> term) -> term -> term\<close>
\<^item> \<^ML>\<open>Term_Subst.instantiate: typ TVars.table * term Vars.table -> term -> term\<close>
\<^item> \<^ML>\<open>Term_Subst.instantiateT: typ TVars.table -> typ -> typ\<close>
\<^item> \<^ML>\<open>Term_Subst.generalizeT: Names.set -> int -> typ -> typ\<close>
                        this is the standard type generalisation function !!!
                        only type-frees in the string-list were taken into account. 
\<^item> \<^ML>\<open>Term_Subst.generalize: Names.set * Names.set -> int -> term -> term\<close>
                        this is the standard term generalisation function !!!
                        only type-frees and frees in the string-lists were taken 
                        into account. 
\<close>



text \<open>Apparently, a bizarre conversion between the old-style interface and 
  the new-style  \<^ML>\<open>tyenv\<close> is necessary. See the following example.\<close>
ML\<open>
val S = Vartab.dest tyenv;
val S' = (map (fn (s,(t,u)) => ((s,t),u)) S) : ((indexname * sort) * typ) list;
         (* it took me quite some time to find out that these two type representations,
            obscured by a number of type-synonyms, where actually identical. *)
val ty = t_schematic;
val ty' = Term_Subst.instantiateT S' t_schematic;

(* Don't know how to build a typ TVars.table *)
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

subsection\<open>Another Approach for Typed Parsing\<close>

text\<open>Another example for influencing @{ML "Syntax.read_term"} by modifying
the @{ML_type "Proof.context"}: \<close>

definition "zz = ()" 
ML\<open>@{term zz}\<close>  (* So : @(term "zz"} is now a constant*) 
ML\<open>val  Free ("zz", ty) = Proof_Context.add_fixes 
                            [(@{binding "zz"}, SOME @{typ nat}, NoSyn)] @{context}
                          |> (fn (S, ctxt) => (writeln (String.concat S); 
                                               Syntax.read_term ctxt "zz"));
                (* So : @(term "zz"} is here a free variable. *) \<close>
ML\<open>@{term zz}\<close>  (* So : @(term "zz"} is now a constant again.*) 
locale Z =
  fixes zz :: nat
begin
  ML\<open>@{term "(zz)"}\<close>
end

lemma True
proof - fix a :: nat
  show True
    ML_prf \<open>@{term a}\<close>
    term a
    oops





subsection*[t233::technical]\<open> Theories and the Signature API\<close>  
text\<open>
\<^enum> \<^ML>\<open>Sign.tsig_of : theory -> Type.tsig\<close> extracts the type-signature of a theory
\<^enum> \<^ML>\<open>Sign.syn_of  : theory -> Syntax.syntax\<close> extracts the constant-symbol signature 
\<^enum> \<^ML>\<open>Sign.of_sort : theory -> typ * sort -> bool\<close> decides that a type belongs to a sort.
\<close>

subsection*[t234::technical]\<open>\<^ML_structure>\<open>Thm\<close>'s and the LCF-Style, "Mikro"-Kernel \<close>  
text\<open> 
  The basic constructors and operations on theorems \<^file>\<open>$ISABELLE_HOME/src/Pure/thm.ML\<close>,
  a set of derived (Pure) inferences can be found in \<^file>\<open>$ISABELLE_HOME/src/Pure/drule.ML\<close>.

  The main types provided by structure \<^verbatim>\<open>thm\<close> are certified types \<^ML_type>\<open>Thm.ctyp\<close>, 
  certified terms \<^ML_type>\<open>Thm.cterm\<close>, \<^ML_type>\<open>Thm.thm\<close> as well as conversions \<^ML_type>\<open>Thm.conv\<close> 
  \<^ie>, transformation operations of  \<^ML_type>\<open>Thm.thm\<close>s to logically equivalent ones.

  Errors were reported with the  \<^ML>\<open>CTERM: string * cterm list -> exn\<close>-exceptions.

  Over this kernel, two infix main operations were provided:
  \<^enum> \<^ML>\<open>op RS: thm * thm -> thm\<close> resolved the conclusion of left argument into the left-most
    assumption of the right arguement, while
  \<^enum> \<^ML>\<open>op RSN: thm * (int * thm) -> thm\<close> resolves the conclusion of the left argument into
    the nth assumption of the right argument, so generalizes \<^ML>\<open>op RS\<close>.

  Errors of the resolution operations were reported by 
  \<^ML>\<open>THM : string * int * thm list -> exn\<close>.

  At a glance, the very heart of the kernel is represented as follows (UNSAFE):
\<close>

ML\<open>
signature BASIC_THM' =
sig
  type ctyp
  type cterm
  exception CTERM of string * cterm list
  type thm
  type conv = cterm -> thm
  exception THM of string * int * thm list
  val RSN: thm * (int * thm) -> thm
  val RS: thm * thm -> thm
end;
\<close>

text\<open>Certification of types and terms on the kernel-level is done by the generators:\<close>
text\<open>
\<^item> \<^ML>\<open> Thm.global_ctyp_of: theory -> typ -> ctyp\<close>
\<^item> \<^ML>\<open> Thm.ctyp_of: Proof.context -> typ -> ctyp\<close>
\<^item> \<^ML>\<open> Thm.global_cterm_of: theory -> term -> cterm\<close>
\<^item> \<^ML>\<open> Thm.cterm_of: Proof.context -> term -> cterm\<close>
\<close>


text\<open>... which perform type-checking in the given theory context in order to make a type
     or term "admissible" for the kernel.\<close>

text\<open>These operations were internally used in the ML-antiquotation:\<open>ML\<open>\<^cterm>\<open>zero\<close>\<close>\<close> yielding:\<close>
ML\<open>\<^cterm>\<open>zero\<close>\<close>

text\<open> We come now to the very heart of the LCF-Kernel of Isabelle, which 
     provides the fundamental inference rules of Isabelle/Pure. 

   Besides a number of destructors on \<^ML_type>\<open>thm\<close>'s,
  the abstract data-type \<^ML_type>\<open>thm\<close> is used for logical objects of the form 
  \<open>\<Gamma> \<turnstile>\<^sub>\<theta> \<phi>\<close>, where \<open>\<Gamma>\<close> represents a set of local assumptions,
  \<open>\<theta>\<close> the global context or  \<^ML_type>\<open>theory\<close> in which a formula \<open>\<phi>\<close> 
  has been constructed just by applying the following operations representing 
  the logical kernel inference rules:

\<^item>  \<^ML>\<open> Thm.assume: cterm -> thm\<close>
\<^item>  \<^ML>\<open> Thm.implies_intr: cterm -> thm -> thm\<close>
\<^item>  \<^ML>\<open> Thm.implies_elim: thm -> thm -> thm\<close>
\<^item>  \<^ML>\<open> Thm.forall_intr: cterm -> thm -> thm\<close>
\<^item>  \<^ML>\<open> Thm.forall_elim: cterm -> thm -> thm\<close>
\<^item>  \<^ML>\<open> Thm.transfer : theory -> thm -> thm\<close>
\<^item>  \<^ML>\<open> Thm.generalize: Names.set * Names.set -> int -> thm -> thm\<close>
\<^item>  \<^ML>\<open> Thm.instantiate: ctyp TVars.table * cterm Vars.table -> thm -> thm\<close>
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
 \<open>\<Gamma> \<turnstile>\<^sub>\<theta> \<phi>\<close>   \qquad \qquad     \<open>\<theta> \<sqsubseteq> \<theta>'\<close>  
\justifies
 \<open>\<Gamma> \<turnstile>\<^sub>\<theta>\<^sub>' \<phi>\<close>  \qquad \qquad
\end{prooftree}
\]
  which is a consequence of explicit theories  characteristic for Isabelle's LCF-kernel design
  and a remarkable difference to its sisters HOL-Light and HOL4; instead of transfer, these systems
  reconstruct proofs in an enlarged global context instead of taking the result and converting it.\<close>

text\<open>Besides the meta-logical (Pure) implication \<open>_ \<Longrightarrow> _\<close>, the Kernel axiomatizes
  also a Pure-Equality \<open>_ \<equiv> _\<close> used for definitions of constant symbols: 
\<^item>  \<^ML>\<open> Thm.reflexive: cterm -> thm\<close>
\<^item>  \<^ML>\<open> Thm.symmetric: thm -> thm\<close>
\<^item>  \<^ML>\<open> Thm.transitive: thm -> thm -> thm\<close>
\<close>

text\<open>The operation \<^ML>\<open> Thm.trivial: cterm -> thm \<close>
  ... produces the elementary tautologies of the form \<^prop>\<open>A \<Longrightarrow> A\<close>,
  an operation used to start a backward-style proof.\<close>

text\<open>The elementary conversions are:

\<^item>  \<^ML>\<open>Thm.beta_conversion: bool -> conv\<close>
\<^item>  \<^ML>\<open>Thm.eta_conversion: conv\<close>
\<^item>  \<^ML>\<open>Thm.eta_long_conversion: conv\<close>
\<close>

text\<open>On the level of \<^ML_structure>\<open>Drule\<close>, a number of higher-level operations is established, 
     which is in part accessible by a number of forward-reasoning notations on Isar-level.

\<^item>  \<^ML>\<open> op RLN: thm list * (int * thm list) -> thm list\<close>
\<^item>  \<^ML>\<open> op RL: thm list * thm list -> thm list\<close>
\<^item>  \<^ML>\<open> op MRS: thm list * thm -> thm\<close>
\<^item>  \<^ML>\<open> op OF: thm * thm list -> thm\<close>
\<^item>  \<^ML>\<open> op COMP: thm * thm -> thm\<close>
\<close>


subsection*[t235::technical]\<open> \<^ML_structure>\<open>Theory\<close>'s \<close>

text \<open> This structure yields the abstract datatype \<^ML_structure>\<open>Theory\<close> which becomes the content of 
  \<^ML_type>\<open>Context.theory\<close>. In a way, the LCF-Kernel registers itself into the Nano-Kernel,
  which inspired me (bu) to this naming. However, not that this is a mental model: the Nano-Kernel
  offers ab initio many operations directly linked to its main purpose: incommodating the 
  micro-kernel and its management of local and global contexts.
\<close>

text\<open>
@{theory_text [display] 
\<open>
intern Theory.Thy; 

datatype thy = Thy of
 {pos: Position.T,
  id: serial,
  axioms: term Name_Space.table,
  defs: Defs.T,
  wrappers: wrapper list * wrapper list};
\<close>}

\<^item>  \<^ML>\<open>Theory.check: {long: bool} -> Proof.context -> string * Position.T -> theory\<close>
\<^item>  \<^ML>\<open>Theory.local_setup: (Proof.context -> Proof.context) -> unit\<close>
\<^item>  \<^ML>\<open>Theory.setup: (theory -> theory) -> unit\<close>  (* The thing to extend the table of "command"s with parser - callbacks. *)
\<^item>  \<^ML>\<open>Theory.get_markup: theory -> Markup.T\<close>
\<^item>  \<^ML>\<open>Theory.axiom_table: theory -> term Name_Space.table\<close>
\<^item>  \<^ML>\<open>Theory.axiom_space: theory -> Name_Space.T\<close>
\<^item>  \<^ML>\<open>Theory.all_axioms_of: theory -> (string * term) list\<close>
\<^item>  \<^ML>\<open>Theory.defs_of: theory -> Defs.T\<close>
\<^item>  \<^ML>\<open>Theory.join_theory: theory list -> theory\<close>
\<^item>  \<^ML>\<open>Theory.at_begin: (theory -> theory option) -> theory -> theory\<close>
\<^item>  \<^ML>\<open>Theory.at_end: (theory -> theory option) -> theory -> theory\<close>
\<^item>  \<^ML>\<open>Theory.begin_theory: string * Position.T -> theory list -> theory\<close>
\<^item>  \<^ML>\<open>Theory.end_theory: theory -> theory\<close>
\<close>

section*[t26::technical]\<open>Advanced Specification Constructs\<close>
text\<open>Isabelle is built around the idea that system components were built on top
of the kernel in order to give the user high-level specification constructs 
--- rather than inside as in the Coq kernel that foresees, for example, data-types
and primitive recursors already in the basic \<open>\<lambda>\<close>-term language.
Therefore, records, definitions, type-definitions, recursive function definitions
are supported by packages that belong to the \<^emph>\<open>components\<close> strata. 
With the exception of the \<^ML>\<open>Specification.axiomatization\<close> construct, they
are all-together built as composition of conservative extensions.

The components are a bit scattered in the architecture. A relatively recent and
high-level component (more low-level components such as \<^ML>\<open>Global_Theory.add_defs\<close>
exist) for definitions and axiomatizations is here:
\<close>

text\<open>
\<^item>  \<^ML>\<open>Specification.definition: (binding * typ option * mixfix) option ->
        (binding * typ option * mixfix) list -> term list -> Attrib.binding * term ->
        local_theory -> (term * (string * thm)) * local_theory\<close>
\<^item>  \<^ML>\<open>Specification.definition_cmd: (binding * string option * mixfix) option ->
        (binding * string option * mixfix) list -> string list -> Attrib.binding * string ->
         bool -> local_theory -> (term * (string * thm)) * local_theory\<close>
\<^item>  \<^ML>\<open>Specification.axiomatization: (binding * typ option * mixfix) list ->
        (binding * typ option * mixfix) list -> term list ->
        (Attrib.binding * term) list -> theory -> (term list * thm list) * theory\<close>
\<^item>  \<^ML>\<open>Specification.axiomatization_cmd: (binding * string option * mixfix) list ->
        (binding * string option * mixfix) list -> string list ->
        (Attrib.binding * string) list -> theory -> (term list * thm list) * theory\<close>
\<^item>  \<^ML>\<open>Specification.axiom: Attrib.binding * term -> theory -> thm * theory\<close>
\<^item>  \<^ML>\<open>Specification.abbreviation: Syntax.mode -> (binding * typ option * mixfix) option ->
        (binding * typ option * mixfix) list -> term -> bool -> local_theory -> local_theory\<close>
\<^item>  \<^ML>\<open>Specification.abbreviation_cmd: Syntax.mode -> (binding * string option * mixfix) option ->
        (binding * string option * mixfix) list -> string -> bool -> local_theory -> local_theory\<close>
\<close>


text\<open>
Note that the interface is mostly based on \<^ML_type>\<open>local_theory\<close>, which is a synonym to
\<^ML_type>\<open>Proof.context\<close>. Need to lift this to a global system transition ?
Don't worry, \<^ML>\<open>Named_Target.theory_map: (local_theory -> local_theory) -> theory -> theory\<close> 
does the trick.
\<close>

subsection*[t261::example]\<open>Example\<close>

text\<open>Suppose that we want do  \<^theory_text>\<open>definition I :: "'a \<Rightarrow> 'a" where "I x = x"\<close> at the ML-level.
We construct our defining equation and embed it as a \<^typ>\<open>prop\<close> into Pure.
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
                        #2 o Specification.definition decl params prems spec)
    in cmd args
    end;
in  Named_Target.theory_map (mk_def "I" @{here} )
end\<close>

thm I_def
text\<open>Voilà.\<close>

section*[t24::technical]\<open>Backward Proofs: Tactics, Tacticals and Goal-States\<close>

text\<open>At this point, we leave the Pure-Kernel and start to describe the first layer on top
  of it, involving support for specific styles of reasoning and automation of reasoning.\<close>

text\<open> \<^ML_type>\<open>tactic\<close>'s are in principle \<^emph>\<open>relations\<close> on theorems  \<^ML_type>\<open>thm\<close>; the relation is
  lazy and encoded as function of type \<^ML_type>\<open>thm -> thm Seq.seq\<close>.
  This gives a natural way to represent the fact that HO-Unification
  (and therefore the mechanism of rule-instantiation) are non-deterministic in principle.
  Heuristics may choose particular preferences between 
  the theorems in the range of this relation, but the Isabelle Design accepts this fundamental 
  fact reflected at this point in the prover architecture. 
  This potentially infinite relation is implemented by a function of theorems to lazy lists 
  over theorems, which gives both sufficient structure for heuristic
  considerations as well as a nice algebra, called \<^ML_structure>\<open>Tactical\<close>'s, providing a bottom element
  \<^ML>\<open>no_tac\<close> (the function that always fails), the top-element \<^ML>\<open>all_tac\<close>
   (the function that never fails), sequential composition  \<^ML>\<open>op THEN\<close>, (serialized) 
  non-deterministic composition  \<^ML>\<open>op ORELSE\<close>, conditionals, repetitions over lists, etc.
  The following is an excerpt of \<^file>\<open>~~/src/Pure/tactical.ML\<close>:\<close>


text\<open> More specialized variants of  \<^ML_structure>\<open>Tactical\<close>'s are:

\<^item>  \<^ML>\<open>op THEN': ('a -> tactic) * ('a -> tactic) -> 'a -> tactic\<close> -- lifted version 
\<^item>  \<^ML>\<open>op ORELSE': ('a -> tactic) * ('a -> tactic) -> 'a -> tactic\<close> -- lifted version 
\<^item>  \<^ML>\<open>op TRY: tactic -> tactic\<close>  -- option
\<^item>  \<^ML>\<open>op EVERY: tactic list -> tactic\<close> -- sequential enchainment
\<^item>  \<^ML>\<open>op EVERY': ('a -> tactic) list -> 'a -> tactic\<close> -- lifted version
\<^item>  \<^ML>\<open>op FIRST: tactic list -> tactic\<close> -- alternative enchainment
\<^item>  etc.

\<close>


text\<open>The next layer in the architecture describes  \<^ML_type>\<open>tactic\<close>'s, i.e. basic operations on 
  theorems  in a backward reasoning style (bottom up development of proof-trees). An initial 
  goal-state for some property \<^prop>\<open>A\<close> --- the \<^emph>\<open>goal\<close> --- is constructed via the kernel 
  \<^ML>\<open>Thm.trivial\<close>-operation into  \<^prop>\<open>A \<Longrightarrow> A\<close>, and tactics either refine the premises --- the 
  \<^emph>\<open>subgoals\<close> of this meta-implication --- producing  more and more of them or eliminate them 
  in subsequent goal-states. Subgoals of the form \<^prop>\<open>B\<^sub>1 \<Longrightarrow> B\<^sub>2 \<Longrightarrow> A \<Longrightarrow> B\<^sub>3 \<Longrightarrow> B\<^sub>4 \<Longrightarrow> A\<close> can be 
  eliminated via the \<^ML>\<open>Tactic.assume_tac\<close>-tactic, and a subgoal  \<^prop>\<open>C\<^sub>m\<close> can be refined via the 
  theorem \<^prop>\<open>E\<^sub>1 \<Longrightarrow> E\<^sub>2 \<Longrightarrow> E\<^sub>3 \<Longrightarrow> C\<^sub>m\<close> the \<^ML>\<open>Tactic.resolve_tac\<close> - tactic to new subgoals
  \<^prop>\<open>E\<^sub>1\<close>, \<^prop>\<open>E\<^sub>2\<close>, \<^prop>\<open>E\<^sub>3\<close>. In case that a theorem used for resolution has no premise \<^prop>\<open>E\<^sub>i\<close>, 
  the subgoal  \<^prop>\<open>C\<^sub>m\<close> is also eliminated ("closed").
  
  The following abstract of the most commonly used \<^ML_type>\<open>tactic\<close>'s drawn from
  \<^file>\<open>~~/src/Pure/tactic.ML\<close> are summarized as follows:

\<^item>  \<^ML>\<open> assume_tac: Proof.context -> int -> tactic\<close> 
\<^item>  \<^ML>\<open> compose_tac: Proof.context -> (bool * thm * int) -> int -> tactic\<close>
\<^item>  \<^ML>\<open> resolve_tac: Proof.context -> thm list -> int -> tactic\<close>
\<^item>  \<^ML>\<open> eresolve_tac: Proof.context -> thm list -> int -> tactic\<close>
\<^item>  \<^ML>\<open> forward_tac: Proof.context -> thm list -> int -> tactic\<close>
\<^item>  \<^ML>\<open> dresolve_tac: Proof.context -> thm list -> int -> tactic\<close>
\<^item>  \<^ML>\<open> rotate_tac: int -> int -> tactic\<close>
\<^item>  \<^ML>\<open> defer_tac: int -> tactic\<close>
\<^item>  \<^ML>\<open> prefer_tac: int -> tactic\<close>
\<^item>  ...
\<close>

text\<open>Note that "applying a rule" is a fairly complex operation in the Extended Isabelle Kernel,
  i.e. the tactic layer. It involves at least four phases, interfacing a theorem 
  coming from the global context $\theta$ (=theory), be it axiom or derived, into a given goal-state.
\<^item> \<^emph>\<open>generalization\<close>. All free variables in the theorem were replaced by schematic variables.
  For example, \<^term>\<open>x + y = y + x\<close> is converted into 
  \<open>?x + ?y = ?y + ?x\<close>. 
  By the way, type variables were treated equally.
\<^item> \<^emph>\<open>lifting over assumptions\<close>. If a subgoal is of the form: 
  \<^prop>\<open>B\<^sub>1 \<Longrightarrow> B\<^sub>2 \<Longrightarrow> A\<close> and we have a theorem \<^prop>\<open>D\<^sub>1 \<Longrightarrow> D\<^sub>2 \<Longrightarrow> A\<close>, then before
  applying the theorem, the premisses were \<^emph>\<open>lifted\<close> resulting in the logical refinement:
  \<^prop>\<open>(B\<^sub>1 \<Longrightarrow> B\<^sub>2 \<Longrightarrow> D\<^sub>1) \<Longrightarrow> (B\<^sub>1 \<Longrightarrow> B\<^sub>2 \<Longrightarrow> D\<^sub>2) \<Longrightarrow> A\<close>. Now, \<^ML>\<open>resolve_tac\<close>, for example,
  will replace the subgoal  \<^prop>\<open>B\<^sub>1 \<Longrightarrow> B\<^sub>2 \<Longrightarrow> A\<close> by the subgoals 
  \<^prop>\<open>B\<^sub>1 \<Longrightarrow> B\<^sub>2 \<Longrightarrow> D\<^sub>1\<close>  and \<^prop>\<open>B\<^sub>1 \<Longrightarrow> B\<^sub>2 \<Longrightarrow> D\<^sub>2\<close>. Of course, if the theorem wouldn't
  have assumptions \<^prop>\<open>D\<^sub>1\<close> and \<^prop>\<open>D\<^sub>2\<close>, the subgoal  \<^prop>\<open>A\<close> would be replaced by 
  \<^bold>\<open>nothing\<close>, i.e. deleted.
\<^item> \<^emph>\<open>lifting over parameters\<close>. If a subgoal is meta-quantified like in:
  \<^prop>\<open>\<And> x y z. A x y z\<close>, then a theorem like  \<^prop>\<open>D\<^sub>1 \<Longrightarrow> D\<^sub>2 \<Longrightarrow> A\<close> is \<^emph>\<open>lifted\<close>  
  to \<^prop>\<open>\<And> x y z. D\<^sub>1' \<Longrightarrow> D\<^sub>2' \<Longrightarrow> A'\<close>, too. Since free variables occurring in \<^prop>\<open>D\<^sub>1\<close>, 
  \<^prop>\<open>D\<^sub>2\<close> and \<^prop>\<open>A\<close> have been replaced by schematic variables (see phase one),
  they must be replaced by parameterized schematic variables, i. e. a kind of skolem function.
  For example, \<open>?x + ?y = ?y + ?x\<close> would be lifted to 
  \<open>\<And>  x y z. ?x x y z + ?y x y z = ?y x y z + ?x x y z\<close>. This way, the lifted theorem
  can be instantiated by the parameters  \<open>x y z\<close> representing "fresh free variables"
  used for this sub-proof. This mechanism implements their logically correct bookkeeping via
  kernel primitives.
\<^item> \<^emph>\<open>Higher-order unification (of schematic type and term variables)\<close>.
  Finally, for all these schematic variables, a solution must be found.
  In the case of \<^ML>\<open>resolve_tac\<close>, the conclusion of the (doubly lifted) theorem must
  be equal to the conclusion of the subgoal, so  \<^term>\<open>A\<close> must be \<open>\<alpha>/\<beta>\<close>-equivalent to
  \<^term>\<open>A'\<close> in the example above, which is established by a higher-order unification
  process. It is a bit unfortunate that for implementation efficiency reasons, a very substantial
  part of the code for HO-unification is in the kernel module \<^ML_type>\<open>thm\<close>, which makes this
  critical component of the architecture larger than necessary.  
\<close>

text\<open>In a way, the two lifting processes represent an implementation of the conversion between
  Gentzen Natural Deduction (to which Isabelle/Pure is geared) reasoning and 
  Gentzen Sequent Deduction.\<close>


section*[goalp::technical]\<open>The classical goal package\<close>
text\<open>The main mechanism in Isabelle as an LCF-style system is to produce \<^ML_type>\<open>thm\<close>'s 
  in backward-style via tactics as described in @{technical "t24"}. Given a context
  --- be it global as \<^ML_type>\<open>theory\<close> or be it inside a proof-context as  \<^ML_type>\<open>Proof.context\<close>,
  user-programmed verification of (type-checked) terms or just strings can be done via the 
  operations:

\<^item>  \<^ML>\<open>Goal.prove_internal : Proof.context -> cterm list -> cterm -> (thm list -> tactic) -> thm\<close>
\<^item>  \<^ML>\<open>Goal.prove_global   :  theory -> string list -> term list -> term -> 
                                ({context: Proof.context, prems: thm list} -> tactic) -> thm\<close>
\<^item>  ... and many more variants. 
\<close>

subsection*[ex211::example]\<open>Proof Example (Low-level)\<close>  

text\<open>Take this proof at Isar Level as example:\<close>

lemma X  : "(10::int) + 2 = 12" by simp

declare X[simp]

text\<open>This represents itself at the SML interface as follows:\<close>

ML\<open>
structure SimpleSampleProof =
struct

val tt = HOLogic.mk_Trueprop (Syntax.read_term @{context} "(10::int) + 2 = 12");
         (* read_term parses and type-checks its string argument;
            HOLogic.mk_Trueprop wraps the embedder from @{ML_type "bool"} to  
            @{ML_type "prop"} from Pure. *)

fun derive_thm name term lthy = 
          Goal.prove lthy          (* global context *)
         [name]                    (* name ? *)
         []                        (* local assumption context *)
         (term)                    (* parsed goal *)
         (fn _ => simp_tac lthy 1) (* proof tactic *)
         |> Thm.close_derivation \<^here> (* some cleanups *);

val thm111_intern = derive_thm "thm111" tt @{context} (* just for fun at the ML level *)

fun store_thm name thm lthy = 
         lthy |> snd o Local_Theory.note ((Binding.name name, []), [thm]) 


val prove_n_store = (Named_Target.theory_map(fn lthy => 
                                       let val thm = derive_thm "thm111" tt lthy
                                       in lthy |> store_thm "thm111" thm end));

end
\<close>

text\<open>Converting a local theory transformation into a global one:\<close>
setup\<open>SimpleSampleProof.prove_n_store\<close>

text\<open>... and there it is in the global (Isar) context:\<close>
thm "thm111"





section\<open>Toplevel --- aka. ''The Isar Engine''\<close>

text\<open>  The main structure of the Isar-engine is \<^ML_structure>\<open>Toplevel\<close>.
   The Isar Toplevel (aka "the Isar engine" or the "Isar Interpreter") is a transaction
   machine sitting over the Isabelle Kernel steering some asynchronous evaluation during the
   evaluation of Isabelle/Isar input, usually stemming from processing Isabelle \<^verbatim>\<open>.thy\<close>-files. \<close>

subsection*[tplstate::technical] \<open>Toplevel Transaction Management in the Isar-Engine\<close>
text\<open>
   The  structure \<^ML_structure>\<open>Toplevel\<close>  provides an internal \<^ML_type>\<open>state\<close> with the 
   necessary infrastructure ---  i.e. the operations to pack and unpack theories and
   queries  on it:

\<^item> \<^ML>\<open> Toplevel.theory_toplevel: theory -> Toplevel.state\<close>
\<^item> \<^ML>\<open> Toplevel.init_toplevel: unit -> Toplevel.state\<close>
\<^item> \<^ML>\<open> Toplevel.is_toplevel: Toplevel.state -> bool\<close>
\<^item> \<^ML>\<open> Toplevel.is_theory: Toplevel.state -> bool\<close>
\<^item> \<^ML>\<open> Toplevel.is_proof: Toplevel.state -> bool\<close>
\<^item> \<^ML>\<open> Toplevel.is_skipped_proof: Toplevel.state -> bool\<close>
\<^item> \<^ML>\<open> Toplevel.level: Toplevel.state -> int\<close>
\<^item> \<^ML>\<open> Toplevel.context_of: Toplevel.state -> Proof.context\<close>
  extracts the local context 
\<^item> \<^ML>\<open> Toplevel.generic_theory_of: Toplevel.state -> generic_theory\<close>
  extracts the generic (local or global) context 
\<^item> \<^ML>\<open> Toplevel.theory_of: Toplevel.state -> theory\<close>
   extracts the global context 
\<^item> \<^ML>\<open> Toplevel.proof_of: Toplevel.state -> Proof.state\<close>
\<^item> \<^ML>\<open> Toplevel.presentation_context: Toplevel.state -> Proof.context\<close>
\<^item>  ... 
\<close>

text\<open>  Type \<^ML_type>\<open>Toplevel.state\<close> represents Isar toplevel states, which are normally 
  manipulated through the concept of toplevel transitions only.
  This type is constructed as the sum of \<^emph>\<open>empty state\<close>,  \<^ML_type>\<open>Context.generic\<close>
  (synonym to  \<^ML_type>\<open>generic_theory\<close>) and enriched versions of proof states or
  abort proofs.
\<close>


subsection*[transmgt::technical] \<open>Toplevel Transaction Management in the Isar-Engine\<close>

text\<open> The extensibility of Isabelle as a system framework depends on a number of tables,
  into which various concepts commands, ML-antiquotations, text-antiquotations, cartouches, ...
  can be entered via a late-binding on the fly. 
 
  The main operations to toplevel transitions are:

 \<^item> \<^ML>\<open>Toplevel.keep: (Toplevel.state -> unit) -> Toplevel.transition -> Toplevel.transition\<close>
   adjoins a diagnostic command
 \<^item> \<^ML>\<open>Toplevel.theory: (theory -> theory) -> Toplevel.transition -> Toplevel.transition\<close>
   adjoins a theory transformer.
 \<^item> \<^ML>\<open>Toplevel.generic_theory: (generic_theory -> generic_theory) -> Toplevel.transition -> Toplevel.transition\<close>
 \<^item> \<^ML>\<open>Toplevel.theory': (bool -> theory -> theory) -> Toplevel.transition -> Toplevel.transition\<close>
 \<^item> \<^ML>\<open>Toplevel.exit: Toplevel.transition -> Toplevel.transition\<close>
 \<^item> \<^ML>\<open>Toplevel.ignored: Position.T -> Toplevel.transition\<close>
 \<^item> \<^ML>\<open>Toplevel.present_local_theory:  (xstring * Position.T) option ->
                       (Toplevel.state -> Latex.text) -> Toplevel.transition -> Toplevel.transition\<close>

\<close>
subsection*[cmdbinding::technical] \<open>Toplevel Transaction Management in the Isar-Engine\<close>
text\<open>
 Toplevel transitions can finally be registered together with commandkeywords and 
 IDE information into the toplevel.
 The global type of this key function for extending the Isar toplevel is, together
 with a few query operations on the state of the toplevel:
 \<^item>  \<^ML>\<open>Outer_Syntax.command : Outer_Syntax.command_keyword -> string -> 
                              (Toplevel.transition -> Toplevel.transition) parser -> unit\<close>,
 \<^item>  \<^ML>\<open>Document.state : unit -> Document.state\<close>, giving the state as a "collection" of named
     nodes, each consisting of an editable list of commands, associated with asynchronous 
     execution process,
 \<^item>  \<^ML>\<open>Session.get_keywords : unit -> Keyword.keywords\<close>, this looks to be session global,
 \<^item>  \<^ML>\<open>Thy_Header.get_keywords : theory -> Keyword.keywords\<close> this looks to be just theory global.


  A paradigmatic example is the \<^ML>\<open>Outer_Syntax.command\<close>-operation, which ---
  representing itself as a toplevel system transition --- allows to define a new 
  command section and bind its syntax and semantics at a specific keyword.
  Calling \<^ML>\<open>Outer_Syntax.command\<close> creates an implicit \<^ML>\<open>Theory.setup\<close> with an entry
  for a call-back function, which happens to be a parser that must have as side-effect   
  a Toplevel-transition-transition. 
  Registers  \<^ML_type>\<open>Toplevel.transition -> Toplevel.transition\<close> parsers to the 
  Isar interpreter.\<close>

text\<open>The file \<^file>\<open>~~/src/HOL/Examples/Commands.thy\<close> shows some example Isar command definitions, with the 
     all-important theory header declarations for outer syntax keywords.\<close>
 
text\<open>@{ML_structure Pure_Syn}\<close>

subsubsection*[ex1137::example]\<open>Examples: \<^theory_text>\<open>text\<close>\<close>
text\<open> The integration of the  \<^theory_text>\<open>text\<close>-command is done as follows:

 @{ML [display]\<open>
  Outer_Syntax.command ("text", @{here}) "formal comment (primary style)"
    (Parse.opt_target -- Parse.document_source >> Document_Output.document_output 
                                                  {markdown = true, markup = I})
 \<close>}

 where \<^ML>\<open>Document_Output.document_output\<close> is the defining operation for the 
 "diagnostic" (=side-effect-free) toplevel operation.
  \<^ML>\<open>Document_Output.document_output\<close> looks as follows:

 @{ML [display]\<open>let fun document_reports txt =
  let val pos = Input.pos_of txt in
    [(pos, Markup.language_document (Input.is_delimited txt)),
     (pos, Markup.plain_text)]
  end;
fun document_output {markdown, markup} (loc, txt) =
  let
    fun output st =
      let
        val ctxt = Toplevel.presentation_context st;
        val _ = Context_Position.reports ctxt (document_reports txt);
      in txt |> Document_Output.output_document ctxt {markdown = markdown} |> markup end;
  in
    Toplevel.present (fn st =>
      (case loc of
        NONE => output st
      | SOME (_, pos) =>
          error ("Illegal target specification -- not a theory context" ^ Position.here pos))) o
    Toplevel.present_local_theory loc output
  end in () end
\<close>}
\<close>

subsubsection*[ex1138::example]\<open>Examples: \<^theory_text>\<open>ML\<close>\<close>

text\<open>
 The integration of the  \<^theory_text>\<open>ML\<close>-command is done as follows:

 @{ML [display]\<open>
  Outer_Syntax.command ("ML", \<^here>) "ML text within theory or local theory"
    (Parse.ML_source >> (fn source =>
      Toplevel.generic_theory
        (ML_Context.exec (fn () =>
            ML_Context.eval_source (ML_Compiler.verbose true ML_Compiler.flags) source) #>
          Local_Theory.propagate_ml_env)))
  \<close>}
\<close>


subsection\<open>Miscellaneous\<close>

text\<open>Here are a few queries relevant for the global config of the isar engine:\<close>
ML\<open> Document.state();\<close>
ML\<open> Session.get_keywords(); (* this looks to be  session global. *) \<close>
ML\<open> Thy_Header.get_keywords @{theory};(* this looks to be really theory global. *) \<close>

  
subsection*[conf::technical]\<open> Configuration Flags in the Isar-engine. \<close>
text\<open>The toplevel also provides an infrastructure for managing configuration options 
  for system components. Based on a sum-type @{ML_type Config.value } 
  with the alternatives \<^verbatim>\<open> Bool of bool | Int of int | Real of real | String of string\<close>
  and building the parametric configuration types @{ML_type "'a Config.T" } and the
  instance  \<^verbatim>\<open>type raw = value T\<close>, for all registered configurations the protocol:


  \<^item>  \<^ML>\<open>Config.get : Proof.context -> 'a Config.T -> 'a\<close>
  \<^item>  \<^ML>\<open>Config.map: 'a Config.T -> ('a -> 'a) -> Proof.context -> Proof.context\<close>  
  \<^item>  \<^ML>\<open>Config.put: 'a Config.T -> 'a -> Proof.context -> Proof.context\<close>  
  \<^item>  \<^ML>\<open>Config.get_global: theory -> 'a Config.T -> 'a\<close>  
  \<^item>  \<^ML>\<open>Config.map_global: 'a Config.T -> ('a -> 'a) -> theory -> theory\<close>  
  \<^item>  \<^ML>\<open>Config.put_global: 'a Config.T -> 'a -> theory -> theory\<close>  
  \<^item>  ... etc. is defined.
\<close>


subsubsection*[ex::example]\<open>Example registration of a config attribute \<close>
text\<open>The attribute XS232 is initialized by false:\<close>
ML\<open> 
val (XS232, XS232_setup)
     = Attrib.config_bool \<^binding>\<open>XS232\<close> (K false);

val _ = Theory.setup XS232_setup;\<close>

text \<open>... which could also be achieved by \<open>setup\<open>XS232_setup\<close>\<close>. \<close>

subsubsection*[ex33333::example]\<open>Defining a high-level attribute:\<close>
ML\<open> 
Attrib.setup \<^binding>\<open>simp\<close> (Attrib.add_del Simplifier.simp_add Simplifier.simp_del)
                            "declaration of Simplifier rewrite rule"
\<close>


subsection*[ex333::example]\<open>A Hack:\<close>

text\<open>Another mechanism are global synchronised variables:\<close>
ML\<open>
           
  val C = Synchronized.var "Pretty.modes" "latEEex"; 
  (* Synchronized: a mechanism to bookkeep global
     variables with synchronization mechanism included *)
  Synchronized.value C;\<close>  


subsection*[ex213::example]\<open>A Definition Command (High-level)\<close>  

text\<open>A quite complex example is drawn from the Theory \<^verbatim>\<open>Clean\<close>; it generates \<close>

ML\<open>Specification.definition\<close>

ML\<open>
structure HLDefinitionSample = 
struct
fun cmd (decl, spec, prems, params) = #2 o Specification.definition decl params prems spec

fun MON_SE_T res state = state --> optionT(HOLogic.mk_prodT(res,state));

fun push_eq binding  name_op rty sty lthy = 
         let val mty = MON_SE_T rty sty 
             val thy = Proof_Context.theory_of lthy
             val term = Free("\<sigma>",sty)
         in  mk_meta_eq((Free(name_op, mty) $ Free("\<sigma>",sty)), 
                         mk_Some ( HOLogic.mk_prod (mk_undefined rty,term)))
                          
         end;

fun mk_push_name binding = Binding.prefix_name "push_" binding

fun mk_push_def binding sty lthy =
    let val name =  mk_push_name binding
        val rty = \<^typ>\<open>unit\<close>
        val eq = push_eq binding  (Binding.name_of name) rty sty lthy
        val mty = MON_SE_T rty sty 
        val args = (SOME(name, SOME mty, NoSyn), (Binding.empty_atts,eq),[],[])
    in cmd args lthy  end;

val define_test =  Named_Target.theory_map (mk_push_def (Binding.name "test") @{typ "'a"})

end
\<close>

setup\<open>HLDefinitionSample.define_test\<close>

subsection*[ex212::example]\<open>Proof Example (High-level)\<close>  

text\<open>The Isar-toplevel refers to a level of "specification constructs"; i.e. to a level with
more high-level commands that represent internally quite complex theory transformations;
with the exception of the axiomatization constructs, they are alltogether logically conservative.
The proof command interface behind \<open>lemma\<close> or \<open>theorem\<close> uses a structure capturing the 
syntactic @{ML_structure Element}'s of the \<open>fix\<close>, \<open>assume\<close>, \<open>shows\<close> structuring.
\<close>

text\<open>By the way, the Isar-language Element interface can by found under @{ML_structure Element}:
\<^enum> @{ML "Element.Fixes : (binding * 'a option * mixfix) list -> ('a, 'b, 'c) Element.ctxt"}
\<^enum> @{ML "Element.Assumes: (Attrib.binding * ('a * 'a list) list) list -> ('b, 'a, 'c) Element.ctxt"}
\<^enum> @{ML "Element.Notes: string * (Attrib.binding * ('a * Token.src list) list) list 
                       -> ('b, 'c, 'a) Element.ctxt"}
\<^enum> @{ML "Element.Shows: (Attrib.binding * ('a * 'a list) list) list -> ('b, 'a) Element.stmt"}
\<close>

(* UNCHECKED ! ! ! *)

ML\<open>
fun lemma1 lemma_name goals_to_prove  a lthy = 
    let val lemma_name_bdg =(Binding.make (lemma_name, @{here}), []) 
        val attrs' = ["simp"] (* ?????? *)
    in  lthy |>
        Specification.theorem_cmd true 
                                  Thm.theoremK NONE (K I)
                                  Binding.empty_atts [] [] 
                                  (Element.Shows [(lemma_name_bdg,[(goals_to_prove, attrs')])])
                                  true (* disp ??? *)
    end

fun lemma1' lemma_name goals_to_prove a b lthy =
    let fun gen_attribute_token simp lthy = 
        List.map (fn s => Attrib.check_src lthy [Token.make_string (s, Position.none)])
                 (if simp then ["simp", "code_unfold"] else [])
        val lemma_name_bdg =(Binding.make (lemma_name, @{here}), gen_attribute_token true lthy) 
    in  lthy |> #2 o Specification.theorems Thm.theoremK a b true end
\<close>


chapter*[frontend::technical]\<open>Front-End \<close>  
text\<open>In the following chapter, we turn to the right part of the system architecture 
  shown in \<^figure>\<open>architecture\<close>: 
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
  @{theory_text [display] \<open>
  theory Isa_DOF                (* Isabelle Document Ontology Framework *)
    imports  Main  
             RegExpInterface    (* Interface to functional regular automata for monitoring *)
             Assert
             
    keywords "+=" ":=" "accepts" "rejects"
  \<close>}
  where \<^verbatim>\<open>Isa_DOF\<close> is the abstract name of the text-file, \<^verbatim>\<open>Main\<close> etc. refer to imported
  text files (recall that the import relation must be acyclic). \<^emph>\<open>keyword\<close>s are used to separate 
  commands form each other;
  predefined commands allow for the dynamic creation of new commands similarly 
  to the definition of new functions in an interpreter shell (or: toplevel, see above.).
  A command starts with a pre-declared keyword and specific syntax of this command;
  the declaration of a keyword is only allowed in the same \<^verbatim>\<open>.thy\<close>-file where
  the corresponding new command is defined. The semantics of the command is expressed
  in ML and consists of a @{ML_type "Toplevel.transition -> Toplevel.transition"}
  function. Thus, the Isar-toplevel supports the generic document model 
  and allows for user-programmed extensions.\<close>

text\<open>In the traditional literature, Isabelle \<^verbatim>\<open>.thy\<close>-files 
  were said to be processed by two types of parsers:
\<^enum> the "outer-syntax" (i.e. the syntax for commands) is processed 
  by a lexer-library and parser combinators built on top, and
\<^enum> the "inner-syntax" (i.e. the syntax for @{term \<open>\<Lambda>\<close>}-terms) 
  with an evolved, eight-layer parsing and pretty-printing process
  based on an Earley-algorithm.
\<close>

text\<open>This picture is less and less true for a number of reasons:
\<^enum> With the advent of \<open>\<open> ... \<close>\<close>, a mechanism for
  \<^emph>\<open>cascade-syntax\<close> came to the Isabelle platform that introduces a flexible means
  to change parsing contexts \<^emph>\<open>and\<close> parsing technologies. 
\<^enum> Inside the term-parser levels, the concept of \<^emph>\<open>cartouche\<close> can be used 
  to escape the parser and its underlying parsing technology.
\<^enum> Outside, in the traditional toplevel-parsers, the 
  \<open>\<open> ... \<close>\<close> is becoming more and more enforced
  (some years ago, syntax like \<open>term{* ... *}\<close> was replaced by 
   syntax \<open>term\<open> ... \<close>\<close>. This makes technical support of cascade syntax
   more and more easy.
\<^enum> The Lexer infra-structure is already rather generic; nothing prevents to
  add beside the lexer - configurations for ML-Parsers, Toplevel Command Syntax 
  parsers, mathematical notation parsers for $\lambda$-terms new pillars
  of parsing technologies, say, for parsing C or Rust or JavaScript inside 
  Isabelle.
\<close>


section\<open>Basics: string, bstring and xstring\<close>
text\<open>\<^ML_type>\<open>string\<close> is the basic library type from the SML library
  in structure \<^ML_structure>\<open>String\<close>. Many Isabelle operations produce
  or require formats thereof introduced as type synonyms 
  \<^ML_type>\<open>bstring\<close> (defined in structure  \<^ML_structure>\<open>Binding\<close>)
  and \<^ML_type>\<open>xstring\<close> (defined in structure \<^ML_structure>\<open>Name_Space\<close>).
  Unfortunately, the abstraction is not tight and combinations with 
  elementary routines might produce quite crappy results.\<close>

ML\<open>val b = Binding.name_of @{binding \<open>here\<close>}\<close>
text\<open>... produces the system output \<^verbatim>\<open>val it = "here": bstring\<close>,
     but note that it is misleading to believe it is just a string.\<close>

ML\<open>String.explode b\<close> (* is harmless, but  *)
ML\<open>String.explode(Binding.name_of
          (Binding.conglomerate[Binding.qualified_name "X.x", @{binding "here"}]  ))\<close>
text\<open>... which leads to the output \<^verbatim>\<open>val it = [#"x", #"_", #"h", #"e", #"r", #"e"]: char list\<close>\<close>

text\<open> However, there is an own XML parser for this format. See Section Markup. \<close>

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

(* \<^here> *)
text\<open> ... uses the antiquotation @{ML "@{here}"} to infer from the system lexer the actual position
  of itself in the global document, converts it to markup (a string-representation of it) and sends
  it via the usual @{ML "writeln"} to the interface. \<close>

figure*[hyplinkout::figure,relative_width="40",src="''figures/markup-demo''"]
\<open>Output with hyperlinked position.\<close>

text\<open>@{figure \<open>hyplinkout\<close>} shows the produced output where the little house-like symbol in the 
  display is hyperlinked to the position of @{ML "@{here}"} in the ML sample above.\<close>

section\<open>Markup and Low-level Markup Reporting\<close>
text\<open>The structures @{ML_structure Markup} and @{ML_structure Properties} represent the basic 
  annotation data which is part of the protocol sent from Isabelle to the front-end.
  They are qualified as "quasi-abstract", which means they are intended to be an abstraction of 
  the serialized, textual presentation of the protocol. Markups are structurally a pair of a key
  and properties; @{ML_structure Markup} provides a number of such \<^emph>\<open>key\<close>s for annotation classes
  such as "constant", "fixed", "cartouche", some of them quite obscure. Here is a code sample
  from \<^theory_text>\<open>Isabelle_DOF\<close>. A markup must be tagged with an id; this is done by the @{ML serial}-function
  discussed earlier. Markup operations were used for hyperlinking applications to binding
  occurrences, info for hovering, infos for type ... \<close>  

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
Markup.theoryN : string;

fun theory_markup refN  (def:bool) (name:string) (id:serial) (pos:Position.T) =
  if id = 0 then Markup.empty
  else Position.make_entity_markup {def = def} id refN (name, pos);

serial();   (* A global, lock-guarded serial counter used to produce unique identifiers,
               be it on the level of thy-internal states or as reference in markup in
               PIDE *)
\<close>


subsection\<open>A simple Example\<close>
ML\<open>
local 
  
val docclassN = "doc_class";    

(* derived from: theory_markup; def for "defining occurrence" (true) in contrast to
   "referring occurence" (false). *) 
val docclass_markup  = theory_markup docclassN  

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
text\<open>Note that this example is only animated in the integrated source of this document;
     it is essential that is executed inside Isabelle/jEdit. \<close>
ML \<open>

fun markup_tvar def_name ps (name, id) =
  let 
    fun markup_elem name = (name, (name, []): Markup.T);
    val (tvarN, tvar) = markup_elem ((case def_name of SOME name => name | _ => "") ^ "'s nickname is");
    val entity = Markup.entity tvarN name (* ??? *)
    val def = def_name = NONE
  in
    tvar ::
    (if def then I else cons (Markup.keyword_properties Markup.ML_keyword3))
      (map (fn pos => Position.make_entity_markup {def = def} id tvarN (name, pos) ) ps)
  end

(* Position.make_entity_markup {def = def} id refN (name, pos) *)

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

text\<open> The structure \<^ML_structure>\<open>Name_Space\<close> offers an own infra-structure for names and
      manages the markup accordingly.  MORE TO COME\<close>
text\<open> \<^ML_type>\<open>'a Name_Space.table\<close> \<close>


section\<open>The System Lexer and Token Issues\<close>
text\<open>Four syntactic contexts are predefined in Isabelle (others can be added): 
  the ML context, the text context, the Isar-command context and the term-context, referring
  to different needs of the Isabelle Framework as an extensible framework supporting incremental,
  partially programmable extensions and as a Framework geared towards Formal Proofs and therefore
  mathematical notations. The basic data-structure for the lexical treatment of these elements
  are \<^ML_structure>\<open>Token\<close>'s. \<close>

subsection\<open>Tokens\<close>

text\<open>The basic entity that lexers treat are \<^emph>\<open>tokens\<close>. defined in \<^ML_structure>\<open>Token\<close>
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
  \<^ML_structure>\<open>Scan\<close> providing the \<^ML_type>\<open>'a parser\<close> which is a synonym for
  \<^ML_type>\<open>Token.T list -> 'a * Token.T list\<close>. 
  
  "parsers" are actually  interpreters; an \<^ML_type>\<open>'a parser\<close> is a function that parses
  an input stream and computes (=evaluates) it into \<open>'a\<close>. 

  \<^item> \<^theory_text>\<open>type 'a parser = Token.T list -> 'a * Token.T list\<close>
  \<^item> \<^theory_text>\<open> type 'a context_parser = Context.generic * Token.T list -> 
      'a * (Context.generic * Token.T list)\<close>

  Since the semantics of an Isabelle command is a \<^ML_type>\<open>Toplevel.transition -> Toplevel.transition \<close>
  or theory  \<^ML_type>\<open>theory -> theory\<close>  function, i.e. a global system transition,
  "parsers" of that type can be constructed and be bound as call-back functions
  to a table in the Toplevel-structure of Isar.
  
  The library also provides a bunch of infix parsing combinators, notably:

\<^item> \<^ML>\<open>op !! : ('a * message option -> message) -> ('a -> 'b) -> 'a -> 'b\<close> 
 (*apply function*)
\<^item> \<^ML>\<open>op >> : ('a -> 'b * 'c) * ('b -> 'd) -> 'a -> 'd * 'c\<close> 
 (*alternative*)
\<^item> \<^ML>\<open> op || : ('a -> 'b) * ('a -> 'b) -> 'a -> 'b\<close>
 (*sequential pairing*)
\<^item> \<^ML>\<open>op -- : ('a -> 'b * 'c) * ('c -> 'd * 'e) -> 'a -> ('b * 'd) * 'e\<close> 
 (*dependent pairing*)
\<^item> \<^ML>\<open> op :-- : ('a -> 'b * 'c) * ('b -> 'c -> 'd * 'e) -> 'a -> ('b * 'd) * 'e\<close>
 (*projections*)
\<^item> \<^ML>\<open>op :|-- : ('a -> 'b * 'c) * ('b -> 'c -> 'd * 'e) -> 'a -> 'd * 'e\<close> 
\<^item> \<^ML>\<open>op |-- : ('a -> 'b * 'c) * ('c -> 'd * 'e) -> 'a -> 'd * 'e\<close> 
  concatenate and forget first parse result
\<^item> \<^ML>\<open>op --| : ('a -> 'b * 'c) * ('c -> 'd * 'e) -> 'a -> 'b * 'e\<close> 
  concatenate and forget second parse result
\<^item> \<^ML>\<open>op ^^ : ('a -> string * 'b) * ('b -> string * 'c) -> 'a -> string * 'c\<close> 
\<^item> \<^ML>\<open>op ::: : ('a -> 'b * 'c) * ('c -> 'b list * 'd) -> 'a -> 'b list * 'd\<close> 
\<^item> \<^ML>\<open>op @@@ : ('a -> 'b list * 'c) * ('c -> 'b list * 'd) -> 'a -> 'b list * 'd\<close> 
  parse one element literal
\<^item> \<^ML>\<open>op $$ : string -> string list -> string * string list\<close> 
\<^item> \<^ML>\<open>op ~$$ : string -> string list -> string * string list\<close> 
\<close>


subsection\<open>Examples and Useful Glue\<close>
ML\<open>

(* conversion between these two : *)

fun parser2contextparser pars (ctxt, toks) = let val (a, toks') = pars toks
                                             in  (a,(ctxt, toks')) end;
val _ = parser2contextparser : 'a parser -> 'a context_parser;

(* bah, it's the same as Scan.lift *)
val _ = Scan.lift Args.cartouche_input : Input.source context_parser;\<close>

subsection\<open>Advanced Parser Library\<close>

text\<open>There are two parts. A general multi-purpose parsing combinator library is 
  found under @{ML_structure "Parse"}, providing basic functionality for parsing strings
  or integers. There is also an important combinator that reads the current position information
  out of the input stream:

\<^item> \<^ML>\<open>Parse.nat: int parser\<close>  
\<^item> \<^ML>\<open>Parse.int: int parser\<close>
\<^item> \<^ML>\<open>Parse.enum_positions: string -> 'a parser -> ('a list * Position.T list) parser\<close>
\<^item> \<^ML>\<open>Parse.enum : string -> 'a parser -> 'a list parser\<close>
\<^item> \<^ML>\<open>Parse.input: 'a parser -> Input.source parser\<close>

\<^item> \<^ML>\<open>Parse.enum': string -> 'a context_parser -> 'a list context_parser\<close>
\<^item> \<^ML>\<open>Parse.!!! : (Token.T list -> 'a) -> Token.T list -> 'a\<close>
\<^item> \<^ML>\<open>Parse.position: 'a parser -> ('a * Position.T) parser\<close>

\<^item> \<^ML>\<open>Parse.position Args.cartouche_input\<close>
\<close>

text\<open>The second part is much more high-level, and can be found under \<^ML_structure>\<open>Args\<close>.
  In parts, these combinators are again based on more low-level combinators, in parts they serve as 
  an interface to the underlying Earley-parser for mathematical notation used in types and terms.
  This is perhaps meant with the fairly cryptic comment:
  "Quasi-inner syntax based on outer tokens: concrete argument syntax of
  attributes, methods etc." at the beginning of this structure.\<close>

text\<open> Some more combinators
\<^item>\<^ML>\<open>Args.symbolic : Token.T parser\<close>
\<^item>\<^ML>\<open>Args.$$$ : string -> string parser\<close>
\<^item>\<^ML>\<open>Args.maybe : 'a parser -> 'a option parser\<close>
\<^item>\<^ML>\<open>Args.name_token: Token.T parser\<close>

Common Isar Syntax
\<^item>\<^ML>\<open>Args.colon: string parser\<close>
\<^item>\<^ML>\<open>Args.query: string parser\<close>
\<^item>\<^ML>\<open>Args.bang: string parser\<close>
\<^item>\<^ML>\<open>Args.query_colon: string parser\<close>
\<^item>\<^ML>\<open>Args.bang_colon: string parser\<close>
\<^item>\<^ML>\<open>Args.parens: 'a parser -> 'a parser\<close>
\<^item>\<^ML>\<open>Args.bracks: 'a parser -> 'a parser\<close>
\<^item>\<^ML>\<open>Args.mode: string -> bool parser\<close>
\<^item>\<^ML>\<open>Args.name: string parser\<close>
\<^item>\<^ML>\<open>Args.name_position: (string * Position.T) parser\<close>
\<^item>\<^ML>\<open>Args.cartouche_inner_syntax: string parser\<close>
\<^item>\<^ML>\<open>Args.cartouche_input: Input.source parser\<close>
\<^item>\<^ML>\<open>Args.text_token: Token.T parser \<close>


Common Isar Syntax
\<^item>\<^ML>\<open>Args.text_input: Input.source parser\<close>
\<^item>\<^ML>\<open>Args.text      : string parser\<close>
\<^item>\<^ML>\<open>Args.binding   : Binding.binding parser\<close>

Common Stuff related to Inner Syntax Parsing
\<^item>\<^ML>\<open>Args.alt_name: string parser\<close>
\<^item>\<^ML>\<open>Args.liberal_name   : string parser\<close>
\<^item>\<^ML>\<open>Args.var: indexname parser\<close>
\<^item>\<^ML>\<open>Args.internal_source: Token.src parser\<close>
\<^item>\<^ML>\<open>Args.internal_name: Token.name_value parser\<close>
\<^item>\<^ML>\<open>Args.internal_typ : typ parser\<close>
\<^item>\<^ML>\<open>Args.internal_term: term parser\<close>
\<^item>\<^ML>\<open>Args.internal_fact: thm list parser\<close>
\<^item>\<^ML>\<open>Args.internal_attribute: (morphism -> attribute) parser\<close>
\<^item>\<^ML>\<open>Args.internal_declaration: declaration parser\<close>
\<^item>\<^ML>\<open>Args.alt_name    : string parser\<close>
\<^item>\<^ML>\<open>Args.liberal_name: string parser\<close>



Common Isar Syntax
\<^item>\<^ML>\<open>Args.named_source: (Token.T -> Token.src) -> Token.src parser\<close>
\<^item>\<^ML>\<open>Args.named_typ   : (string -> typ) -> typ parser\<close>
\<^item>\<^ML>\<open>Args.named_term : (string -> term) -> term parser\<close>
\<^item>\<^ML>\<open>Args.text_declaration: (Input.source -> declaration) -> declaration parser\<close>
\<^item>\<^ML>\<open>Args.cartouche_declaration: (Input.source -> declaration) -> declaration parser\<close>
\<^item>\<^ML>\<open>Args.typ_abbrev  : typ context_parser\<close>
\<^item>\<^ML>\<open>Args.typ: typ context_parser\<close>
\<^item>\<^ML>\<open>Args.term: term context_parser\<close>
\<^item>\<^ML>\<open>Args.term_pattern: term context_parser\<close>
\<^item>\<^ML>\<open>Args.term_abbrev : term context_parser \<close>
\<^item>\<^ML>\<open>Args.named_source: (Token.T -> Token.src) -> Token.src parser\<close>
\<^item>\<^ML>\<open>Args.named_typ : (string -> typ) -> typ parser\<close>
\<^item>\<^ML>\<open>Args.named_term: (string -> term) -> term parser\<close>
\<^item>\<^ML>\<open>Args.text_declaration: (Input.source -> declaration) -> declaration parser\<close>
\<^item>\<^ML>\<open>Args.cartouche_declaration: (Input.source -> declaration) -> declaration parser\<close>

Syntax for some major Pure commands in Isar
\<^item>\<^ML>\<open>Args.prop: term context_parser\<close>
\<^item>\<^ML>\<open>Args.type_name: {proper: bool, strict: bool} -> string context_parser\<close>
\<^item>\<^ML>\<open>Args.const: {proper: bool, strict: bool} -> string context_parser\<close>
\<^item>\<^ML>\<open>Args.goal_spec: ((int -> tactic) -> tactic) context_parser\<close>
\<^item>\<^ML>\<open>Args.context: Proof.context context_parser\<close>
\<^item>\<^ML>\<open>Args.theory: theory context_parser\<close>

\<close>



subsection\<open> Bindings \<close>  

text\<open> The structure \<^ML_structure>\<open>Binding\<close> serves as 
  \<open>structured name bindings\<close>, as says the description, i.e. a mechanism to basically 
  associate an input string-fragment to its position. This concept is vital in all parsing processes
  and the interaction with PIDE.

  Key are two things:
\<^enum> the type-synonym \<^ML_type>\<open>bstring\<close> which is synonym to \<^ML_type>\<open>string\<close>
  and intended for "primitive names to be bound"
\<^enum> the projection \<^ML>\<open>Binding.pos_of :  Binding.binding -> Position.T\<close>
\<^enum> the constructor establishing a binding \<^ML>\<open>Binding.make: bstring * Position.T -> Binding.binding\<close>

\<close>


subsubsection\<open> Example \<close>  

text\<open>Since this is so common in interface programming, there are a number of antiquotations\<close>
ML\<open>
val H = @{binding here}; (* There are "bindings" consisting of a text-span and a position, 
                            where "positions" are absolute references to a file *)                                  

Binding.pos_of H;  (* clicking on "H" activates the hyperlink to the defining occ of "H" above *)
(*  {offset=23, end_offset=27, id=-17214}: Position.T *)

(* a modern way to construct a binding is by the following code antiquotation : *)
\<^binding>\<open>theory\<close>

\<close>  

subsection \<open>Input streams. \<close>  
text\<open>Reads as : Generic input with position and range information, to be processed in a 
left-to right manner. Preferable to strings if used for larger data. 

Constructor: \<^ML>\<open>Input.source_explode : Input.source -> Symbol_Pos.T list\<close>

\<close>

subsubsection \<open>Example :Input streams. \<close>  

ML\<open> Input.source_explode (Input.string " f @{thm refl}");
  
   (* If stemming from the input window, this can be something like: 
      
        [(" ", {offset=14, id=-2769}), ("f", {offset=15, id=-2769}), (" ", {offset=16, id=-2769}),
        ("@", {offset=17, id=-2769}), ("{", {offset=18, id=-2769}), ("t", {offset=19, id=-2769}),
        ("h", {offset=20, id=-2769}), ("m", {offset=21, id=-2769}), (" ", {offset=22, id=-2769}),
        ("r", {offset=23, id=-2769}), ("e", {offset=24, id=-2769}), ("f", {offset=25, id=-2769}),
        ("l", {offset=26, id=-2769}), ("}", {offset=27, id=-2769})]
   *)

\<close>
  

section\<open>Term Parsing\<close>  

text\<open>The heart of the parsers for mathematical notation, based on an Earley-parser that can cope
  with incremental changes of the grammar as required for sophisticated mathematical output, is hidden
  behind the API described in this section.\<close>
  
text\<open> Note that the naming underlies the following convention. 
   There are:
   \<^enum> "parser"s 
   \<^enum>  type-"checker"s, which usually also englobe the markup generation for PIDE
   \<^enum> "reader"s which do both together with pretty-printing
   
   This is encapsulated in the data structure @{ML_structure Syntax} --- 
   the table with const symbols,  print and ast translations, ... The latter is accessible, e.g. 
   from a Proof context via @{ML Proof_Context.syn_of}.
\<close>

text\<open> Inner Syntax Parsing combinators for elementary Isabelle Lexems\<close>  
text\<open>
\<^item> \<^ML>\<open> Syntax.parse_sort : Proof.context  -> string -> sort\<close>
\<^item> \<^ML>\<open> Syntax.parse_typ  : Proof.context  -> string -> typ\<close>
\<^item> \<^ML>\<open> Syntax.parse_term : Proof.context  -> string -> term\<close>
\<^item> \<^ML>\<open> Syntax.parse_prop : Proof.context  -> string -> term\<close>
\<^item> \<^ML>\<open> Syntax.check_term : Proof.context  -> term -> term\<close>
\<^item> \<^ML>\<open> Syntax.check_props: Proof.context  -> term list -> term list\<close>
\<^item> \<^ML>\<open> Syntax.uncheck_sort: Proof.context -> sort -> sort\<close>
\<^item> \<^ML>\<open> Syntax.uncheck_typs: Proof.context -> typ list -> typ list\<close>
\<^item> \<^ML>\<open> Syntax.uncheck_terms: Proof.context -> term list -> term list\<close>
\<close>

text\<open>In contrast to mere parsing, the following operators provide also type-checking
     and internal reporting to PIDE --- see below. I did not find a mechanism to address
     the internal serial-numbers used for the PIDE protocol, however, rumours have it
     that such a thing exists. The variants \<^verbatim>\<open>_global\<close> work on theories instead on 
     \<^ML_type>\<open>Proof.context\<close>s.\<close>

text\<open>
\<^item> \<^ML>\<open>Syntax.read_sort: Proof.context -> string -> sort\<close>
\<^item> \<^ML>\<open>Syntax.read_typ : Proof.context -> string -> typ\<close>
\<^item> \<^ML>\<open>Syntax.read_term: Proof.context -> string -> term\<close>
\<^item> \<^ML>\<open>Syntax.read_typs: Proof.context -> string list -> typ list\<close>
\<^item> \<^ML>\<open>Syntax.read_sort_global: theory -> string -> sort\<close>
\<^item> \<^ML>\<open>Syntax.read_typ_global: theory -> string -> typ\<close>
\<^item> \<^ML>\<open>Syntax.read_term_global: theory -> string -> term\<close>
\<^item> \<^ML>\<open>Syntax.read_prop_global: theory -> string -> term\<close>
                                                                    \<close>
text \<open>The following operations are concerned with the conversion of pretty-prints
and, from there, the generation of (non-layouted) strings :

\<^item> \<^ML>\<open>Syntax.pretty_term:Proof.context -> term -> Pretty.T\<close>
\<^item> \<^ML>\<open>Syntax.pretty_typ:Proof.context -> typ -> Pretty.T \<close>
\<^item> \<^ML>\<open>Syntax.pretty_sort:Proof.context -> sort -> Pretty.T \<close>
\<^item> \<^ML>\<open>Syntax.pretty_classrel: Proof.context -> class list -> Pretty.T\<close>
\<^item> \<^ML>\<open>Syntax.pretty_arity: Proof.context -> arity -> Pretty.T\<close>
\<^item> \<^ML>\<open>Syntax.string_of_term: Proof.context -> term -> string \<close>
\<^item> \<^ML>\<open>Syntax.string_of_typ: Proof.context -> typ -> string \<close>
\<^item> \<^ML>\<open>Syntax.lookup_const : Syntax.syntax -> string -> string option\<close>
\<close>






text\<open>
  Note that \<^ML>\<open>Syntax.install_operations\<close> is a late-binding interface, i.e. a collection of 
  "hooks" used to resolve an apparent architectural cycle.
  The real work is done in \<^file>\<open>~~/src/Pure/Syntax/syntax_phases.ML\<close> 
  
  Even the parsers and type checkers stemming from the theory-structure are registered via
  hooks (this can be confusing at times). Main phases of inner syntax processing, with standard 
  implementations of parse/unparse operations were treated this way.
  At the very very end in, it sets up the entire syntax engine (the hooks) via:

  \<^theory_text>\<open>Theory.setup
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
      uncheck_terms = uncheck_terms})
  \<close>
\<close>



(*
Document_Antiquotation
*)

subsection*[ex33::example] \<open>Example\<close>

ML\<open>
     
     (* here follows the definition of the attribute parser : *)
     val Z = let val attribute = Parse.position Parse.name -- 
                                 Scan.optional (Parse.$$$ "=" |-- Parse.!!! Parse.name) "";
             in   (Scan.optional(Parse.$$$ "," |-- (Parse.enum "," attribute))) end ;
     
     
     (* Here is the code to register the above parsers as text antiquotations into the Isabelle
        Framework: *)
      Document_Output.antiquotation_pretty_source \<^binding>\<open>theory\<close> 
                                            (Scan.lift (Parse.position Parse.embedded));
     
      Document_Output.antiquotation_raw           \<^binding>\<open>file\<close> 
                                            (Scan.lift (Parse.position Parse.path))  ;
     
\<close>

text\<open>where we have the registration of the action
     \<^ML>\<open>Scan.lift (Parse.position Args.cartouche_input)\<close>
     to be bound to the  \<open>name\<close>  as a whole is a system 
     transaction that, of course, has the type \<^ML_type>\<open>theory -> theory\<close> :

     @{ML [display] \<open>
          (fn name => (Document_Output.antiquotation_pretty_source 
                 name
                (Scan.lift (Parse.position Args.cartouche_input))))
          : binding -> 
               (Proof.context -> Input.source * Position.T -> Pretty.T) -> 
               theory -> theory
     \<close>}
    \<close>

 
section \<open> Output: Very Low Level \<close>
text\<open> For re-directing the output channels, the structure \<^ML_structure>\<open>Output\<close> may be relevant:
      \<^ML>\<open>Output.output:string -> string\<close> is the  structure for the "hooks" with the target devices.
    \<close>

ML\<open> Output.output "bla_1:" \<close>

text\<open>It provides a number of hooks that can be used for redirection hacks ...\<close>

section \<open> Output: LaTeX \<close>
text\<open>The heart of the LaTeX generator is to be found in the structure \<^ML_structure>\<open>Document_Output\<close>.
This is an own parsing and writing process, with the risc that a parsed file in the IDE parsing
process can not be parsed for the LaTeX Generator. The reason is twofold:

\<^enum> The LaTeX Generator makes a rough attempt to mimic the LayOut in the thy-file; thus, its
  spacing is relevant.
\<^enum> there is a special bracket \<open>(*<*)\<close> ... \<open>(*>*)\<close> that allows to specify input that is checked by
  Isabelle, but excluded from the LaTeX generator (this is handled in an own sub-parser
  called  \<^ML>\<open>Document_Source.improper\<close> where also other forms of comment parsers are provided.

Since Isabelle2018, an own AST is provided for the LaTeX syntax, analogously to 
\<^ML_structure>\<open>Pretty\<close>. Key functions of this structure  \<^ML_structure>\<open>Latex\<close> are:

\<^item>\<^ML>\<open>Latex.string: string -> Latex.text\<close>
\<^item>\<^ML>\<open>Latex.text: string * Position.T -> Latex.text\<close>

\<^item>\<^ML>\<open>Latex.output_name: string -> string\<close>
\<^item>\<^ML>\<open>Latex.output_ascii: string -> string\<close>
\<^item>\<^ML>\<open>Latex.output_symbols: Symbol.symbol list -> string\<close>
                                                                          

\<^item>\<^ML>\<open>Latex.environment: string -> Latex.text -> Latex.text\<close>

\<^item>\<^ML>\<open>Latex.block: Latex.text -> XML.tree\<close>
\<close>



ML\<open> Latex.output_ascii;
    Latex.environment "isa" (Latex.string "bg");
    Latex.output_ascii "a_b:c'é";
    (* Note: *)
    space_implode "sd &e sf dfg" ["qs","er","alpa"]; 
  \<close>

text\<open>Here is an abstract of the main interface to @{ML_structure Document_Output}:\<close>

text\<open>
\<^item>\<^ML>\<open>Document_Output.output_document: Proof.context -> {markdown: bool} -> Input.source -> Latex.text \<close>
\<^item>\<^ML>\<open>Document_Output.output_token: Proof.context -> Token.T -> Latex.text \<close>
\<^item>\<^ML>\<open>Document_Output.output_source: Proof.context -> string -> Latex.text \<close>
\<^item>\<^ML>\<open>Document_Output.present_thy: Options.T -> theory -> Document_Output.segment list -> Latex.text \<close>

\<^item>\<^ML>\<open>Document_Output.isabelle: Proof.context -> Latex.text  -> Latex.text\<close>
\<^item>\<^ML>\<open>Document_Output.isabelle_typewriter: Proof.context -> Latex.text  -> Latex.text\<close>
\<^item>\<^ML>\<open>Document_Output.typewriter: Proof.context -> string -> Latex.text\<close>
\<^item>\<^ML>\<open>Document_Output.verbatim: Proof.context -> string -> Latex.text\<close>
\<^item>\<^ML>\<open>Document_Output.source: Proof.context -> {embedded: bool} -> Token.src -> Latex.text\<close>
\<^item>\<^ML>\<open>Document_Output.pretty: Proof.context -> Pretty.T -> Latex.text\<close>
\<^item>\<^ML>\<open>Document_Output.pretty_source: Proof.context -> {embedded: bool} -> Token.src -> Pretty.T -> Latex.text\<close>
\<^item>\<^ML>\<open>Document_Output.pretty_items: Proof.context -> Pretty.T list -> Latex.text\<close>
\<^item>\<^ML>\<open>Document_Output.pretty_items_source: Proof.context -> {embedded: bool} -> Token.src -> Pretty.T list -> Latex.text\<close>

Finally a number of antiquotation registries :

\<^item>\<^ML>\<open>Document_Output.antiquotation_pretty:
                 binding -> 'a context_parser -> (Proof.context -> 'a -> Pretty.T) -> theory -> theory\<close>
\<^item>\<^ML>\<open>Document_Output.antiquotation_pretty_source:
                 binding -> 'a context_parser -> (Proof.context -> 'a -> Pretty.T) -> theory -> theory\<close>
\<^item>\<^ML>\<open>Document_Output.antiquotation_raw:
                 binding -> 'a context_parser -> (Proof.context -> 'a -> Latex.text) -> theory -> theory\<close>
\<^item>\<^ML>\<open>Document_Output.antiquotation_verbatim:
               binding -> 'a context_parser -> (Proof.context -> 'a -> string) -> theory -> theory\<close>
\<close>


text\<open> Thus, \<^ML_structure>\<open>Syntax_Phases\<close> does the actual work of markup generation, including
        markup generation and  generation of reports. Look at the following snippet: 
\<open>
fun check_typs ctxt raw_tys =
  let
    val (sorting_report, tys) = Proof_Context.prepare_sortsT ctxt raw_tys;
    val _ = if Context_Position.is_visible ctxt then Output.report sorting_report else ();
  in
    tys
    |> apply_typ_check ctxt
    |> Term_Sharing.typs (Proof_Context.theory_of ctxt)
  end;
\<close>

which is the real implementation behind \<^ML>\<open>Syntax.check_typ\<close>

\<open>
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
\<close>

which is the real implementation behind \<^ML>\<open>Syntax.check_term\<close>. As one can see, check-routines 
internally generate the markup.
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
  already been done in the surrounding Isabelle/DOF environment... 
  \<^verbatim>\<open>
  parse_translation \<open>
    [( @{syntax_const "_cartouche_string"}
     , parse_translation_cartouche \<^binding>\<open>cartouche_type\<close> Cartouche_Grammar.default (K I) ())]
  \<close>
  \<close>
\<close>

text\<open> Test for this cartouche... \<close>
term  "\<open>A \<Longrightarrow> B\<close> = ''''"



chapter*[c::conclusion]\<open>Conclusion\<close>
text\<open> This interactive Isabelle Programming Cook-Book represents my current way 
  to view and explain Isabelle programming API's to students and collaborators. 
  It differs from the reference  manual in some places on purpose, since I believe 
  that a lot of internal Isabelle API's need a more conceptual view on what is happening 
  (even if this conceptual view is at times over-abstracting a little).
  It is written in Isabelle/DOF and conceived as "living document" (a term that I owe to 
  Simon Foster), i.e. as hypertext-heavy text making direct references to the Isabelle API's 
  which were checked whenever this document is re-visited in Isabelle/jEdit.
      
  All hints and contributions of collegues and collaborators are greatly welcomed; all errors
  and the roughness of this presentation is entirely my fault.
\<close>
(*<*)

paragraph\<open>Many thanks to Frederic Tuong, who contributed some example such as the string 
cartouche for Unicode Character Denotations as well as many local hints for improvements.\<close>

section*[bib::bibliography]\<open>Bibliography\<close>

close_monitor*[this] 
check_doc_global

end
(*>*)
