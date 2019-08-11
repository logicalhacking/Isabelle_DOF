(*<*)
theory "05_Implementation"
  imports "04_RefMan"
begin
(*>*)


chapter*[isadof_developers::text_section]\<open>Extending \isadof\<close>
text\<open>
  In this chapter, we describe the basic implementation aspects of \isadof, which is based on 
  the following design-decisions:
  \<^item> the entire \isadof is a ``pure add-on,'' \ie, we deliberately resign on the possibility to 
    modify Isabelle itself.
  \<^item> we made a small exception to this rule: the \isadof package modifies in its installation 
    about 10 lines in the \LaTeX-generator (\path{src/patches/thy_output.ML}).
  \<^item> we decided to make the markup-generation by itself to adapt it as well as possible to the 
    needs of tracking the linking in documents.
  \<^item> \isadof is deeply integrated into the Isabelle's IDE (PIDE) to give immediate feedback during 
    editing and other forms of document evolution.
\<close>
text\<open>
  Semantic macros, as required by our document model, are called \<^emph>\<open>document antiquotations\<close>
  in the Isabelle literature~@{cite "wenzel:isabelle-isar:2019"}. While Isabelle's code-antiquotations 
  are an old concept going back to Lisp and having found via SML and OCaml their ways into modern 
  proof systems, special annotation syntax inside documentation comments have their roots in 
  documentation generators such as Javadoc. Their use, however, as a mechanism to embed 
  machine-checked \<^emph>\<open>formal content\<close> is usually very limited and also lacks 
  IDE support.
\<close>

section\<open>\isadof: A User-Defined Plugin in Isabelle/Isar\<close>
text\<open>
  A plugin in Isabelle starts with defining the local data and registering it in the framework. As 
  mentioned before, contexts are structures with independent cells/compartments having three
  primitives \inlinesml+init+, \inlinesml+extend+ and \inlinesml+merge+. Technically this is done by 
  instantiating a functor \inlinesml+Generic_Data+, and the following fairly typical code-fragment 
  is drawn from \isadof:

\begin{sml}
structure Data = Generic_Data
(  type T = docobj_tab * docclass_tab * ...
   val empty  = (initial_docobj_tab, initial_docclass_tab, ...) 
   val extend = I
   fun merge((d1,c1,...),(d2,c2,...)) = (merge_docobj_tab  (d1,d2,...), 
                                         merge_docclass_tab(c1,c2,...))
);
\end{sml}
  where the table \inlinesml+docobj_tab+ manages document classes and \inlinesml+docclass_tab+ the 
  environment for class definitions (inducing the inheritance relation). Other tables capture, \eg, 
  the class invariants, inner-syntax antiquotations. Operations follow the MVC-pattern, where 
  Isabelle/Isar provides the controller part. A typical model operation has the type:

\begin{sml}
val opn :: <args_type> -> Context.generic -> Context.generic
\end{sml}
  representing a transformation on system contexts. For example, the operation of declaring a local 
  reference in the context is presented as follows:

\begin{sml}
fun declare_object_local oid ctxt  =
let fun decl {tab,maxano} = {tab=Symtab.update_new(oid,NONE) tab,
                             maxano=maxano}
in  (Data.map(apfst decl)(ctxt)
  handle Symtab.DUP _ =>
              error("multiple declaration of document reference"))
end
\end{sml}                                            
  where \inlineisar+Data.map+ is the update function resulting from the instantiation of the 
  functor \inlinesml|Generic_Data|. This code fragment uses operations from a library structure 
  \inlinesml+Symtab+ that were used to update the appropriate table for document objects in
  the plugin-local state. Possible exceptions to the update operation were mapped to a system-global 
  error reporting function.

  Finally, the view-aspects were handled by an API for parsing-combinators. The library structure 
  \inlinesml+Scan+ provides the operators:

\begin{sml}
op ||     : ('a -> 'b) * ('a -> 'b) -> 'a -> 'b
op --     : ('a -> 'b * 'c) * ('c -> 'd * 'e) -> 'a -> ('b * 'd) * 'e
op >>     : ('a -> 'b * 'c) * ('b -> 'd) -> 'a -> 'd * 'c
op option : ('a -> 'b * 'a) -> 'a -> 'b option * 'a
op repeat : ('a -> 'b * 'a) -> 'a -> 'b list * 'a 
\end{sml}                                            
  for alternative, sequence, and piping, as well as combinators for option and repeat. Parsing 
  combinators have the advantage that they can be smoothlessly integrated into standard programs, 
  and they enable the dynamic extension of the grammar. There is a more high-level structure 
  \inlinesml{Parse} providing specific combinators for the command-language Isar:

\begin{sml}[mathescape=false]
val attribute = Parse.position Parse.name 
              -- Scan.optional(Parse.$$$ "=" |-- Parse.!!! Parse.name)"";
val reference = Parse.position Parse.name 
              -- Scan.option (Parse.$$$ "::" |-- Parse.!!!
                              (Parse.position Parse.name));
val attributes =(Parse.$$$ "[" |-- (reference 
               -- (Scan.optional(Parse.$$$ ","
                   |--(Parse.enum ","attribute)))[]))--| Parse.$$$ "]"              
\end{sml}                                            

  The ``model'' \inlineisar+declare_reference_opn+ and ``new'' \inlineisar+attributes+ parts were 
  combined via the piping operator and registered in the Isar toplevel:

\begin{sml}
  fun declare_reference_opn (((oid,_),_),_) =
                 (Toplevel.theory (DOF_core.declare_object_global oid))
  val _ = Outer_Syntax.command <@>{command_keyword "declare_reference"}
          "declare document reference"
          (attributes >> declare_reference_opn);
\end{sml}

  Altogether, this gives the extension of Isabelle/HOL with Isar syntax and semantics for the 
  new \emph{command}:

\begin{isar}
declare_reference [lal::requirement, alpha="main", beta=42]
\end{isar}

  The construction also generates implicitly some markup information; for example, when hovering
  over the \inlineisar|declare_reference| command in the IDE, a popup window with the text: 
  ``declare document reference'' will appear.
\<close>

section\<open>Programming Antiquotations\<close>
text\<open>
  The definition and registration of text antiquotations and ML-antiquotations is similar in 
  principle: based on a number of combinators, new user-defined antiquotation syntax and semantics
  can be added to the system that works on the internal plugin-data freely. For example, in

\begin{sml}
val _ = Theory.setup(
          Thy_Output.antiquotation <@>{binding docitem} 
                                   docitem_antiq_parser 
                                   (docitem_antiq_gen default_cid) #>
          ML_Antiquotation.inline  <@>{binding docitem_value} 
                                   ML_antiq_docitem_value)
\end{sml}
  the text antiquotation \inlineisar+docitem+ is declared and bounded to a parser for the argument 
  syntax and the overall semantics. This code defines a generic antiquotation to be used in text 
  elements such as

\begin{isar}
text\<Open>as defined in <@>{docitem \<Open>d1\<Close>} ...\<Close>
\end{isar}

  The subsequent registration \inlineisar+docitem_value+ binds code to a ML-antiquotation usable 
  in an ML context for user-defined extensions; it permits the access to the current ``value'' 
  of document element, \ie; a term with the entire update history.

  It is possible to generate antiquotations \emph{dynamically}, as a consequence of a class 
  definition in ODL. The processing of the ODL class \inlineisar+d$$efinition+ also \emph{generates}
  a text antiquotation \inlineisar+<@>{definition \<Open>d1\<Close>}+, which works similar to 
  \inlineisar+<@>{docitem \<Open>d1\<Close>}+ except for an additional type-check that assures that 
  \inlineisar+d1+ is a reference to a definition. These type-checks support the subclass hierarchy.
\<close>

section\<open>Implementing Second-level Type-Checking\<close>
text\<open>
  On expressions for attribute values, for which we chose to use HOL syntax to avoid that users 
  need to learn another syntax, we implemented an own pass over type-checked terms. Stored in the 
  late-binding table \inlineisar+ISA_transformer_tab+, we register for each inner-syntax-annotation 
  (ISA's), a function of type

\begin{sml}
   theory -> term * typ * Position.T -> term option
\end{sml}

  Executed in a second pass of term parsing, ISA's may just return \inlineisar+None+. This is 
  adequate for ISA's just performing some checking in the logical context \inlineisar+theory+; 
  ISA's of this kind report errors  by exceptions. In contrast, \<^emph>\<open>transforming\<close> ISA's will 
  yield a term; this is adequate, for example, by replacing a string-reference to some term denoted 
  by it. This late-binding table is also used to generate standard inner-syntax-antiquotations from 
  a \inlineisar+doc_class+.
\<close>

section\<open>Programming Class Invariants\<close>
text\<open>
  For the moment, there is no high-level syntax for the definition of class invariants. A 
  formulation, in SML, of the first class-invariant in @{docref "sec:class_inv"} is straight-forward:

\begin{sml}
fun check_result_inv oid {is_monitor:bool} ctxt =
  let val kind = compute_attr_access ctxt "kind" oid <@>{here} <@>{here} 
      val prop = compute_attr_access ctxt "property" oid <@>{here} <@>{here} 
      val tS = HOLogic.dest_list prop
  in  case kind_term of
       <@>{term "proof"} => if not(null tS) then true
                          else error("class result invariant violation") 
      | _ => false
  end
 val _ = Theory.setup (DOF_core.update_class_invariant 
                                "tiny_cert.result" check_result_inv)
\end{sml}

  The \inlinesml{setup}-command (last line) registers the \inlineisar+check_result_inv+ function 
  into the \isadof kernel, which activates any creation or modification of an instance of
  \inlineisar+result+.  We cannot replace \inlineisar+compute_attr_access+ by the corresponding 
  antiquotation \inlineisar+<@>{docitem_value kind::oid}+, since \inlineisar+oid+ is
  bound to a variable here and can therefore not be statically expanded.
\<close>

section\<open>Implementing Monitors\<close>
text\<open>
  Since monitor-clauses have a regular expression syntax, it is natural to implement them as 
  deterministic automata. These are stored in the  \inlineisar+docobj_tab+ for monitor-objects 
  in the \isadof component. We implemented the functions:

\begin{sml}
   val  enabled : automaton -> env -> cid list
   val  next    : automaton -> env -> cid -> automaton
\end{sml}
  where \inlineisar+env+ is basically a map between internal automaton states and class-id's 
  (\inlineisar+cid+'s). An automaton is said to be \<^emph>\<open>enabled\<close> for a class-id, 
  iff it either occurs in its accept-set or its reject-set (see @{docref "sec:monitors"}). During 
  top-down document validation, whenever a text-element is encountered, it is checked if a monitor 
  is \emph{enabled} for this class; in this case, the \inlineisar+next+-operation is executed. The 
  transformed automaton recognizing the rest-language is stored in \inlineisar+docobj_tab+ if
  possible; otherwise, if \inlineisar+next+ fails, an error is reported. The automata implementation 
  is, in large parts, generated from a formalization of functional automata~\cite{Functional-Automata-AFP}.
\<close>

section\<open>The \LaTeX-Core of \isadof\<close>
text\<open>
  The \LaTeX-implementation of \isadof heavily relies on the 
  ``keycommand''~@{cite "chervet:keycommand:2010"} package. In fact, the core \isadof \LaTeX-commands
  are just wrappers for the corresponding commands from the keycommand package:

\begin{ltx}
\newcommand\newisadof[1]{%
  \expandafter\newkeycommand\csname isaDof.#1\endcsname}%
\newcommand\renewisadof[1]{%
  \expandafter\renewkeycommand\csname isaDof.#1\endcsname}%
\newcommand\provideisadof[1]{%
  \expandafter\providekeycommand\csname isaDof.#1\endcsname}%
\end{ltx}

  The \LaTeX-generator of \isadof maps each \inlineisar{doc_item} to an \LaTeX-environment (recall
  @{docref "text-elements"}). As generic \inlineisar{doc_item} are derived from the text element, 
  the enviornment \inlineltx|{isamarkuptext*}| builds the core of \isadof's \LaTeX{} implementation. 
  For example, the @{docref "ass123"} from page \pageref{ass123} is mapped to

\begin{ltx}
\begin{isamarkuptext*}%
[label = {ass122},type = {CENELEC_50128.SRAC}, 
 args={label = {ass122}, type = {CENELEC_50128.SRAC}, 
       CENELEC_50128.EC.assumption_kind = {formal}}
] The overall sampling frequence of the odometer subsystem is therefore 
 14 khz, which includes sampling, computing and result communication 
 times ...
\end{isamarkuptext*}
\end{ltx}

This environment is mapped to a plain \LaTeX command via (again, recall @{docref "text-elements"}):
\begin{ltx}
  \NewEnviron{isamarkuptext*}[1][]{\isaDof[env={text},#1]{\BODY}}
\end{ltx}

For the command-based setup, \isadof provides a dispatcher that selects the most specific 
implementation for a given \inlineisar|doc_class|:

\begin{ltx}
%% The Isabelle/DOF dispatcher:
\newkeycommand+[\|]\isaDof[env={UNKNOWN},label=,type={dummyT},args={}][1]{%
  \ifcsname isaDof.\commandkey{type}\endcsname%
      \csname isaDof.\commandkey{type}\endcsname%
              [label=\commandkey{label},\commandkey{args}]{#1}%
  \else\relax\fi%
  \ifcsname isaDof.\commandkey{env}.\commandkey{type}\endcsname%
      \csname isaDof.\commandkey{env}.\commandkey{type}\endcsname%
              [label=\commandkey{label},\commandkey{args}]{#1}%
  \else%
      \message{Isabelle/DOF: Using default LaTeX representation for concept %
        "\commandkey{env}.\commandkey{type}".}%
      \ifcsname isaDof.\commandkey{env}\endcsname%
         \csname isaDof.\commandkey{env}\endcsname%
                [label=\commandkey{label}]{#1}%
      \else%
      \errmessage{Isabelle/DOF: No LaTeX representation for concept %
        "\commandkey{env}.\commandkey{type}" defined and no default %
        definition for "\commandkey{env}" available either.}%
      \fi%
  \fi%
}
\end{ltx}
\<close>

(*<*)
end
(*>*)
