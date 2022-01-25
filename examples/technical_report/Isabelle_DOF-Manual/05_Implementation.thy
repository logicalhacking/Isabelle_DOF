(*************************************************************************
 * Copyright (C) 
 *               2019-2021 University of Exeter 
 *               2018-2021 University of Paris-Saclay
 *               2018      The University of Sheffield
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

(*<*)
theory "05_Implementation"
  imports "04_RefMan"
begin
(*>*)


chapter*[isadof_developers::text_section]\<open>Extending \<^isadof>\<close>
text\<open>
  In this chapter, we describe the basic implementation aspects of \<^isadof>, which is based on 
  the following design-decisions:
  \<^item> the entire \<^isadof> is a ``pure add-on,'' \<^ie>, we deliberately resign on the possibility to 
    modify Isabelle itself.
  \<^item> we made a small exception to this rule: the \<^isadof> package modifies in its installation 
    about 10 lines in the \LaTeX-generator (\path{src/patches/thy_output.ML}).
  \<^item> we decided to make the markup-generation by itself to adapt it as well as possible to the 
    needs of tracking the linking in documents.
  \<^item> \<^isadof> is deeply integrated into the Isabelle's IDE (PIDE) to give immediate feedback during 
    editing and other forms of document evolution.
\<close>
text\<open>
  Semantic macros, as required by our document model, are called \<^emph>\<open>document antiquotations\<close>
  in the Isabelle literature~@{cite "wenzel:isabelle-isar:2020"}. While Isabelle's code-antiquotations 
  are an old concept going back to Lisp and having found via SML and OCaml their ways into modern 
  proof systems, special annotation syntax inside documentation comments have their roots in 
  documentation generators such as Javadoc. Their use, however, as a mechanism to embed 
  machine-checked \<^emph>\<open>formal content\<close> is usually very limited and also lacks 
  IDE support.
\<close>

section\<open>\<^isadof>: A User-Defined Plugin in Isabelle/Isar\<close>
text\<open> 
  A plugin in Isabelle starts with defining the local data and registering it in the framework. As 
  mentioned before, contexts are structures with independent cells/compartments having three
  primitives \<^boxed_sml>\<open>init\<close>,  \<^boxed_sml>\<open>extend\<close> and  \<^boxed_sml>\<open>merge\<close>. Technically this is done by 
  instantiating a functor  \<^boxed_sml>\<open>Generic_Data\<close>, and the following fairly typical code-fragment 
  is drawn from \<^isadof>:

@{boxed_sml [display]
\<open>structure Data = Generic_Data
(  type T = docobj_tab * docclass_tab * ...
   val empty  = (initial_docobj_tab, initial_docclass_tab, ...) 
   val extend = I
   fun merge((d1,c1,...),(d2,c2,...)) = (merge_docobj_tab  (d1,d2,...), 
                                         merge_docclass_tab(c1,c2,...))
);\<close>}
  where the table  \<^boxed_sml>\<open>docobj_tab\<close> manages document classes and  \<^boxed_sml>\<open>docclass_tab\<close> the
  environment for class definitions (inducing the inheritance relation). Other tables capture, \eg, 
  the class invariants, inner-syntax antiquotations. Operations follow the MVC-pattern, where 
  Isabelle/Isar provides the controller part. A typical model operation has the type:

@{boxed_sml [display]
\<open>val opn :: <args_type> -> Context.generic -> Context.generic\<close>}
  representing a transformation on system contexts. For example, the operation of declaring a local 
  reference in the context is presented as follows:

@{boxed_sml [display]
\<open>fun declare_object_local oid ctxt  =
let fun decl {tab,maxano} = {tab=Symtab.update_new(oid,NONE) tab,
                             maxano=maxano}
in  (Data.map(apfst decl)(ctxt)
  handle Symtab.DUP _ =>
              error("multiple declaration of document reference"))
end\<close>}
  where \<^boxed_theory_text>\<open>Data.map\<close> is the update function resulting from the instantiation of the 
  functor  \<^boxed_sml>\<open>Generic_Data\<close>. This code fragment uses operations from a library structure 
   \<^boxed_sml>\<open>Symtab\<close> that were used to update the appropriate table for document objects in
  the plugin-local state. Possible exceptions to the update operation were mapped to a system-global 
  error reporting function.

  Finally, the view-aspects were handled by an API for parsing-combinators. The library structure 
   \<^boxed_sml>\<open>Scan\<close> provides the operators:

@{boxed_sml [display]
\<open>op ||     : ('a -> 'b) * ('a -> 'b) -> 'a -> 'b
op --     : ('a -> 'b * 'c) * ('c -> 'd * 'e) -> 'a -> ('b * 'd) * 'e
op >>     : ('a -> 'b * 'c) * ('b -> 'd) -> 'a -> 'd * 'c
op option : ('a -> 'b * 'a) -> 'a -> 'b option * 'a
op repeat : ('a -> 'b * 'a) -> 'a -> 'b list * 'a \<close>}
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

  The ``model'' \<^boxed_theory_text>\<open>declare_reference_opn\<close> and ``new'' \<^boxed_theory_text>\<open>attributes\<close> parts were 
  combined via the piping operator and registered in the Isar toplevel:

@{boxed_sml [display]
\<open>fun declare_reference_opn (((oid,_),_),_) =
                 (Toplevel.theory (DOF_core.declare_object_global oid))
  val _ = Outer_Syntax.command <@>{command_keyword "declare_reference"}
          "declare document reference"
          (attributes >> declare_reference_opn);\<close>}

  Altogether, this gives the extension of Isabelle/HOL with Isar syntax and semantics for the 
  new \emph{command}:

@{boxed_theory_text [display]\<open>
declare_reference [lal::requirement, alpha="main", beta=42]
\<close>}

  The construction also generates implicitly some markup information; for example, when hovering
  over the \<^boxed_theory_text>\<open>declare_reference\<close> command in the IDE, a popup window with the text: 
  ``declare document reference'' will appear.
\<close>

section\<open>Programming Antiquotations\<close>
text\<open>
  The definition and registration of text antiquotations and ML-antiquotations is similar in 
  principle: based on a number of combinators, new user-defined antiquotation syntax and semantics
  can be added to the system that works on the internal plugin-data freely. For example, in

@{boxed_sml [display]
\<open>val _ = Theory.setup(
          Thy_Output.antiquotation <@>{binding docitem} 
                                   docitem_antiq_parser 
                                   (docitem_antiq_gen default_cid) #>
          ML_Antiquotation.inline  <@>{binding docitem_value} 
                                   ML_antiq_docitem_value)\<close>}
  the text antiquotation \<^boxed_theory_text>\<open>docitem\<close> is declared and bounded to a parser for the argument 
  syntax and the overall semantics. This code defines a generic antiquotation to be used in text 
  elements such as

@{boxed_theory_text [display]\<open>
text\<open>as defined in <@>{docitem \<open>d1\<close>} ...\<close>
\<close>}

  The subsequent registration \<^boxed_theory_text>\<open>docitem_value\<close> binds code to a ML-antiquotation usable 
  in an ML context for user-defined extensions; it permits the access to the current ``value'' 
  of document element, \ie; a term with the entire update history.

  It is possible to generate antiquotations \emph{dynamically}, as a consequence of a class 
  definition in ODL. The processing of the ODL class \<^boxed_theory_text>\<open>definition\<close> also \emph{generates}
  a text antiquotation \<^boxed_theory_text>\<open>@{definition \<open>d1\<close>}\<close>, which works similar to 
  \<^boxed_theory_text>\<open>@{docitem \<open>d1\<close>}\<close> except for an additional type-check that assures that 
  \<^boxed_theory_text>\<open>d1\<close> is a reference to a definition. These type-checks support the subclass hierarchy.
\<close>

section\<open>Implementing Second-level Type-Checking\<close>
text\<open>
  On expressions for attribute values, for which we chose to use HOL syntax to avoid that users 
  need to learn another syntax, we implemented an own pass over type-checked terms. Stored in the 
  late-binding table \<^boxed_theory_text>\<open>ISA_transformer_tab\<close>, we register for each inner-syntax-annotation 
  (ISA's), a function of type

@{boxed_sml [display]
\<open>   theory -> term * typ * Position.T -> term option\<close>}

  Executed in a second pass of term parsing, ISA's may just return \<^boxed_theory_text>\<open>None\<close>. This is 
  adequate for ISA's just performing some checking in the logical context \<^boxed_theory_text>\<open>theory\<close>; 
  ISA's of this kind report errors  by exceptions. In contrast, \<^emph>\<open>transforming\<close> ISA's will 
  yield a term; this is adequate, for example, by replacing a string-reference to some term denoted 
  by it. This late-binding table is also used to generate standard inner-syntax-antiquotations from 
  a \<^boxed_theory_text>\<open>doc_class\<close>.
\<close>

section\<open>Programming Class Invariants\<close>
text\<open>
  See \<^technical>\<open>sec:low_level_inv\<close>.
\<close>

section\<open>Implementing Monitors\<close>
text\<open>
  Since monitor-clauses have a regular expression syntax, it is natural to implement them as 
  deterministic automata. These are stored in the  \<^boxed_theory_text>\<open>docobj_tab\<close> for monitor-objects 
  in the \<^isadof> component. We implemented the functions:

@{boxed_sml [display]
\<open>  val  enabled : automaton -> env -> cid list
   val  next    : automaton -> env -> cid -> automaton\<close>}
  where \<^boxed_theory_text>\<open>env\<close> is basically a map between internal automaton states and class-id's 
  (\<^boxed_theory_text>\<open>cid\<close>'s). An automaton is said to be \<^emph>\<open>enabled\<close> for a class-id, 
  iff it either occurs in its accept-set or its reject-set (see @{docitem "sec:monitors"}). During 
  top-down document validation, whenever a text-element is encountered, it is checked if a monitor 
  is \emph{enabled} for this class; in this case, the \<^boxed_theory_text>\<open>next\<close>-operation is executed. The 
  transformed automaton recognizing the rest-language is stored in \<^boxed_theory_text>\<open>docobj_tab\<close> if
  possible; otherwise, if \<^boxed_theory_text>\<open>next\<close> fails, an error is reported. The automata implementation 
  is, in large parts, generated from a formalization of functional automata~\cite{nipkow.ea:functional-Automata-afp:2004}.
\<close>

section\<open>The \LaTeX-Core of \<^isadof>\<close>
text\<open>
  The \LaTeX-implementation of \<^isadof> heavily relies on the 
  ``keycommand''~@{cite "chervet:keycommand:2010"} package. In fact, the core \<^isadof> \LaTeX-commands
  are just wrappers for the corresponding commands from the keycommand package:

@{boxed_latex [display]
\<open>\newcommand\newisadof[1]{%
  \expandafter\newkeycommand\csname isaDof.#1\endcsname}%
\newcommand\renewisadof[1]{%
  \expandafter\renewkeycommand\csname isaDof.#1\endcsname}%
\newcommand\provideisadof[1]{%
  \expandafter\providekeycommand\csname isaDof.#1\endcsname}%\<close>}

  The \LaTeX-generator of \<^isadof> maps each \<^boxed_theory_text>\<open>doc_item\<close> to an \LaTeX-environment (recall
  @{docitem "text-elements"}). As generic \<^boxed_theory_text>\<open>doc_item\<close> are derived from the text element, 
  the enviornment \inlineltx|{isamarkuptext*}| builds the core of \<^isadof>'s \LaTeX{} implementation. 
  For example, the @{docitem "ass123"} from page \pageref{ass123} is mapped to

@{boxed_latex [display]
\<open>\begin{isamarkuptext*}%
[label = {ass122},type = {CENELEC_50128.SRAC}, 
 args={label = {ass122}, type = {CENELEC_50128.SRAC}, 
       CENELEC_50128.EC.assumption_kind = {formal}}
] The overall sampling frequence of the odometer subsystem is therefore 
 14 khz, which includes sampling, computing and result communication 
 times ...
\end{isamarkuptext*}\<close>}

This environment is mapped to a plain \LaTeX command via (again, recall @{docitem "text-elements"}):
@{boxed_latex [display]
\<open> \NewEnviron{isamarkuptext*}[1][]{\isaDof[env={text},#1]{\BODY}} \<close>}

For the command-based setup, \<^isadof> provides a dispatcher that selects the most specific 
implementation for a given \<^boxed_theory_text>\<open>doc_class\<close>:

@{boxed_latex [display]
\<open>%% The Isabelle/DOF dispatcher:
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
}\<close>}
\<close>

(*<*)
end
(*>*)
