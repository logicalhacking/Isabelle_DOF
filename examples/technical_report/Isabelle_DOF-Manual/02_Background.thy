(*<*)
theory "02_Background"
  imports "01_Introduction"
begin
(*>*)

chapter*[bgrnd::text_section,main_author="Some(@{docitem ''adb''}::author)"]
        \<open> Background: The Isabelle System \<close>
section*[bgrnd1::introduction]\<open>Document Processing in Isabelle\<close>
text*[background::introduction]\<open>
While Isabelle @{cite "nipkow.ea:isabelle:2002"} is widely perceived as an interactive theorem prover
for HOL (Higher-order Logic)~@{cite "nipkow.ea:isabelle:2002"}, we
would like to emphasize the view that Isabelle is far more than that:
it is the \<^emph>\<open>Eclipse of Formal Methods Tools\<close>.  This refers to the
``\textsl{generic system framework of Isabelle/Isar underlying recent
  versions of Isabelle.  Among other things, Isar provides an
  infrastructure for Isabelle plug-ins, comprising extensible state
  components and extensible syntax that can be bound to ML
  programs. Thus, the Isabelle/Isar architecture may be understood as
  an extension and refinement of the traditional `LCF approach', with
  explicit infrastructure for building derivative
  \<^emph>\<open>systems\<close>.}''~@{cite "wenzel.ea:building:2007"} 

The current system framework offers moreover the following features:

\<^item> a build management grouping components into to pre-compiled sessions,
\<^item> a prover IDE (PIDE) framework~@{cite "wenzel:asynchronous:2014"} with various front-ends 
\<^item> documentation - and code generators,
\<^item> an extensible front-end language Isabelle/Isar, and,
\<^item> last but not least, an LCF style, generic theorem prover kernel as 
  the most prominent and deeply integrated system component.
\<close>  

figure*[architecture::figure,relative_width="100",src="''figures/isabelle-architecture''"]\<open> 
     The system architecture of Isabelle (left-hand side) and the 
     asynchronous communication between the Isabelle system and 
     the IDE (right-hand side). \<close>

text*[blug::introduction]\<open> The Isabelle system architecture shown in @{docitem_ref \<open>architecture\<close>}
 comes with many layers, with Standard ML (SML) at the bottom layer as implementation 
language. The architecture actually foresees a \<^emph>\<open>Nano-Kernel\<close> (our terminology) which 
resides in the SML structure \texttt{Context}. This structure provides a kind of container called 
\<^emph>\<open>context\<close> providing an identity, an ancestor-list as well as typed, user-defined state 
for components (plugins) such as \isadof. On top of the latter, the LCF-Kernel, tactics, 
automated proof procedures as well as specific support for higher specification constructs
were built. \<close>


text\<open> Of particular interest for \dof is the  documentation generation component in 
the architecture, which is based on literate specification commands such as \inlineisar+section+ 
\ldots, \inlineisar+subsection+ \ldots, \inlineisar+text+ \ldots, etc. Moreover, we assume that
\<^emph>\<open>inside\<close> text-elements, there are generic and extendible ways to add "semantic", i.e.
machine-checked sub-elements.

In the sequel, we will outline the general assumptions that \dof makes for the underlying
document model, and than explain how Isabelle as a framework fits into this picture.
\<close>


(*
Thus, a user can add a simple text:
\begin{isar}
  text\<Open>This is a description.\<Close>
\end{isar}
These text-commands can be arbitrarily mixed with other commands stating definitions, proofs, code, etc.,
and will result in the corresponding output in generated \LaTeX{} or HTML documents. 
Now, \<^emph>\<open>inside\<close> the textual content, it is possible to embed a \<^emph>\<open>text-antiquotation\<close>:
\begin{isar}
  text\<Open>According to the reflexivity axiom \at{thm refl}, we obtain in \<Gamma> 
           for \at{term "fac 5"} the result \at{value "fac 5"}.\<Close>
\end{isar}
which is represented in the generated output by:
\begin{out}
  According to the reflexivity axiom $x = x$, we obtain in $\Gamma$ for $\operatorname{fac} 5$ the result $120$.
\end{out}
where \inlineisar+refl+ is actually the reference to the axiom of reflexivity in HOL. 
For the antiquotation \inlineisar+\at{value "fac 5"}+  we assume the usual definition for 
\inlineisar+fac+ in HOL.
\<close>

text*[anti]\<open> Thus, antiquotations can refer to formal content, can be type-checked before being 
displayed and can be used for calculations before actually being typeset. When editing, 
Isabelle's PIDE offers auto-completion and error-messages while typing the above 
\<^emph>\<open>semi-formal\<close> content.  \<close>
*)


section*["sec:background"::introduction]\<open>The Required Document Model\<close>
text\<open>
In this section, we explain the assumed document model underlying
\dof in general; in particular the concepts \<^emph>\<open>integrated document\<close>, 
\<^emph>\<open>sub-document\<close> , \<^emph>\<open>text-element\<close> and \<^emph>\<open>semantic macros\<close> occurring 
inside text-elements. Furthermore, we assume two different levels of 
parsers (for \<^emph>\<open>outer\<close> and \<^emph>\<open>inner syntax\<close>) where the inner-syntax is basically a typed
$\lambda$-calculus and some Higher-order Logic (HOL).\<close>

figure*["fig:dependency"::figure,relative_width="50",src="''figures/document-hierarchy''"]\<open> 
     A Theory-Graph in the Document Model. \<close>


text\<open>
We assume a hierarchical document model, \ie, an \<^emph>\<open>integrated\<close> 
document consist of a hierarchy \<^emph>\<open>sub-documents\<close>  (files) that
can depend acyclically on each other. Sub-documents can have different
document types in order to capture documentations consisting of
documentation, models, proofs, code of various forms and other
technical artifacts.  We call the main sub-document type, for
historical reasons, \<^emph>\<open>theory\<close>-files.  A theory file consists of a
\<^emph>\<open>header\<close>, a \<^emph>\<open>context definition\<close>, and a body consisting of a
sequence of \<^emph>\<open>command\<close>s (@{figure "fig:dependency"}). Even the
header consists of a sequence of commands used for introductory text
elements not depending on any context.  The context-definition
contains an \inlineisar{import} and a \inlineisar{keyword} section,
for example:
\begin{isar}
theory Example         (* Name of the "theory"                     *)
  imports              (* Declaration of "theory" dependencies     *)
    Main               (* Imports a library called "Main"          *)
  keywords             (* Registration of keywords defined locally *)
    requirement        (* A command for describing requirements    *)
\end{isar}
where \inlineisar{Example} is the abstract name of the text-file,
\texttt{Main} refers to an imported theory (recall that the import
relation must be acyclic) and \inlineisar{keywords} are used to
separate commands from each other.\<close>

text\<open>We distinguish fundamentally two different syntactic levels:
\begin{compactenum}
\item the \emph{outer-syntax} (\ie, the syntax for commands) is processed 
  by a lexer-library and parser combinators built on top, and
\item the \emph{inner-syntax} (\ie, the syntax for $\lambda$-terms in
  HOL) with its own parametric polymorphism type checking.
\end{compactenum}
On the semantic level, we assume a validation process for an
integrated document, where the semantics of a command is a
transformation \inlineisar+\<theta> \<rightarrow> \<theta>+ for some
system state \inlineisar+\<theta>+. This document model can be
instantiated with outer-syntax commands for common text elements, \eg,
 \inlineisar+section{*...*}+ or \inlineisar+text{*...*}+.  Thus, users can add informal text to a 
sub-document using a text command:
\begin{isar}
  text\<Open>This is a description.\<Close>
\end{isar}
This will type-set the corresponding text in, for example, a PDF document. 
However, this translation is not necessarily one-to-one: text
elements can be enriched by formal, \ie, machine-checked content via
\emph{semantic macros}, called antiquotations:
\begin{isar}
  text\<Open>According to the reflexivity axiom @{thm refl}, we obtain in \<Gamma> 
        for @{term "fac 5"} the result @{value "fac 5"}.\<Close>
\end{isar}
which is represented in the final document (\eg, a PDF) by:
\begin{out}
  According to the reflexivity axiom $x = x$, we obtain in $\Gamma$ for $\operatorname{fac} 5$ the result $120$.
\end{out}
Semantic macros are partial functions of type %
\inlineisar+\<theta> \<rightarrow> text+; since they can use the
system state, they can perform all sorts of specific checks or
evaluations (type-checks, executions of code-elements, references to
text-elements or proven theorems such as \inlineisar+refl+, which is
the reference to the axiom of reflexivity).

Semantic macros establish \<^emph>\<open>formal content\<close> inside informal content; they can be 
type-checked before being displayed and can be used for calculations before being 
typeset. They represent the device for linking the formal with the informal. \<close>



section*[bgrnd21::introduction]\<open>Implementability of the Required Document Model.\<close>
text\<open> Batch-mode checkers for \dof can be implemented in all systems of the
LCF-style prover family, \ie, systems with a type-checked
\inlinesml{term}, and abstract \inlinesml{thm}-type for
theorems (protected by a kernel).  This includes, \eg, ProofPower,
HOL4, HOL-light, Isabelle, as well as Coq and its derivatives.  \dof
is, however, designed for fast interaction in an IDE. If a user wants
to benefit from this experience, only Isabelle and Coq have the
necessary infrastructure of asynchronous proof-processing and support
by a PIDE
@{cite "DBLP:conf/itp/Wenzel14" and "DBLP:journals/corr/Wenzel14" and "DBLP:conf/mkm/BarrasGHRTWW13"
       and "Faithfull:2018:COQ:3204179.3204223"} which in many features
over-accomplishes the required features of \dof. For example, current Isabelle versions
offer cascade-syntaxes (different syntaxes and even parser-technologies 
which can be nested along the \inlineisar+ \<Open> ... \<Close> + barriers, while
\dof actually only requires a 2-level syntax model.\<close>

figure*["fig:dof-ide"::figure,relative_width="80",src="''figures/cicm2018-combined''"]\<open> 
     The \isadof IDE (left) and the corresponding PDF (right).% , showing the first page
     % of~\cite{brucker.ea:isabelle-ontologies:2018}. \<close>

text\<open> We call the present implementation of \dof on the
 Isabelle platform  \isadof. In 
@{docitem "fig:dof-ide"},  a screen-shot of an introductory paper on \isadof 
@{cite "brucker.ea:isabelle-ontologies:2018"} is shown;
this paper focusses on a number of application scenarios and user-interface aspects. 
In @{docitem "fig:dof-ide"}, the \isadof PIDE can be seen on the left, while  
the generated presentation in PDF is shown on the right.

Isabelle provides, beyond the features required for \dof, a lot of
additional benefits. For example, it also allows the asynchronous
evaluation and checking of the document content
@{cite "DBLP:conf/itp/Wenzel14" and "DBLP:journals/corr/Wenzel14" and 
       "DBLP:conf/mkm/BarrasGHRTWW13"}
and is dynamically extensible. Its PIDE provides a \<^emph>\<open>continuous build, continuous check\<close> 
functionality, syntax highlighting, and IntelliSense-like auto-completion. 
It also provides infrastructure for
displaying meta-information (\eg, binding and type annotation) as
pop-ups, while hovering over sub-expressions.  A fine-grained
dependency analysis allows the processing of individual parts of
theory files asynchronously, allowing Isabelle to interactively
process large (hundreds of theory files) documents.  Isabelle can
group sub-documents into sessions, \ie, sub-graphs of the
document-structure that can be ``pre-compiled'' and loaded
instantaneously, \ie, without re-processing. \<close>

(*<*) 
end
(*>*) 
  
