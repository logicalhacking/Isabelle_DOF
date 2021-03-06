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
theory "02_Background"
  imports "01_Introduction"
begin
(*>*)

chapter*[background::text_section]\<open> Background\<close>
section*[bgrnd1::introduction]\<open>The Isabelle System Architecture\<close>

figure*[architecture::figure,relative_width="95",src="''figures/isabelle-architecture''"]\<open> 
     The system architecture of Isabelle (left-hand side) and the 
     asynchronous communication between the Isabelle system and 
     the IDE (right-hand side). \<close>

text*[bg::introduction]\<open>
While Isabelle @{cite "nipkow.ea:isabelle:2002"} is widely perceived as an interactive theorem 
prover for HOL (Higher-order Logic)~@{cite "nipkow.ea:isabelle:2002"}, we would like to emphasize
the view that Isabelle is far more than that: it is the \<^emph>\<open>Eclipse of Formal Methods Tools\<close>.  This 
refers to the ``\<^emph>\<open>generic system framework of Isabelle/Isar underlying recent versions of Isabelle.  
Among other things, Isar provides an infrastructure for Isabelle plug-ins, comprising extensible 
state components and extensible syntax that can be bound to ML programs. Thus, the Isabelle/Isar 
architecture may be understood as an extension and refinement of the traditional `LCF approach', 
with explicit infrastructure for building derivative systems.\<close>''~@{cite "wenzel.ea:building:2007"} 

The current system framework offers moreover the following features:
\<^item> a build management grouping components into to pre-compiled sessions,
\<^item> a prover IDE (PIDE) framework~@{cite "wenzel:asynchronous:2014"} with various front-ends 
\<^item> documentation-generation,
\<^item> code generators for various target languages,
\<^item> an extensible front-end language Isabelle/Isar, and,
\<^item> last but not least, an LCF style, generic theorem prover kernel as 
  the most prominent and deeply integrated system component.


The Isabelle system architecture shown in @{docitem \<open>architecture\<close>} comes with many layers, 
with Standard ML (SML) at the bottom layer as implementation  language. The architecture actually 
foresees a \<^emph>\<open>Nano-Kernel\<close> (our terminology) which resides in the SML structure\<^boxed_sml>\<open>Context\<close>. 
This structure provides a kind of container called \<^emph>\<open>context\<close> providing an identity, an 
ancestor-list as well as typed, user-defined state for components (plugins) such as \<^isadof>. 
On top of the latter, the LCF-Kernel, tactics,  automated proof procedures as well as specific 
support for higher specification constructs were built.\<close>

section*[dof::introduction]\<open>The Document Model Required by \<^dof>\<close>
text\<open>
  In this section, we explain the assumed document model underlying our Document Ontology Framework 
  (\<^dof>) in general. In particular we discuss the concepts 
   \<^emph>\<open>integrated document\<close>\<^bindex>\<open>integrated document\<close>, \<^emph>\<open>sub-document\<close>\<^bindex>\<open>sub-document\<close>,  
  \<^emph>\<open>text-element\<close>\<^bindex>\<open>text-element\<close>, and \<^emph>\<open>semantic macros\<close>\<^bindex>\<open>semantic macros\<close> occurring 
  inside text-elements. Furthermore, we assume two different levels of parsers 
  (for \<^emph>\<open>outer\<close> and \<^emph>\<open>inner syntax\<close>) where the inner-syntax is basically a typed \<open>\<lambda>\<close>-calculus 
  and some Higher-order Logic (HOL)\<^bindex>\<open>HOL\<close>.
\<close>

(*<*)
declare_reference*["fig:dependency"::text_section]
(*>*)


text\<open>
  We assume a hierarchical document model\<^index>\<open>document model\<close>, \<^ie>, an \<^emph>\<open>integrated\<close> document 
  consist of a hierarchy \<^emph>\<open>sub-documents\<close>  (files) that can depend acyclically on each other. 
  Sub-documents can have different document types in order to capture documentations consisting of 
  documentation, models, proofs, code of various forms and other technical artifacts.  We call the 
  main sub-document type, for historical reasons, \<^emph>\<open>theory\<close>-files.  A theory file\<^bindex>\<open>theory!file\<close>
  consists of a \<^emph>\<open>header\<close>\<^bindex>\<open>header\<close>, a \<^emph>\<open>context definition\<close>\<^index>\<open>context\<close>, and a body 
  consisting of a sequence of \<^emph>\<open>command\<close>s (see @{figure (unchecked) "fig:dependency"}). Even 
  the header consists of a sequence of commands used for introductory text elements not depending on 
  any context. The context-definition contains an \<^boxed_theory_text>\<open>import\<close> and a 
  \<^boxed_theory_text>\<open>keyword\<close> section, for example:
@{boxed_theory_text [display]\<open>
  theory Example         \<comment>\<open>Name of the 'theory'\<close>
    imports              \<comment>\<open>Declaration of 'theory' dependencies\<close>
      Main               \<comment>\<open>Imports a library called 'Main'\<close>
    keywords             \<comment>\<open>Registration of keywords defined locally\<close>
      requirement        \<comment>\<open>A command for describing requirements\<close> \<close>}
  where \<^boxed_theory_text>\<open>Example\<close> is the abstract name of the text-file, \<^boxed_theory_text>\<open>Main\<close> 
  refers to an imported theory (recall that the import relation must be acyclic) and 
  \<^boxed_theory_text>\<open>keywords\<close> are used to separate commands from each other.
\<close>

text\<open> A text-element \<^index>\<open>text-element\<close> may look like this:

  @{boxed_theory_text [display]\<open>
text\<open> According to the \<^emph>\<open>reflexivity\<close> axiom @{thm refl}, 
   we obtain in \<Gamma> for @{term "fac 5"} the result @{value "fac 5"}.\<close>\<close>}
so it is a command \<^theory_text>\<open>text\<close> followed by an argument (here in  \<open>\<open> ... \<close>\<close> paranthesis) which 
contains characters and and a special notation for semantic macros \<^bindex>\<open>semantic macros\<close> 
(here \<^theory_text>\<open>@{term "fac 5"}).\<close>
\<close>

text\<open>
  We distinguish fundamentally two different syntactic levels:
  \<^item> the \<^emph>\<open>outer-syntax\<close>\<^bindex>\<open>syntax!outer\<close>\<^index>\<open>outer syntax|see {syntax, outer}\<close> (\<^ie>, the 
    syntax for commands) is processed by a lexer-library and parser combinators built on top, and
  \<^item> the \<^emph>\<open>inner-syntax\<close>\<^bindex>\<open>syntax!inner\<close>\<^index>\<open>inner syntax|see {syntax, inner}\<close> (\<^ie>, the 
    syntax for \<open>\<lambda>\<close>-terms in HOL) with its own parametric polymorphism type  checking.

  On the semantic level, we assume a validation process for an integrated document, where the 
  semantics of a command is a transformation \<open>\<theta> \<rightarrow> \<theta>\<close> for some system state \<open>\<theta>\<close>.
  This document model can be instantiated with outer-syntax commands for common 
  text elements, \<^eg>, \<^theory_text>\<open>section\<open>...\<close>\<close> or \<^theory_text>\<open>text\<open>...\<close>\<close>.  
  Thus, users can add informal text to a sub-document using a text command:
  @{boxed_theory_text [display] \<open>text\<open>This is a description.\<close>\<close> }
  This will type-set the corresponding text in, for example, a PDF document.  However, this 
  translation is not necessarily one-to-one: text elements can be enriched by formal, \<^ie>, 
  machine-checked content via \<^emph>\<open>semantic macros\<close>, called antiquotations\<^bindex>\<open>antiquotation\<close>:
  @{boxed_theory_text [display]
  \<open>text\<open> According to the \<^emph>\<open>reflexivity\<close> axiom @{thm refl}, we obtain in \<Gamma> 
         for @{term "fac 5"} the result @{value "fac 5"}.\<close>\<close>
  }
which is represented in the final document (\<^eg>, a PDF) by:
@{boxed_pdf [display]
\<open>According to the $\emph{reflexivity}$ axiom $\mathrm{x = x}$, we obtain in $\Gamma$ 
for $\operatorname{fac} \text{\textrm{5}}$ the result $\text{\textrm{120}}$.\<close>
 }

  Semantic macros are partial functions of type \<open>\<theta> \<rightarrow> text\<close>; since they can use the
  system state, they can perform all sorts of specific checks or evaluations (type-checks, 
  executions of code-elements, references to text-elements or proven theorems such as 
  \<open>refl\<close>, which is the reference to the axiom of reflexivity).

  Semantic macros establish \<^emph>\<open>formal content\<close> inside informal content; they can be 
  type-checked before being displayed and can be used for calculations before being 
  typeset. They represent the device for linking the formal with the informal. 
\<close>

figure*["fig:dependency"::figure,relative_width="70",src="''figures/document-hierarchy''"]
       \<open>A Theory-Graph in the Document Model. \<close>

section*[bgrnd21::introduction]\<open>Implementability of the Required Document Model\<close>
text\<open> 
  Batch-mode checkers for \<^dof> can be implemented in all systems of the LCF-style prover family, 
  \<^ie>, systems with a type-checked \<open>term\<close>, and abstract \<open>thm\<close>-type for theorems 
  (protected by a kernel).  This includes, \<^eg>, ProofPower, HOL4, HOL-light, Isabelle, or Coq
  and its derivatives. \<^dof> is, however, designed for fast interaction in an IDE. If a user wants
  to benefit from this experience, only Isabelle and Coq have the necessary infrastructure of 
  asynchronous proof-processing and support by a PIDE~@{cite "wenzel:asynchronous:2014" and 
  "wenzel:system:2014" and "barras.ea:pervasive:2013" and "faithfull.ea:coqoon:2018"} which 
  in many features over-accomplishes the required  features of \<^dof>. For example, current Isabelle 
  versions offer cascade-syntaxes (different syntaxes and even parser-technologies which can be 
  nested along the \<open>\<open>...\<close>\<close> barriers), while \<^dof> actually only requires a two-level syntax model.
\<close>

figure*["fig:dof-ide"::figure,relative_width="95",src="''figures/cicm2018-combined''"]\<open> 
     The \<^isadof> IDE (left) and the corresponding PDF (right), showing the first page
      of~@{cite "brucker.ea:isabelle-ontologies:2018"}.\<close>

text\<open> 
  We call the present implementation of \<^dof> on the Isabelle platform  \<^isadof> . 
  @{docitem "fig:dof-ide"} shows  a screen-shot of an introductory paper on 
  \<^isadof>~@{cite "brucker.ea:isabelle-ontologies:2018"}: the \<^isadof> PIDE can be seen on the left, 
  while the generated presentation in PDF is shown on the right.

  Isabelle provides, beyond the features required for \<^dof>, a lot of additional benefits. 
  Besides UTF8-support for characters used in text-elements, Isabelle offers built-in already a 
  mechanism user-programmable antiquotations \<^index>\<open>antiquotations\<close> which we use to implement
  semantic macros  \<^index>\<open>semantic macros\<close> in \<^isadof> (We will actually use these two terms
  as synonym in the context of \<^isadof>). Moreover, \<^isadof> allows for the asynchronous 
  evaluation and checking of the document content~@{cite "wenzel:asynchronous:2014" and 
  "wenzel:system:2014" and "barras.ea:pervasive:2013"} and is dynamically extensible. Its PIDE 
  provides a  \<^emph>\<open>continuous build, continuous check\<close>  functionality, syntax highlighting, and 
  auto-completion. It also provides infrastructure for displaying meta-information (\<^eg>, binding 
  and type annotation) as pop-ups, while hovering over sub-expressions.  A fine-grained dependency 
  analysis allows the processing of individual parts of theory files asynchronously, allowing 
  Isabelle to interactively process large (hundreds of theory files) documents.  Isabelle can group 
  sub-documents into sessions, \<^ie>, sub-graphs of the document-structure that can be ``pre-compiled'' 
  and loaded instantaneously, \<^ie>, without re-processing, which is an important means to scale up. \<close>

(*<*) 
end
(*>*) 
  
