(*************************************************************************
 * Copyright (C) 
 *               2019      The University of Exeter 
 *               2018-2019 The University of Paris-Saclay
 *               2018      The University of Sheffield
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

(*<*)
theory IsaDofApplications
  imports "Isabelle_DOF.scholarly_paper"
begin

use_template "lncs"
use_ontology "Isabelle_DOF.scholarly_paper"

open_monitor*[this::article] 
declare[[strict_monitor_checking=false]]

define_shortcut* isadof   \<rightleftharpoons> \<open>\isadof\<close>
                 LaTeX    \<rightleftharpoons> \<open>\LaTeX{}\<close>
                 dots     \<rightleftharpoons> \<open>\ldots\<close>
                 isabelle \<rightleftharpoons> \<open>Isabelle/HOL\<close>
                 Protege  \<rightleftharpoons> \<open>Prot{\'e}g{\'e}\<close>

(* slanted text in contrast to italics *)
define_macro* slanted_text \<rightleftharpoons> \<open>\textsl{\<close> _ \<open>}\<close>

ML\<open>

fun boxed_text_antiquotation name (* redefined in these more abstract terms *) =
    DOF_lib.gen_text_antiquotation name DOF_lib.report_text 
                           (fn ctxt => DOF_lib.string_2_text_antiquotation ctxt
                                       #> DOF_lib.enclose_env false ctxt "isarbox")

val neant = K(Latex.text("",\<^here>))

fun boxed_theory_text_antiquotation name (* redefined in these more abstract terms *) =
    DOF_lib.gen_text_antiquotation name DOF_lib.report_theory_text 
                           (fn ctxt => DOF_lib.string_2_theory_text_antiquotation ctxt 
                                        #> DOF_lib.enclose_env false ctxt "isarbox"
                                        (* #> neant *)) (*debugging *)

fun boxed_sml_text_antiquotation name  =
    DOF_lib.gen_text_antiquotation name (K(K())) 
                           (fn ctxt => Input.source_content 
                                        #> Latex.text 
                                        #> DOF_lib.enclose_env true ctxt "sml") 
                           (* the simplest conversion possible *)

fun boxed_pdf_antiquotation name =
    DOF_lib.gen_text_antiquotation name (K(K())) 
                           (fn ctxt => Input.source_content 
                                        #> Latex.text 
                                        #> DOF_lib.enclose_env true ctxt "out") 
                           (* the simplest conversion possible *)

fun boxed_latex_antiquotation name =
    DOF_lib.gen_text_antiquotation name (K(K())) 
                           (fn ctxt => Input.source_content 
                                        #> Latex.text 
                                        #> DOF_lib.enclose_env true ctxt "ltx") 
                           (* the simplest conversion possible *)

fun boxed_bash_antiquotation name =
    DOF_lib.gen_text_antiquotation name (K(K())) 
                           (fn ctxt => Input.source_content 
                                        #> Latex.text 
                                        #> DOF_lib.enclose_env true ctxt "bash") 
                           (* the simplest conversion possible *)
\<close>

setup\<open>boxed_text_antiquotation         \<^binding>\<open>boxed_text\<close> #>
      boxed_text_antiquotation         \<^binding>\<open>boxed_cartouche\<close> #>
      boxed_theory_text_antiquotation  \<^binding>\<open>boxed_theory_text\<close> #>

      boxed_sml_text_antiquotation     \<^binding>\<open>boxed_sml\<close> #>
      boxed_pdf_antiquotation          \<^binding>\<open>boxed_pdf\<close> #>
      boxed_latex_antiquotation        \<^binding>\<open>boxed_latex\<close>#>
      boxed_bash_antiquotation         \<^binding>\<open>boxed_bash\<close> 
     \<close>

(*>*)

title*[tit::title]       \<open>Using the Isabelle Ontology Framework\<close> 
subtitle*[stit::subtitle]\<open>Linking the Formal with the Informal\<close>
author*[adb,
        email       ="''a.brucker@sheffield.ac.uk''",
        orcid       ="''0000-0002-6355-1200''",
        affiliation ="''The University of Sheffield, Sheffield, UK''"]\<open>Achim D. Brucker\<close>
author*[idir,
        email       = "''idir.aitsadoune@centralesupelec.fr''",
        affiliation = "''CentraleSupelec, Paris, France''"]\<open>Idir Ait-Sadoune\<close>
author*[paolo,
        email       = "''paolo.crisafulli@irt-systemx.fr''",
        affiliation = "''IRT-SystemX, Paris, France''"]\<open>Paolo Crisafulli\<close>
author*[bu,
        email       = "\<open>wolff@lri.fr\<close>",
        affiliation = "\<open>Université Paris-Saclay, Paris, France\<close>"]\<open>Burkhart Wolff\<close>
    

abstract*[abs::abstract, keywordlist="[''Ontology'',''Ontological Modeling'',''Isabelle/DOF'']"]\<open>
   While Isabelle is mostly known as part of \<^isabelle> (an interactive 
   theorem prover), it actually provides a framework for developing a wide
   spectrum of applications. A particular strength
   of the Isabelle framework is the combination of text editing, formal verification,
   and code generation. 
   
   Up to now, Isabelle's document preparation system lacks a mechanism
   for ensuring the structure of different document types (as, e.g.,
   required in certification processes) in general and, in particular,
   mechanism for linking informal and formal parts of a document. 
   
   In this paper, we present \<^isadof>, a novel Document Ontology Framework 
   on top of Isabelle. \<^isadof> allows for conventional typesetting
   \<^emph>\<open>as well\<close> as formal development. We show how to model document
    ontologies inside \<^isadof>, how to use the resulting meta-information 
   for enforcing a certain document structure, and discuss ontology-specific 
   IDE support. 

   %% If you consider citing this paper, please refer to 
   %% @{cite "brucker.ea:isabelle-ontologies:2018"}.
\<close>

section*[intro::introduction]\<open> Introduction \<close>  
text*[introtext::introduction, level = "Some 1"]\<open> 
The linking of the \<^emph>\<open>formal\<close> to the \<^emph>\<open>informal\<close> is perhaps the
most pervasive challenge in the digitization of knowledge and its
propagation. This challenge incites numerous research efforts
summarized under the labels ``semantic web'', ``data mining'', or any
form of advanced ``semantic'' text processing.  A key role in
structuring this linking play \<^emph>\<open>document ontologies\<close> (also called
\<^emph>\<open>vocabulary\<close> in the semantic web community~@{cite "w3c:ontologies:2015"}), 
\<^ie>, a machine-readable form of the structure of documents as well as 
the document discourse.

Such ontologies can be used for the scientific discourse within scholarly
articles, mathematical libraries, and in the engineering discourse  
of standardized software certification 
documents~@{cite "boulanger:cenelec-50128:2015" and "cc:cc-part3:2006"}. 
Further applications are the domain-specific discourse in juridical texts or medical reports.  
In general, an ontology is a formal explicit description of \<^emph>\<open>concepts\<close> 
in a domain of discourse (called \<^emph>\<open>classes\<close>), properties of each concept 
describing \<^emph>\<open>attributes\<close> of the concept, as well as \<^emph>\<open>links\<close> between 
them. A particular link between concepts is the \<^emph>\<open>is-a\<close> relation declaring 
the instances of a subclass to be instances of the super-class.

The main objective of this paper is to present \<^isadof>, a novel
framework to \<^emph>\<open>model\<close> typed ontologies and to \<^emph>\<open>enforce\<close> them during
document evolution. Based on Isabelle infrastructures, ontologies may refer to
types, terms, proven theorems, code, or established assertions.
Based on a novel adaption of the Isabelle IDE, a document is checked to be 
\<^emph>\<open>conform\<close> to a particular ontology---\<^isadof> is designed to give fast user-feedback 
\<^emph>\<open>during the capture of content\<close>. This is particularly valuable for document 
changes, where the \<^emph>\<open>coherence\<close> between the formal and the informal parts of the
content can be mechanically checked.

To avoid any misunderstanding: \<^isadof>  is \<^emph>\<open>not a theory in HOL\<close> on ontologies and operations 
to track and trace links in texts, it is an \<^emph>\<open>environment to write structured text\<close> which 
\<^emph>\<open>may contain\<close> \<^isabelle> definitions and proofs like mathematical articles, tech-reports and
scientific papers---as the present one, which is written in \<^isadof> itself. \<^isadof> is a plugin 
into the Isabelle/Isar framework in the style of~@{cite "wenzel.ea:building:2007"}.
\<close>

(* declaring the forward references used in the subsequent sections *)  
(*<*)
declare_reference*[bgrnd::text_section]
declare_reference*[isadof::text_section]
declare_reference*[ontomod::text_section]
declare_reference*[ontopide::text_section]
declare_reference*[conclusion::text_section]
(*>*)
text*[plan::introduction, level="Some 1"]\<open> The plan of the paper is as follows: we start by 
introducing the underlying Isabelle system (@{text_section (unchecked) \<open>bgrnd\<close>}) followed by 
presenting the essentials of  \<^isadof> and its ontology language (@{text_section (unchecked) \<open>isadof\<close>}). 
It follows @{text_section (unchecked) \<open>ontomod\<close>}, where we present three application 
scenarios from the point of view of the ontology modeling. In @{text_section (unchecked) \<open>ontopide\<close>}
we discuss the user-interaction generated from the ontological definitions.  Finally, we draw 
conclusions and discuss related work in @{text_section (unchecked) \<open>conclusion\<close>}. \<close>  

section*[bgrnd::text_section,main_author="Some(@{docitem ''bu''}::author)"]
        \<open> Background: The Isabelle System \<close>
text*[background::introduction, level="Some 1"]\<open>
While Isabelle is widely perceived as an interactive theorem prover for HOL 
(Higher-order Logic)~@{cite "nipkow.ea:isabelle:2002"}, we would like to emphasize the view that 
Isabelle is far more than that: it is the \<^emph>\<open>Eclipse of Formal Methods Tools\<close>.  This refers to the
``\<^slanted_text>\<open>generic system framework of Isabelle/Isar underlying recent versions of Isabelle.  
  Among other things, Isar provides an infrastructure for Isabelle plug-ins, comprising extensible 
  state components and extensible syntax that can be bound to ML programs. Thus, the Isabelle/Isar 
  architecture may be understood as an extension and refinement of the traditional `LCF approach', 
  with explicit infrastructure for building derivative \<^emph>\<open>systems\<close>.\<close>''~@{cite "wenzel.ea:building:2007"} 

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

text*[blug::introduction, level="Some 1"]\<open> The Isabelle system architecture shown in @{figure \<open>architecture\<close>}
 comes with many layers, with Standard ML (SML) at the bottom layer as implementation 
language. The architecture actually foresees a \<^emph>\<open>Nano-Kernel\<close> (our terminology) which 
resides in the SML structure \<^ML_structure>\<open>Context\<close>. This structure provides a kind of container called 
\<^emph>\<open>context\<close> providing an identity, an ancestor-list as well as typed, user-defined state 
for components (plugins) such as \<^isadof>. On top of the latter, the LCF-Kernel, tactics, 
automated proof procedures as well as specific support for higher specification constructs
were built. \<close>
    
text\<open> We would like to detail the documentation generation of the architecture,
which is based on literate specification commands such as \<^theory_text>\<open>section\<close> \<^dots>, 
\<^theory_text>\<open>subsection\<close> \<^dots>, \<^theory_text>\<open>text\<close> \<^dots>, etc.
Thus, a user can add a simple text:
  @{boxed_theory_text [display]\<open>
text\<open> This is a description.\<close>\<close>}
These text-commands can be arbitrarily mixed with other commands stating definitions, proofs, code, etc.,
and will result in the corresponding output in generated \<^LaTeX> or HTML documents. 
Now, \<^emph>\<open>inside\<close> the textual content, it is possible to embed a \<^emph>\<open>text-antiquotation\<close>:
@{boxed_theory_text [display]\<open>
   text\<open> According to the \<^emph>\<open>reflexivity\<close> axiom @{thm refl}, 
         we obtain in \<Gamma> for @{term "fac 5"} the result @{value "fac 5"}.\<close>\<close>}

which is represented in the generated output by:
@{boxed_pdf [display]\<open>According to the reflexivity axiom $x = x$, we obtain in $\Gamma$ for $\operatorname{fac} 5$ the result $120$.\<close>}

where \<^theory_text>\<open>refl\<close> is actually the reference to the axiom of reflexivity in HOL. 
For the antiquotation \<^theory_text>\<open>@{value "''fac 5''"}\<close>  we assume the usual definition for 
\<^theory_text>\<open>fac\<close> in HOL.
\<close>

text*[anti::introduction, level = "Some 1"]\<open> Thus, antiquotations can refer to formal content, 
can be type-checked before being displayed and can be used for calculations before actually being 
typeset. When editing, Isabelle's PIDE offers auto-completion and error-messages while typing the 
above \<^emph>\<open>semi-formal\<close> content.\<close>

section*[isadof::technical,main_author="Some(@{docitem ''adb''}::author)"]\<open> \<^isadof> \<close>
   
text\<open> An \<^isadof> document consists of three components: 
\<^item> the \<^emph>\<open>ontology definition\<close> which is an Isabelle theory file with definitions
  for document-classes and all auxiliary datatypes.  
\<^item> the \<^emph>\<open>core\<close> of the document itself which is an Isabelle theory
  importing the ontology definition. \<^isadof> provides an own family of text-element
  commands such as \<^theory_text>\<open>title*\<close>, \<^theory_text>\<open>section*\<close>, \<^theory_text>\<open>text*\<close>, etc., 
  which can be annotated with meta-information defined in the underlying  ontology definition.
\<^item> the \<^emph>\<open>layout definition\<close> for the given ontology exploiting this meta-information.
\<close>
text\<open>\<^isadof> is a novel Isabelle system component providing specific support for all these 
three parts. Note that the document core \<^emph>\<open>may\<close>, but \<^emph>\<open>must\<close> not 
use Isabelle definitions or proofs for checking the formal content---the 
present paper is actually an example of a document not containing any proof.

 The document generation process of \<^isadof> is currently restricted to \<^LaTeX>, which means
that the layout is defined by a set of \<^LaTeX> style files. Several layout 
definitions for one ontology are possible and pave the way that different \<^emph>\<open>views\<close> for
the same central document were generated, addressing the needs of different purposes `
and/or target readers. 

 While the ontology and the layout definition will have to be developed by an expert
with knowledge over Isabelle and \<^isadof> and the back end technology depending on the layout 
definition, the core is intended to require only minimal knowledge of these two. The situation
is similar to \<^LaTeX>-users, who usually have minimal knowledge about the content in 
style-files (\<^verbatim>\<open>.sty\<close>-files). In the document core authors \<^emph>\<open>can\<close>  use \<^LaTeX>  commands in 
their source, but this limits the possibility of using different representation technologies, 
\<^eg>, HTML, and increases the risk of arcane error-messages in generated \<^LaTeX>. 

The \<^isadof> ontology specification language consists basically on a notation for document classes, 
where the attributes were typed with HOL-types and can be instantiated by terms HOL-terms, \<^ie>, 
the actual parsers and type-checkers of the Isabelle system were reused. This has the particular 
advantage that \<^isadof> commands can be arbitrarily mixed with Isabelle/HOL commands providing the 
machinery for type declarations and term specifications such as enumerations. In particular, 
document class definitions provide:
\<^item>  a HOL-type for each document class as well as inheritance, 
\<^item>  support for attributes with HOL-types and optional default values,
\<^item>  support for overriding of attribute defaults but not overloading, and
\<^item>  text-elements annotated with document classes; they are mutable 
   instances of document classes.\<close>

text\<open>
Attributes referring to other ontological concepts are called \<^emph>\<open>links\<close>. The HOL-types inside the 
document specification language support built-in types for Isabelle/HOL \<^theory_text>\<open>typ\<close>'s, \<^theory_text>\<open>term\<close>'s, and
\<^theory_text>\<open>thm\<close>'s reflecting internal Isabelle's internal types  for these entities; when denoted in 
HOL-terms  to instantiate an attribute, for example, there is a  specific syntax 
(called \<^emph>\<open>inner syntax antiquotations\<close>) that is checked by \<^isadof> for consistency.

Document classes can have a \<^theory_text>\<open>where\<close> clause containing a regular expression over class names. 
Classes with such a \<^theory_text>\<open>where\<close>  were called \<^emph>\<open>monitor classes\<close>. While document classes and their 
inheritance relation structure meta-data of text-elements in an object-oriented manner, monitor 
classes enforce structural organization of documents via the language specified by the regular 
expression enforcing a sequence of text-elements that belong to the corresponding classes.  \<^vs>\<open>-0.4cm\<close>\<close>

section*[ontomod::text_section]\<open> Modeling Ontologies in \<^isadof> \<close> 
text\<open> In this section, we will use the \<^isadof> document ontology language for three different 
application scenarios: for scholarly papers, for mathematical exam sheets as well as standardization 
documents where the concepts of the standard are captured in the ontology. For space reasons, we 
will concentrate in all three cases on aspects of the modeling due to space limitations.\<close>

subsection*[scholar_onto::example]\<open> The Scholar Paper Scenario: Eating One's Own Dog Food. \<close>  
text\<open> The following ontology is a simple ontology modeling scientific papers. In this 
\<^isadof> application scenario, we deliberately refrain from integrating references to
(Isabelle) formal content in order  demonstrate that \<^isadof> is not a framework from 
Isabelle users to Isabelle users only. Of course, such references can be added easily and 
represent a particular strength of \<^isadof>.\<close>

(*
text\<open>\begin{figure}
@{boxed_theory_text [display]\<open>
doc_class title =
   short_title :: "string option"  <=  None
     
doc_class subtitle =
   abbrev :: "string option"       <=  None

doc_class author =
   affiliation :: "string"

doc_class abstract =
   keyword_list :: "string list"  <= None

doc_class text_section = 
   main_author :: "author option"  <=  None 
   todo_list   :: "string list"    <=  "[]"
\<close>}
\caption{The core of the ontology definition for writing scholarly papers.}
\label{fig:paper-onto-core}
\end{figure}\<close>
*) 
text*["paper_onto_core"::figure2, 
      caption="''The core of the ontology definition for writing scholarly papers.''"]
\<open>@{boxed_theory_text [display]\<open>
doc_class title =
   short_title :: "string option"  <=  None
     
doc_class subtitle =
   abbrev :: "string option"       <=  None

doc_class author =
   affiliation :: "string"

doc_class abstract =
   keyword_list :: "string list"  <= None

doc_class text_section = 
   main_author :: "author option"  <=  None
   todo_list   :: "string list"    <=  "[]" 
\<close>}\<close>

text\<open> The first part of the ontology \<^theory_text>\<open>scholarly_paper\<close> 
(see \autoref{fig:paper-onto-core})
(see @{figure2 "paper_onto_core"})
contains the document class definitions
with the usual text-elements of a scientific paper. The attributes \<^theory_text>\<open>short_title\<close>, 
\<^theory_text>\<open>abbrev\<close> etc are introduced with their types as well as their default values.
Our model prescribes an optional \<^theory_text>\<open>main_author\<close> and a todo-list attached to an arbitrary 
text section; since instances of this class are mutable (meta)-objects of text-elements, they
can be modified arbitrarily through subsequent text and of course globally during text evolution.
Since \<^theory_text>\<open>author\<close> is a HOL-type internally generated by \<^isadof> framework and can therefore
appear in the \<^theory_text>\<open>main_author\<close> attribute of the \<^theory_text>\<open>text_section\<close> class; 
semantic links between concepts can be modeled this way.

The translation of its content to, \<^eg>, Springer's \<^LaTeX> setup for the Lecture Notes in Computer 
Science Series, as required by many scientific conferences, is mostly straight-forward. 
\<^vs>\<open>-0.8cm\<close>\<close>

figure*[fig1::figure,spawn_columns=False,relative_width="95",src="''figures/Dogfood-Intro''"]
       \<open> Ouroboros I: This paper from inside \<^dots> \<close>  

text\<open>\<^vs>\<open>-0.8cm\<close> @{figure \<open>fig1\<close>} shows the corresponding view in the Isabelle/PIDE of the present paper.
Note that the text uses \<^isadof>'s own text-commands containing the meta-information provided by
the underlying ontology.
We proceed by a definition of \<^theory_text>\<open>introduction\<close>'s, which we define as the extension of
\<^theory_text>\<open>text_section\<close> which is intended to capture common infrastructure:
@{boxed_theory_text [display]\<open>
doc_class introduction = text_section +
   comment :: string
\<close>}
As a consequence of the definition as extension, the \<^theory_text>\<open>introduction\<close> class
inherits the attributes \<^theory_text>\<open>main_author\<close> and \<^theory_text>\<open>todo_list\<close> together with 
the corresponding default values.

As a variant of the introduction, we could add here an attribute that contains the formal 
claims of the article --- either here, or, for example, in the keyword list of the abstract. 
As type, one could use either the built-in type \<^theory_text>\<open>term\<close> (for syntactically correct, 
but not necessarily proven entity) or \<^theory_text>\<open>thm\<close> (for formally proven entities). It suffices 
to add the line:
@{boxed_theory_text [display]\<open>
   claims  :: "thm list"
\<close>}
and to extent the \<^LaTeX>-style accordingly to handle the additional field. 
Note that \<^theory_text>\<open>term\<close> and \<^theory_text>\<open>thm\<close> are types reflecting the core-types of the
Isabelle kernel. In a corresponding conclusion section, one could model analogously an 
achievement section; by programming a specific compliance check in SML, the implementation 
of automated forms of validation check for specific categories of papers is envisageable. 
Since this requires deeper knowledge in Isabelle programming, however, we consider this out 
of the scope of this paper.

We proceed more or less conventionally by the subsequent sections (\autoref{fig:paper-onto-sections})\<close>  
text\<open>
\begin{figure}
@{boxed_theory_text [display]\<open>
doc_class technical = text_section +
   definition_list :: "string list" <=  "[]"

doc_class example   = text_section +
   comment :: string

doc_class conclusion = text_section +
   main_author :: "author option"  <=  None
   
doc_class related_work = conclusion +
   main_author :: "author option"  <=  None

doc_class bibliography =
   style :: "string option"  <=  "''LNCS''"
\<close>}
\caption{Various types of sections of a scholarly papers.}
\label{fig:paper-onto-sections}
\end{figure}\<close>  
text\<open>... and finish with a monitor class definition that enforces a textual ordering
in the document core by a regular expression (\autoref{fig:paper-onto-monitor}).\<close>  
text\<open>
\begin{figure}
@{boxed_theory_text [display]\<open>
doc_class article = 
   trace :: "(title + subtitle + author+ abstract +
              introduction + technical + example +
              conclusion + bibliography) list"
   where "(title       ~~ \<lbrakk>subtitle\<rbrakk>   ~~ \<lbrace>author\<rbrace>$^+$+  ~~  abstract    ~~
             introduction ~~  \<lbrace>technical || example\<rbrace>$^+$  ~~  conclusion ~~  
             bibliography)"
\<close>}
\caption{A monitor for the scholarly paper ontology.}
\label{fig:paper-onto-monitor}
\end{figure}
\<close>
text\<open> We might wish to add a component into our ontology that models figures to be included into 
the document. This boils down to the exercise of modeling structured data in the style of a 
functional programming language in HOL and to reuse the implicit HOL-type inside a suitable document 
class \<^theory_text>\<open>figure\<close>:
@{boxed_theory_text [display]\<open>
datatype placement = h | t | b | ht | hb   
doc_class figure   = text_section +
   relative_width   :: "int" (* percent of textwidth *)    
   src     :: "string"
   placement :: placement 
   spawn_columns :: bool <= True 
\<close>}
\<close>

text\<open> Alternatively, by including the HOL-libraries for rationals, it is possible to 
use fractions or even mathematical reals. This must be counterbalanced by syntactic 
and semantic convenience. Choosing the mathematical reals, \<^eg>, would have the drawback that 
attribute evaluation could be substantially more complicated.\<close>

figure*[fig_figures::figure,spawn_columns=False,relative_width="85",src="''figures/Dogfood-figures''"]
       \<open> Ouroboros II: figures \<^dots> \<close>

text\<open> The document class \<^theory_text>\<open>figure\<close> --- supported by the \<^isadof> text command 
\<^theory_text>\<open>figure*\<close> --- makes it possible to express the pictures and diagrams in this paper 
such as @{figure \<open>fig_figures\<close>}.
\<close>
         
subsection*[math_exam::example]\<open> The Math-Exam Scenario \<close> 
text\<open> The Math-Exam Scenario is an application with mixed formal and 
semi-formal content. It addresses applications where the author of the exam is not present 
during the exam and the preparation requires a very rigorous process, as the french 
\<^emph>\<open>baccaleaureat\<close> and exams at The University of Sheffield.

We assume that the content has four different types of addressees, which have a different
\<^emph>\<open>view\<close> on the integrated document: 

\<^item> the \<^emph>\<open>setter\<close>, \<^ie>, the author of the exam,
\<^item> the \<^emph>\<open>checker\<close>, \<^ie>, an internal person that checks 
  the exam for feasibility and non-ambiguity, 
\<^item> the \<^emph>\<open>external examiner\<close>, \<^ie>, an external person that checks 
  the exam for feasibility and non-ambiguity, and 
\<^item> the \<^emph>\<open>student\<close>, \<^ie>, the addressee of the exam. 
\<close>
text\<open> The latter quality assurance mechanism is used in many universities,
where for organizational reasons the execution of an exam takes place in facilities
where the author of the exam is not expected to be physically present.
Furthermore, we assume a simple grade system (thus, some calculation is required). \<close>  
text\<open>
\begin{figure}
@{boxed_theory_text [display]\<open>
doc_class Author = ...
datatype Subject =  algebra | geometry | statistical
datatype Grade =  A1 | A2 | A3

doc_class Header =  examTitle   :: string
                    examSubject :: Subject
                    date        :: string
                    timeAllowed :: int --  minutes

datatype ContentClass =  setter
                      | checker 
                      | external_examiner   
                      | student   

doc_class Exam_item = 
  concerns :: "ContentClass set"  

doc_class Exam_item = 
  concerns :: "ContentClass set"  

type_synonym SubQuestion = string
\<close>}
\caption{The core of the ontology modeling math exams.}
\label{fig:onto-exam}
\end{figure}\<close>  
text\<open>The heart of this ontology (see \autoref{fig:onto-exam}) is an alternation of questions and answers, 
where the answers can consist of simple yes-no answers (QCM style check-boxes) or lists of formulas. 
Since we do not
assume familiarity of the students with Isabelle (\<^theory_text>\<open>term\<close> would assume that this is a 
parse-able and type-checkable entity), we basically model a derivation as a sequence of strings
(see \autoref{fig:onto-questions}).\<close>  
text\<open>
\begin{figure}
@{boxed_theory_text [display]\<open>
doc_class Answer_Formal_Step =  Exam_item +
  justification :: string
  "term"        :: "string" 
  
doc_class Answer_YesNo =  Exam_item +
  step_label :: string
  yes_no     :: bool  -- \<open>for checkboxes\<close>

datatype Question_Type =   
  formal | informal | mixed 
  
doc_class Task = Exam_item +
  level    :: Level
  type     :: Question_Type
  subitems :: "(SubQuestion * 
                   (Answer_Formal_Step list + Answer_YesNo) list) list"
  concerns :: "ContentClass set" <= "UNIV" 
  mark     :: int
doc_class Exercise = Exam_item +
  type     :: Question_Type
  content  :: "(Task) list"
  concerns :: "ContentClass set" <= "UNIV" 
  mark     :: int
\<close>}
\caption{An exam can contain different types of questions.}
\label{fig:onto-questions}
\end{figure}\<close>
text\<open>
In many institutions, it makes sense to have a rigorous process of validation
for exam subjects: is the initial question correct? Is a proof in the sense of the
question possible? We model the possibility that the @{term examiner} validates a 
question by a sample proof validated by Isabelle (see \autoref{fig:onto-exam-monitor}). 
In our scenario this sample proofs are completely \<^emph>\<open>intern\<close>, \<^ie>, not exposed to the 
students but just additional material for the internal review process of the exam.\<close>  
text\<open>
\begin{figure}
@{boxed_theory_text [display]\<open>
doc_class Validation = 
   tests  :: "term list"  <="[]"
   proofs :: "thm list"   <="[]"
  
doc_class Solution = Exam_item +
  content  :: "Exercise list"
  valids   :: "Validation list"
  concerns :: "ContentClass set" <= "{setter,checker,external_examiner}"
  
doc_class MathExam=
  content :: "(Header + Author + Exercise) list"
  global_grade :: Grade 
  where "\<lbrace>Author\<rbrace>$^+$  ~~  Header ~~  \<lbrace>Exercise ~~ Solution\<rbrace>$^+$ "
\<close>}
\caption{Validating exams.}
\label{fig:onto-exam-monitor}
\end{figure}
\<close>
  
(*<*)declare_reference*["fig_qcm"::figure](*>*)

text\<open> Using the \<^LaTeX> package hyperref, it is possible to conceive an interactive 
exam-sheets with multiple-choice and/or free-response elements 
(see @{figure (unchecked) \<open>fig_qcm\<close>}). With the 
help of the latter, it is possible that students write in a browser a formal mathematical 
derivation---as part of an algebra exercise, for example---which is submitted to the examiners 
electronically. \<close>
figure*[fig_qcm::figure,spawn_columns=False,
        relative_width="90",src="''figures/InteractiveMathSheet''"]
        \<open> A Generated QCM Fragment \<^dots> \<close>  

subsection*[cenelec_onto::example]\<open> The Certification Scenario following CENELEC \<close>
text\<open> Documents to be provided in formal certifications (such as CENELEC
50126/50128, the DO-178B/C, or Common Criteria) can much profit from the control of ontological 
consistency: a lot of an evaluators work consists in tracing down the links from requirements over 
assumptions down to elements of evidence, be it in the models, the code, or the tests. 
In a certification process, traceability becomes a major concern; and providing
mechanisms to ensure complete traceability already at the development of the
global document will clearly increase speed and reduce risk and cost of a
certification process. Making the link-structure machine-checkable, be it between requirements, 
assumptions, their implementation and their discharge by evidence (be it tests, proofs, or
authoritative arguments), is therefore natural and has the potential to decrease the cost 
of developments targeting certifications. Continuously checking the links between the formal
and the semi-formal parts of such documents is particularly valuable during the (usually
collaborative) development effort. 

As in many other cases, formal certification documents come with an own terminology and pragmatics 
of what has to be demonstrated and where, and how the trace-ability of requirements through
design-models over code to system environment assumptions has to be assured.  
\<close>
text\<open> In the sequel, we present a simplified version of an ontological model used in a 
case-study~ @{cite "bezzecchi.ea:making:2018"}. We start with an introduction of the concept of requirement 
(see \autoref{fig:conceptual}). \<close>  
text\<open>
\begin{figure}
@{boxed_theory_text [display]\<open>
doc_class requirement = long_name :: "string option"

doc_class requirement_analysis = no :: "nat"
   where "requirement_item +"

doc_class hypothesis = requirement +
      hyp_type :: hyp_type <= physical  (* default *)
  
datatype ass_kind = informal | semiformal | formal
  
doc_class assumption = requirement +
     assumption_kind :: ass_kind <= informal 
\<close>}
\caption{Modeling requirements.}
\label{fig:conceptual}
\end{figure}\<close>

text\<open>Such ontologies can be enriched by larger explanations and examples, which may help
the team of engineers substantially when developing the central document for a certification, 
like an explication what is precisely the difference between an \<^emph>\<open>hypothesis\<close> and an 
\<^emph>\<open>assumption\<close> in the context of the evaluation standard. Since the PIDE makes for each 
document class its definition available by a simple mouse-click, this kind on meta-knowledge 
can be made far more accessible during the document evolution.

For example, the term of category \<^emph>\<open>assumption\<close> is used for domain-specific assumptions. 
It has formal, semi-formal and informal sub-categories. They have to be 
tracked and discharged by appropriate validation procedures within a 
certification process, by it by test or proof. It is different from a hypothesis, which is
globally assumed and accepted.

In the sequel, the category \<^emph>\<open>exported constraint\<close> (or \<^emph>\<open>ec\<close> for short)
is used for formal assumptions, that arise during the analysis,
design or implementation and have to be tracked till the final
evaluation target, and discharged by appropriate validation procedures 
within the certification process, by it by test or proof.  A particular class of interest 
is the category \<^emph>\<open>safety related application condition\<close> (or \<^emph>\<open>srac\<close> 
for short) which is used for \<^emph>\<open>ec\<close>'s that establish safety properties
of the evaluation target. Their track-ability throughout the certification
is therefore particularly critical. This is naturally modeled as follows:
@{boxed_theory_text [display]\<open>  
doc_class ec = assumption  +
     assumption_kind :: ass_kind <= (*default *) formal
                        
doc_class srac = ec  +
     assumption_kind :: ass_kind <= (*default *) formal
\<close>}
\<close>
   
section*[ontopide::technical]\<open> Ontology-based IDE support \<close>  
text\<open> We present a selection of interaction scenarios  @{example \<open>scholar_onto\<close>}
and @{example \<open>cenelec_onto\<close>} with Isabelle/PIDE instrumented by \<^isadof>. \<close>

subsection*[scholar_pide::example]\<open> A Scholarly Paper \<close>  
text\<open> In \autoref{fig-Dogfood-II-bgnd1} and \autoref{fig-bgnd-text_section} we show how
hovering over links permits to explore its meta-information. 
Clicking on a document class identifier permits to hyperlink into the corresponding
class definition (\autoref{fig:Dogfood-IV-jumpInDocCLass}); hovering over an attribute-definition
(which is qualified in order to disambiguate; \autoref{fig:Dogfood-V-attribute}).
\<close>
     
side_by_side_figure*["text-elements"::side_by_side_figure,anchor="''fig-Dogfood-II-bgnd1''",
                      caption="''Exploring a Reference of a Text-Element.''",relative_width="48",
                      src="''figures/Dogfood-II-bgnd1''",anchor2="''fig-bgnd-text_section''",
                      caption2="''Exploring the class of a text element.''",relative_width2="47",
                      src2="''figures/Dogfood-III-bgnd-text_section''"]\<open> Exploring text elements. \<close>

side_by_side_figure*["hyperlinks"::side_by_side_figure,anchor="''fig:Dogfood-IV-jumpInDocCLass''",
                      caption="''Hyperlink to Class-Definition.''",relative_width="48",
                      src="''figures/Dogfood-IV-jumpInDocCLass''",anchor2="''fig:Dogfood-V-attribute''",
                      caption2="''Exploring an attribute.''",relative_width2="47",
                      src2="''figures/Dogfood-III-bgnd-text_section''"]\<open> Hyperlinks.\<close>


(*<*)declare_reference*["figDogfoodVIlinkappl"::figure](*>*)
text\<open> An ontological reference application in \autoref{figDogfoodVIlinkappl}: the ontology-dependant 
antiquotation \<^theory_text>\<open>@{example ...}\<close> refers to the corresponding text-elements. Hovering allows 
for inspection, clicking for jumping to the definition.  If the link does not exist or has a 
non-compatible type, the text is not validated.  \<close>

figure*[figDogfoodVIlinkappl::figure,relative_width="80",src="''figures/Dogfood-V-attribute''"]
       \<open> Exploring an attribute (hyperlinked to the class). \<close> 
subsection*[cenelec_pide::example]\<open> CENELEC  \<close>
(*<*)declare_reference*[figfig3::figure](*>*)  
text\<open> The corresponding view in @{docitem (unchecked) \<open>figfig3\<close>} shows core part of a document,  
coherent to the @{example \<open>cenelec_onto\<close>}. The first sample shows standard Isabelle antiquotations 
@{cite "wenzel:isabelle-isar:2017"} into formal entities of a theory. This way, the informal parts 
of a document get ``formal content'' and become more robust under change.\<close>

figure*[figfig3::figure,relative_width="80",src="''figures/antiquotations-PIDE''"]
\<open> Standard antiquotations referring to theory elements.\<close>

(*<*)declare_reference*[figfig5::figure]  (*>*)
text\<open> The subsequent sample in @{figure (unchecked) \<open>figfig5\<close>} shows the definition of an 
\<^emph>\<open>safety-related application condition\<close>, a side-condition of a theorem which 
has the consequence that a certain calculation must be executed sufficiently fast on an embedded 
device. This condition can not be established inside the formal theory but has to be 
checked by system integration tests.\<close>
  
figure*[figfig5::figure, relative_width="80", src="''figures/srac-definition''"]
        \<open> Defining a SRAC reference \<^dots> \<close>
figure*[figfig7::figure, relative_width="80", src="''figures/srac-as-es-application''"]
        \<open> Using a SRAC as EC document reference. \<close>
       
text\<open> Now we reference in @{figure \<open>figfig7\<close>} this safety-related condition; 
however, this happens in a context where general \<^emph>\<open>exported constraints\<close> are listed. 
\<^isadof>'s checks establish that this is legal in the given ontology. 

This example shows that ontological modeling is indeed adequate for large technical,
collaboratively developed documentations, where modifications can lead easily to incoherence. 
The current checks help to systematically avoid this type of incoherence between formal and 
informal parts. \<close>    

section*[onto_future::technical]\<open> Monitor Classes \<close>  
text\<open> Besides sub-typing, there is another relation between
document classes: a class can be a \<^emph>\<open>monitor\<close> to other ones,
which is expressed by the occurrence of a @{theory_text \<open>where\<close>} clause
in the document class definition containing a regular
expression (see @{example \<open>scholar_onto\<close>}).
While class-extension refers to data-inheritance of attributes,
a monitor imposes structural constraints -- the order --
in which instances of monitored classes may occur. \<close>

text\<open>
The control of monitors is done by the commands:
\<^item> \<^theory_text>\<open>open_monitor*\<close> \<^emph>\<open><doc-class>\<close>  
\<^item> \<^theory_text>\<open>close_monitor*\<close> \<^emph>\<open><doc-class>\<close> 
\<close>
text\<open>
where the automaton of the monitor class is expected to be in a final state. In the final state, 
user-defined SML Monitors can be nested, so it is possible to "overlay" one or more monitoring 
classes and imposing different sets of structural constraints in a Classes which are neither 
directly nor indirectly (via inheritance) mentioned in the monitor are \<^emph>\<open>independent\<close> from a 
monitor; instances of independent test elements may occur freely. \<close>


section*[conclusion::conclusion]\<open> Conclusion and Related Work\<close>    
text\<open> We have demonstrated the use of \<^isadof>, a novel ontology modeling and enforcement
IDE deeply integrated into the Isabelle/Isar Framework. The two most distinguishing features are
\<^item> \<^isadof> and its ontology language  are a strongly typed language that allows
  for referring (albeit not reasoning) to entities of \<^isabelle>, most notably types, terms,
  and (formally proven) theorems, and
\<^item> \<^isadof> is supported by the Isabelle/PIDE framework; thus, the advantages of an IDE for 
  text-exploration (which is the type of this link? To which text element does this link refer?
  Which are the syntactic alternatives here?) were available during editing
  instead of a post-hoc validation process.
\<close>

text\<open> Of course, a conventional batch-process  also exists which can be used
for the validation of large document bases in a conventional continuous build process.
This combination of formal and semi-informal elements, as well as a systematic enforcement
of the coherence to a document ontology of the latter, is, as we believe, novel and offers 
a unique potential for the semantic treatment of scientific texts and technical documentations. \<close>

text\<open>
To our knowledge, this is the first ontology-driven framework for
editing mathematical and technical documents that focuses particularly
on documents mixing formal and informal content---a type of documents
that is very common in technical certification processes. We see
mainly one area of related works: IDEs and text editors that support
editing and checking of documents based on an ontology.  There is a
large group of ontology editors (\<^eg>, \<^Protege>~@{cite "protege"},
Fluent Editor~@{cite "cognitum"}, NeOn~@{cite "neon"}, or
OWLGrEd~@{cite "owlgred"}). With them, we share the support for defining
ontologies as well as auto-completion when editing documents based on
an ontology. While our ontology definitions are currently based on a
textual definition, widely used ontology editors (\<^eg>,
OWLGrEd~@{cite "owlgred"}) also support graphical notations. This could
be added to \<^isadof> in the future. A unique feature of \<^isadof> is the
deep integration of formal and informal text parts. The only other
work in this area we are aware of is rOntorium~@{cite "rontorium"}, a plugin
for \<^Protege> that integrates R~@{cite "adler:r:2010"} into an
ontology environment. Here, the main motivation behind this
integration is to allow for statistically analyze ontological
documents. Thus, this is complementary to our work.\<close>

text\<open> \<^isadof> in its present form has a number of technical short-comings as well 
  as potentials not yet explored. On the long list of the short-comings is the 
  fact that strings inside HOL-terms do not support, for example, Unicode. 
  For the moment, \<^isadof> is conceived as an 
  add-on for \<^isabelle>; a much deeper integration of \<^isadof> into Isabelle 
  could increase both performance and uniformity. Finally, different target 
  presentation (such as HTML) would be highly desirable in particular for the 
  math exam scenarios. And last but not least, it would be desirable that PIDE 
  itself is ``ontology-aware'' and can, for example, use meta-information
  to control read- and write accesses of \<^emph>\<open>parts\<close> of documents.
\<close>

paragraph\<open> Availability. \<close> 
text\<open> The implementation of the framework, the discussed ontology definitions, 
        and examples  are available at 
        \url{\dofurl}.\<close>
paragraph\<open> Acknowledgement. \<close> 
text\<open> This work was partly supported by  the framework of IRT SystemX, Paris-Saclay, France, 
and therefore granted with public funds within the scope of the Program ``Investissements d’Avenir''.\<close>

(*<*) 
section*[bib::bibliography]\<open>References\<close>

close_monitor*[this]


end
(*>*) 
  
