(*************************************************************************
 * Copyright (C) 
 *               2019-2023      The University of Exeter 
 *               2018-2023 The University of Paris-Saclay
 *               2018      The University of Sheffield
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

(*<<*)  
theory 
  CENELEC_50128_Documentation
  imports  
  CENELEC_50128
           
begin

define_shortcut* dof     \<rightleftharpoons> \<open>\dof\<close>
                 isadof  \<rightleftharpoons> \<open>\isadof{}\<close>
define_shortcut* TeXLive \<rightleftharpoons> \<open>\TeXLive\<close>
                 BibTeX  \<rightleftharpoons> \<open>\BibTeX{}\<close> 
                 LaTeX   \<rightleftharpoons> \<open>\LaTeX{}\<close>
                 TeX     \<rightleftharpoons> \<open>\TeX{}\<close>
                 pdf     \<rightleftharpoons> \<open>PDF\<close>

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

setup\<open>(* std_text_antiquotation        \<^binding>\<open>my_text\<close> #> *)
      boxed_text_antiquotation         \<^binding>\<open>boxed_text\<close> #>
      (* std_text_antiquotation        \<^binding>\<open>my_cartouche\<close> #> *)
      boxed_text_antiquotation         \<^binding>\<open>boxed_cartouche\<close> #>
      (* std_theory_text_antiquotation \<^binding>\<open>my_theory_text\<close>#> *)
      boxed_theory_text_antiquotation  \<^binding>\<open>boxed_theory_text\<close> #>

      boxed_sml_text_antiquotation     \<^binding>\<open>boxed_sml\<close> #>
      boxed_pdf_antiquotation          \<^binding>\<open>boxed_pdf\<close> #>
      boxed_latex_antiquotation        \<^binding>\<open>boxed_latex\<close>#>
      boxed_bash_antiquotation         \<^binding>\<open>boxed_bash\<close>
     \<close>



(*>>*)  

section*[cenelec_onto::example]\<open>Writing Certification Documents \<^boxed_theory_text>\<open>CENELEC_50128\<close>\<close>
subsection\<open>The CENELEC 50128 Example\<close>
text\<open> 
  The ontology \<^verbatim>\<open>CENELEC_50128\<close>\index{ontology!CENELEC\_50128} is a small ontology modeling 
  documents for a certification following CENELEC 50128~@{cite "boulanger:cenelec-50128:2015"}.
  The \<^isadof> distribution contains a small example  using the ontology ``CENELEC\_50128'' in 
  the directory \nolinkurl{examples/CENELEC_50128/mini_odo/}. You can inspect/edit the 
  integrated source example by either 
  \<^item> starting Isabelle/jEdit using your graphical user interface (\<^eg>, by clicking on the 
    Isabelle-Icon provided by the Isabelle installation) and loading the file 
    \nolinkurl{examples/CENELEC_50128/mini_odo/mini_odo.thy}.
  \<^item> starting Isabelle/jEdit from the command line by calling:

@{boxed_bash [display]\<open>ë\prompt{\isadofdirn}ë 
  isabelle jedit examples/CENELEC_50128/mini_odo/mini_odo.thy \<close>}
\<close>
text\<open>\<^noindent> Finally, you
  \<^item>   can build the \<^pdf>-document by calling:
@{boxed_bash [display]\<open>ë\prompt{\isadofdirn}ë isabelle build mini_odo \<close>}
\<close>
 
subsection\<open>Modeling CENELEC 50128\<close>

text\<open>
  Documents to be provided in formal certifications (such as CENELEC 
  50128~@{cite "boulanger:cenelec-50128:2015"} or Common Criteria~@{cite "cc:cc-part3:2006"}) can 
  much profit from the control of ontological consistency:  a substantial amount of the work
  of evaluators in formal certification processes consists in  tracing down the links from 
  requirements over assumptions down to elements of evidence, be it in form of semi-formal 
  documentation, models, code, or tests.  In a certification process, traceability becomes a major 
  concern; and providing mechanisms to ensure complete traceability already at the development of 
  the integrated source can in our view increase the speed and reduce the risk certification 
  processes. Making the link-structure machine-checkable, be it between requirements, assumptions, 
  their implementation and their discharge by evidence (be it tests, proofs, or authoritative 
  arguments), has the potential in our view to decrease the cost of software developments 
  targeting certifications. 

  As in many other cases, formal certification documents come with an own terminology and pragmatics
  of what has to be demonstrated and where, and how the traceability of requirements through 
  design-models over code to system environment assumptions has to be assured.  

  In the sequel, we present a simplified version of an ontological model used in a 
  case-study~@{cite "bezzecchi.ea:making:2018"}. We start with an introduction of the concept of 
  requirement:

@{boxed_theory_text [display]\<open>
doc_class requirement = long_name :: "string option"

doc_class hypothesis = requirement +
      hyp_type :: hyp_type <= physical  (* default *)
  
datatype ass_kind = informal | semiformal | formal
  
doc_class assumption = requirement +
     assumption_kind :: ass_kind <= informal 
\<close>}

Such ontologies can be enriched by larger explanations and examples, which may help
the team of engineers substantially when developing the central document for a certification, 
like an explication of what is precisely the difference between an \<^typ>\<open>hypothesis\<close> and an 
\<^typ>\<open>assumption\<close> in the context of the evaluation standard. Since the PIDE makes for each 
document class its definition available by a simple mouse-click, this kind on meta-knowledge 
can be made far more accessible during the document evolution.

For example, the term of category \<^typ>\<open>assumption\<close> is used for domain-specific assumptions. 
It has \<^const>\<open>formal\<close>, \<^const>\<open>semiformal\<close> and \<^const>\<open>informal\<close> sub-categories. They have to be 
tracked and discharged by appropriate validation procedures within a 
certification process, be it by test or proof. It is different from a \<^typ>\<open>hypothesis\<close>, which is
globally assumed and accepted.

In the sequel, the category \<^typ>\<open>exported_constraint\<close> (or \<^typ>\<open>EC\<close> for short)
is used for formal assumptions, that arise during the analysis,
design or implementation and have to be tracked till the final
evaluation target, and discharged by appropriate validation procedures 
within the certification process, be it by test or proof.  A particular class of interest 
is the category \<^typ>\<open>safety_related_application_condition\<close> (or \<^typ>\<open>SRAC\<close> 
for short) which is used for \<^typ>\<open>EC\<close>'s that establish safety properties
of the evaluation target. Their traceability throughout the certification
is therefore particularly critical. This is naturally modeled as follows:
@{boxed_theory_text [display]\<open>  
doc_class EC = assumption  +
     assumption_kind :: ass_kind <= (*default *) formal
                        
doc_class SRAC = EC  +
     assumption_kind :: ass_kind <= (*default *) formal
\<close>}

We now can, \<^eg>, write 

@{boxed_theory_text [display]\<open>
text*[ass123::SRAC]\<open> 
  The overall sampling frequence of the odometer subsystem is therefore 
  14 khz, which includes sampling, computing and result communication 
  times \ldots
\<close>
\<close>}

This will be shown in the \<^pdf> as follows:
\<close>
text*[ass123::SRAC] \<open> The overall sampling frequency of the odometer
subsystem is therefore 14 khz, which includes sampling, computing and
result communication times \ldots \<close>

text\<open>Note that this \<^pdf>-output is the result of a specific setup for \<^typ>\<open>SRAC\<close>s.\<close>

subsection*[ontopide::technical]\<open>Editing Support for CENELEC 50128\<close>  
figure*[figfig3::figure,relative_width="95",file_src="''figures/antiquotations-PIDE.png''"]
\<open> Standard antiquotations referring to theory elements.\<close>
text\<open> The corresponding view in @{docitem  \<open>figfig3\<close>} shows core part of a document 
conforming to the \<^verbatim>\<open>CENELEC_50128\<close> ontology. The first sample shows standard Isabelle antiquotations 
@{cite "wenzel:isabelle-isar:2020"} into formal entities of a theory. This way, the informal parts 
of a document get ``formal content'' and become more robust under change.\<close>

figure*[figfig5::figure, relative_width="95", file_src="''figures/srac-definition.png''"]
        \<open> Defining a \<^typ>\<open>SRAC\<close> in the integrated source ... \<close>

figure*[figfig7::figure, relative_width="95", file_src="''figures/srac-as-es-application.png''"]
        \<open> Using a \<^typ>\<open>SRAC\<close> as \<^typ>\<open>EC\<close> document element. \<close>
text\<open> The subsequent sample in @{figure \<open>figfig5\<close>} shows the definition of a
\<^emph>\<open>safety-related application condition\<close>, a side-condition of a theorem which 
has the consequence that a certain calculation must be executed sufficiently fast on an embedded 
device. This condition can not be established inside the formal theory but has to be 
checked by system integration tests. Now we reference in @{figure  \<open>figfig7\<close>} this 
safety-related condition; however, this happens in a context where general \<^emph>\<open>exported constraints\<close> 
are listed. \<^isadof>'s checks and establishes that this is legal in the given ontology. 
\<close>    

text\<open>
\<^item> \<^theory_text>\<open>@{term_ \<open>term\<close> }\<close> parses and type-checks \<open>term\<close> with term antiquotations,
  for instance \<^theory_text>\<open>@{term_ \<open>@{cenelec-term \<open>FT\<close>}\<close>}\<close> will parse and check
  that \<open>FT\<close> is indeed an instance of the class \<^typ>\<open>cenelec_term\<close>,
\<close>

subsection\<open>A Domain-Specific Ontology: \<^verbatim>\<open>CENELEC_50128\<close>\<close>
(*<*)
ML\<open>val toLaTeX = String.translate (fn c => if c = #"_" then "\\_" else String.implode[c])\<close>     
ML\<open>writeln (DOF_core.print_doc_class_tree 
                 @{context} (fn (n,l) =>  true (*     String.isPrefix "technical_report" l 
                                         orelse String.isPrefix "Isa_COL" l *)) 
                 toLaTeX)\<close>
(*>*)
text\<open> The \<^verbatim>\<open>CENELEC_50128\<close> ontology in \<^theory>\<open>Isabelle_DOF-Ontologies.CENELEC_50128\<close>
is an example of a domain-specific ontology.
It is based on  \<^verbatim>\<open>technical_report\<close> since we assume that this kind of format will be most
appropriate for this type of long-and-tedious documents,

%
\begin{center}
\begin{minipage}{.9\textwidth}\footnotesize
\dirtree{%
.0 .
.1 CENELEC\_50128.judgement\DTcomment{...}.
.1 CENELEC\_50128.test\_item\DTcomment{...}.
.2 CENELEC\_50128.test\_case\DTcomment{...}.
.2 CENELEC\_50128.test\_tool\DTcomment{...}.
.2 CENELEC\_50128.test\_result\DTcomment{...}.
.2 CENELEC\_50128.test\_adm\_role\DTcomment{...}.
.2 CENELEC\_50128.test\_environment\DTcomment{...}.
.2 CENELEC\_50128.test\_requirement\DTcomment{...}.
.2 CENELEC\_50128.test\_specification\DTcomment{...}.
.1 CENELEC\_50128.objectives\DTcomment{...}.
.1 CENELEC\_50128.design\_item\DTcomment{...}.
.2 CENELEC\_50128.interface\DTcomment{...}.
.1 CENELEC\_50128.sub\_requirement\DTcomment{...}.
.1 CENELEC\_50128.test\_documentation\DTcomment{...}.
.1 Isa\_COL.text\_element\DTcomment{...}.
.2 CENELEC\_50128.requirement\DTcomment{...}.
.3 CENELEC\_50128.TC\DTcomment{...}.
.3 CENELEC\_50128.FnI\DTcomment{...}.
.3 CENELEC\_50128.SIR\DTcomment{...}.
.3 CENELEC\_50128.CoAS\DTcomment{...}.
.3 CENELEC\_50128.HtbC\DTcomment{...}.
.3 CENELEC\_50128.SILA\DTcomment{...}.
.3 CENELEC\_50128.assumption\DTcomment{...}.
.4 CENELEC\_50128.AC\DTcomment{...}.
.5 CENELEC\_50128.EC\DTcomment{...}.
.6 CENELEC\_50128.SRAC\DTcomment{...}.
.3 CENELEC\_50128.hypothesis\DTcomment{...}.
.4 CENELEC\_50128.security\_hyp\DTcomment{...}.
.3 CENELEC\_50128.safety\_requirement\DTcomment{...}.
.2 CENELEC\_50128.cenelec\_text\DTcomment{...}.
.3 CENELEC\_50128.SWAS\DTcomment{...}.
.3 [...].
.2 scholarly\_paper.text\_section\DTcomment{...}.
.3 scholarly\_paper.technical\DTcomment{...}.
.4 scholarly\_paper.math\_content\DTcomment{...}.
.5 CENELEC\_50128.semi\_formal\_content\DTcomment{...}.
.1 ...
}
\end{minipage}
\end{center}
\<close>

(* TODO : Rearrange ontology hierarchies. *)

subsubsection\<open>Examples\<close>

text\<open>
The category ``exported constraint (EC)'' is, in the file 
\<^file>\<open>CENELEC_50128.thy\<close> defined as follows:

@{boxed_theory_text [display]\<open>
doc_class requirement = text_element +
   long_name    :: "string option"
   is_concerned :: "role set"
doc_class assumption = requirement +
     assumption_kind :: ass_kind <= informal 
doc_class AC = assumption +
   is_concerned :: "role set" <= "UNIV"
doc_class EC = AC  +
     assumption_kind :: ass_kind <= (*default *) formal
\<close>}
\<close>
text\<open>
We now define the document representations, in the file 
\<^file>\<open>DOF-CENELEC_50128.sty\<close>. Let us assume that we want to 
register the definition of EC's in a dedicated table of contents (\<^boxed_latex>\<open>tos\<close>) 
and use an earlier defined environment \inlineltx|\begin{EC}...\end{EC}| for their graphical 
representation. Note that the \inlineltx|\newisadof{}[]{}|-command requires the 
full-qualified names, \<^eg>, \<^boxed_theory_text>\<open>text.CENELEC_50128.EC\<close> for the document class and 
\<^boxed_theory_text>\<open>CENELEC_50128.requirement.long_name\<close> for the  attribute \<^const>\<open>long_name\<close>, 
inherited from the document class \<^typ>\<open>requirement\<close>. The representation of \<^typ>\<open>EC\<close>'s
can now be defined as follows:
% TODO:
% Explain the text qualifier of the long_name text.CENELEC_50128.EC

\begin{ltx}
\newisadof{text.CENELEC_50128.EC}%
[label=,type=%
,Isa_COL.text_element.level=%
,Isa_COL.text_element.referentiable=%
,Isa_COL.text_element.variants=%
,CENELEC_50128.requirement.is_concerned=%
,CENELEC_50128.requirement.long_name=%
,CENELEC_50128.EC.assumption_kind=][1]{%
\begin{isamarkuptext}%
   \ifthenelse{\equal{\commandkey{CENELEC_50128.requirement.long_name}}{}}{%
      % If long_name is not defined, we only create an entry in the table tos
      % using the auto-generated number of the EC 
      \begin{EC}%
          \addxcontentsline{tos}{chapter}[]{\autoref{\commandkey{label}}}%
    }{%
      % If long_name is defined, we use the long_name as title in the 
      % layout of the EC, in the table "tos" and as index entry. .
      \begin{EC}[\commandkey{CENELEC_50128.requirement.long_name}]%
        \addxcontentsline{toe}{chapter}[]{\autoref{\commandkey{label}}: %
              \commandkey{CENELEC_50128.requirement.long_name}}%
        \DOFindex{EC}{\commandkey{CENELEC_50128.requirement.long_name}}%
    }%
    \label{\commandkey{label}}% we use the label attribute as anchor 
    #1% The main text of the EC
  \end{EC}
\end{isamarkuptext}%
}
\end{ltx}
\<close>
text\<open>
  For example, the @{docitem "ass123"} is mapped to

@{boxed_latex [display]
\<open>\begin{isamarkuptext*}%
[label = {ass122},type = {CENELEC_50128.SRAC}, 
 args={label = {ass122}, type = {CENELEC_50128.SRAC}, 
       CENELEC_50128.EC.assumption_kind = {formal}}
] The overall sampling frequence of the odometer subsystem is therefore 
 14 khz, which includes sampling, computing and result communication 
 times ...
\end{isamarkuptext*}\<close>}

This environment is mapped to a plain \<^LaTeX> command via:
@{boxed_latex [display]
\<open> \NewEnviron{isamarkuptext*}[1][]{\isaDof[env={text},#1]{\BODY}} \<close>}
\<close>
text\<open>
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



(*<<*)  
end 
(*>>*)  
