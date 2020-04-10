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
theory 
    "03_GuidedTour"
  imports 
    "02_Background"
    "Isabelle_DOF.CENELEC_50128"
begin
(*>*)

chapter*[isadof_tour::text_section]\<open>\isadof: A Guided Tour\<close>

text\<open>
  In this chapter, we will give a introduction into using \isadof for users that want to create and 
  maintain documents following an existing document ontology.
\<close>

section*[getting_started::technical]\<open>Getting Started\<close>
text\<open>
As an alternative to installing \isadof{} locally, the latest official release  \isadof is also 
available on \href{https://cloud.docker.com/u/logicalhacking/}{Docker Hub}. Thus, if you have \href{https://www.docker.com}{Docker} installed and 
your installation of Docker supports X11 application, you can start \isadof as follows:

\begin{bash}
ë\prompt{}ë docker run -ti --rm -e DISPLAY=$DISPLAY \
   -v /tmp/.X11-unix:/tmp/.X11-unix \ 
   logicalhacking/isabelle_dof-ë\doflatestversionë_ë\MakeLowercase{\isabellelatestversion}ë \
   isabelle jedit
\end{bash}
\<close>

subsection*[installation::technical]\<open>Installation\<close>
text\<open>
  In this section, we will show how to install \isadof and its pre-requisites: Isabelle and 
  \LaTeX. We assume a basic familiarity with a Linux/Unix-like command line (i.e., a shell). 
\<close>

subsubsection*[prerequisites::technical]\<open>Pre-requisites\<close>
text\<open>
  \isadof has to major pre-requisites: 
  \<^item> \<^bold>\<open>Isabelle\<close>\bindex{Isabelle} (\isabellefullversion). 
    \isadof uses a two-part version system (e.g., 1.0.0/2020), 
    where the first part is the version of \isadof (using semantic versioning) and the second 
    part is the supported version of Isabelle. Thus, the same version of \isadof might be 
    available for different versions of Isabelle. 
  \<^item> \<^bold>\<open>\TeXLive 2019\<close>\bindex{TexLive@\TeXLive} or any other modern 
    \LaTeX-distribution where \pdftex{} supports
    \inlineltx|\expanded| 
    (\url{https://www.texdev.net/2018/12/06/a-new-primitive-expanded}).
\<close>

paragraph\<open>Installing Isabelle\<close>
text\<open>
\enlargethispage{\baselineskip}
  Please download and install the Isabelle \isabelleversion distribution for your operating system 
  from the \href{\isabelleurl}{Isabelle website} (\url{\isabelleurl}). After the successful 
  installation of Isabelle, you should be able to call the \inlinebash|isabelle| tool on the 
  command line:

\begin{bash}
ë\prompt{}ë isabelle version
ë\isabellefullversionë
\end{bash}

Depending on your operating system and depending if you put Isabelle's \inlinebash{bin} directory
in your \inlinebash|PATH|, you will need to invoke \inlinebash|isabelle| using its
full qualified path, \eg:

\begin{bash}
ë\prompt{}ë /usr/local/Isabelleë\isabelleversion/ëbin/isabelle version
ë\isabellefullversionë
\end{bash}
\<close>

paragraph\<open>Installing \TeXLive\<close>
text\<open>
  Modern Linux distribution will allow you to install \TeXLive using their respective package 
  managers. On a modern Debian system or a Debian derivative (\eg, Ubuntu), the following command 
  should install all required \LaTeX{} packages:

\begin{bash}
ë\prompt{}ë sudo aptitude install texlive-latex-extra texlive-fonts-extra
\end{bash}

  Please check that this, indeed, installs a version of \pdftex{} that supports the 
  \inlineltx|\expanded|-primitive. To check your \pdfTeX-binary, execute 

\begin{bash}
ë\prompt{}ë pdftex \\expanded{Success}\\end
This is pdfTeX, Version 3.14159265-2.6-1.40.20 (TeX Live 2019/Debian).
Output written on texput.pdf (1 page, 8650 bytes).
Transcript written on texput.log.
\end{bash}

  If this generates successfully a file \inlinebash|texput.pdf|, your \pdftex-binary supports
  the \inlineltx|\expanded|-primitive. If your Linux distribution does not (yet) ship \TeXLive{} 
  2019 or your are running Windows or OS X, please follow the installation instructions from \url{https://www.tug.org/texlive/acquire-netinstall.html}. 
\<close>

subsubsection*[isadof::technical]\<open>Installing \isadof\<close>
text\<open>
  In the following, we assume that you already downloaded the \isadof distribution 
  (\href{\isadofarchiveurl}{\isadofarchiven}) from the \isadof web site. The main steps for 
  installing are extracting the \isadof distribution and calling its \inlinebash|install| script. 
  We start by extracting the \isadof archive:

\begin{bash}
ë\prompt{}ë tar xf ë\href{\isadofarchiveurl}{\isadofarchiven}ë
\end{bash}
This will create a directory \texttt{\isadofdirn} containing \isadof distribution.
Next, we need to invoke the \inlinebash|install| script. If necessary, the installations 
automatically downloads additional dependencies from the AFP (\url{https://www.isa-afp.org}), 
namely the AFP  entries ``Functional Automata''~@{cite "nipkow.ea:functional-Automata-afp:2004"} and ``Regular 
Sets and Expressions''~@{cite "kraus.ea:regular-sets-afp:2010"}. This might take a few minutes to complete. 
Moreover, the installation script applies a patch to the Isabelle system, which requires 
\<^emph>\<open>write permissions for the Isabelle system directory\<close> and registers \isadof as Isabelle component. 

If the \inlinebash|isabelle| tool is not in your \inlinebash|PATH|, you need to call the 
\inlinebash|install| script with the \inlinebash|--isabelle| option, passing the full-qualified
path of the \inlinebash|isabelle| tool (\inlinebash|install --help| gives 
you an overview of all available configuration options):

\begin{bash}
ë\prompt{}ë cd ë\isadofdirnë
ë\prompt{\isadofdirn}ë ./install --isabelle /usr/local/Isabelleë\isabelleversion/bin/isabelleë

Isabelle/DOF Installer
======================
* Checking Isabelle version:
  Success: found supported Isabelle version ë(\isabellefullversion)ë
* Checking (La)TeX installation:
  Success: pdftex supports \expanded{} primitive.
* Check availability of Isabelle/DOF patch:
  Warning: Isabelle/DOF patch is not available or outdated.
           Trying to patch system ....
       Applied patch successfully, Isabelle/HOL will be rebuilt during
       the next start of Isabelle.
* Checking availability of AFP entries:
  Warning: could not find AFP entry Regular-Sets.
  Warning: could not find AFP entry Functional-Automata.
           Trying to install AFP (this might take a few *minutes*) ....
           Registering Regular-Sets iëën 
                 /home/achim/.isabelle/Isabelleë\isabelleversion/ROOTSë
           Registering Functional-Automata iëën 
                 /home/achim/.isabelle/Isabelleë\isabelleversion/ROOTSë
           AFP installation successful.
* Searching fëëor existing installation:
  No old installation found.
* Installing Isabelle/DOF
  - Installing Tools iëën 
        /home/achim/.isabelle/Isabelleë\isabelleversion/DOF/Toolsë
  - Installing document templates iëën 
        /home/achim/.isabelle/Isabelleë\isabelleversion/DOF/document-templateë
  - Installing LaTeX styles iëën 
       /home/achim/.isabelle/Isabelleë\isabelleversion/DOF/latexë
  - Registering Isabelle/DOF
    * Registering tools iëën 
       /home/achim/.isabelle/Isabelleë\isabelleversion/etc/settingsë
* Installation successful. Enjoy Isabelle/DOF, you can build the session
  Isabelle/DOF and all example documents by executing:
  /usr/local/Isabelleë\isabelleversion/bin/isabelleë build -D .
\end{bash}

After the successful installation, you can now explore the examples (in the sub-directory 
\inlinebash|examples| or create your own project. On the first start, the session 
\inlinebash|Isabelle_DOF| will be built automatically. If you want to pre-build this 
session and all example documents, execute:

\begin{bash}
ë\prompt{\isadofdirn}ë isabelle build -D . 
\end{bash}
\<close>

subsection*[first_project::technical]\<open>Creating an \isadof Project\<close>
text\<open>
  \isadof provides its own variant of Isabelle's 
  \inlinebash|mkroot| tool, called \inlinebash|mkroot_DOF|:\index{mkroot\_DOF}

\begin{bash} 
ë\prompt{}ë isabelle mkroot_DOF -h 

Usage: isabelle mkroot_DOF [OPTIONS] [DIR]

  Options are:
    -h           print this hëëelp text and exëëit
    -n NAME      alternative session name (default: DIR base name)
    -o ONTOLOGY  (default: scholarly_paper)
       Available ontologies:
       * CENELEC_50128
       * math_exam
       * scholarly_paper
       * technical_report
    -t TEMPLATE   (default: scrartcl)
       Available document templates:
       * lncs
       * scrartcl
       * scrreprt-modern
       * scrreprt

  Prepare session root DIR (default: current directory).
\end{bash} 

  Creating a new document setup requires two decisions:
  \<^item> which ontologies (\eg, scholarly\_paper) are required and 
  \<^item> which document template (layout)\index{document template} should be used 
    (\eg, scrartcl\index{scrartcl}). Some templates (\eg, lncs) require that the users manually 
    obtains and adds the necessary \LaTeX class file (\eg, \inlinebash|llncs.cls|. 
    This is mostly due to licensing restrictions.
\<close>
text\<open>
  If you are happy with the defaults, \ie, using the ontology for writing academic papers 
  (scholarly\_paper) using a report layout based on the article class (\inlineltx|scrartcl|) of 
  the KOMA-Script bundle~@{cite "kohm:koma-script:2019"}, you can create your first project 
  \inlinebash|myproject| as follows:

\begin{bash}
ë\prompt{}ë isabelle mkroot_DOF myproject

Preparing session "myproject" iëën "myproject"
  creating "myproject/ROOT"
  creating "myproject/document/root.tex"

Now use the following coëëmmand line to build the session:
  isabelle build -D myproject
\end{bash}

  This creates a directory \inlinebash|myproject| containing the \isadof-setup for your 
  new document. To check the document formally, including the generation of the document in PDF,
  you only need to execute

\begin{bash}
ë\prompt{}ë  isabelle build -d . myproject
\end{bash}

This will create the directory \inlinebash|myproject|: 
\begin{center}
\begin{minipage}{.9\textwidth}
\dirtree{%
.1 .
.2 myproject.
.3 document.
.4 build\DTcomment{Build Script}.
.4 isadof.cfg\DTcomment{\isadof configuraiton}.
.4 preamble.tex\DTcomment{Manual \LaTeX-configuration}.
.3 ROOT\DTcomment{Isabelle build-configuration}.
}
\end{minipage}
\end{center}
The \isadof configuration (\inlinebash|isadof.cfg|) specifies the required
ontologies and the document template using a YAML syntax.\<^footnote>\<open>Isabelle power users will recognize that 
\isadof's document setup does not make use of a file \inlinebash|root.tex|: this file is 
replaced by built-in document templates.\<close> The main two configuration files for 
users are:
\<^item> The file \inlinebash|ROOT|\index{ROOT}, which defines the Isabelle session. New theory files as well as new 
  files required by the document generation (\eg, images, bibliography database using \BibTeX, local
  \LaTeX-styles) need to be registered in this file. For details of Isabelle's build system, please 
  consult the Isabelle System Manual~@{cite "wenzel:system-manual:2020"}.
\<^item> The file \inlinebash|praemble.tex|\index{praemble.tex}, which allows users to add additional 
  \LaTeX-packages or to add/modify \LaTeX-commands. 
\<close>

section*[scholar_onto::example]\<open>Writing Academic Publications (scholarly\_paper)\<close>  
subsection\<open>The Scholarly Paper Example\<close>
text\<open> 
  The ontology ``scholarly\_paper''\index{ontology!scholarly\_paper} is a small ontology modeling 
  academic/scientific papers. In this \isadof application scenario, we deliberately refrain from 
  integrating references to (Isabelle) formal content in order  demonstrate that \isadof is not a 
  framework from Isabelle users to Isabelle users only. Of course, such references can be added 
  easily and represent a particular strength of \isadof.

  The \isadof distribution contains an example (actually, our CICM 2018 
  paper~@{cite "brucker.ea:isabelle-ontologies:2018"}) using the ontology ``scholarly\_paper'' in 
  the directory \nolinkurl{examples/scholarly_paper/2018-cicm-isabelle_dof-applications/}. You 
  can inspect/edit the example in Isabelle's IDE, by either 
  \<^item> starting Isabelle/jedit using your graphical user interface (\eg, by clicking on the 
    Isabelle-Icon provided by the Isabelle installation) and loading the file 
    \nolinkurl{examples/scholarly_paper/2018-cicm-isabelle_dof-applications/IsaDofApplications.thy}.
  \<^item> starting Isabelle/jedit from the command line by calling:

    \begin{bash}
ë\prompt{\isadofdirn}ë 
  isabelle jedit examples/scholarly_paper/2018-cicm-isabelle_dof-applications/\
  IsaDofApplications.thy
\end{bash}
\<close> 
text\<open>  
  You can build the PDF-document by calling:

  \begin{bash}
ë\prompt{}ë isabelle build \
2018-cicm-isabelle_dof-applications                                                   
\end{bash}
\<close>


subsection\<open>Modeling Academic Publications\<close>
text\<open>
  We start by modeling the usual text-elements of an academic paper: the title and author 
  information, abstract, and text section: 

\begin{isar}
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
\end{isar}

  The attributes \inlineisar+short_title+, \inlineisar+abbrev+ etc are introduced with their types as 
  well as their default values. Our model prescribes an optional \inlineisar+main_author+ and a 
  todo-list attached to an arbitrary text section; since instances of this class are mutable 
  (meta)-objects of text-elements, they can be modified arbitrarily through subsequent text and of 
  course globally during text evolution. Since \inlineisar+author+ is a HOL-type internally generated 
  by \isadof framework and can therefore appear in the \inlineisar+main_author+ attribute of the 
  \inlineisar+text_section+ class; semantic links between concepts can be modeled this way.
\<close>

figure*[fig1::figure,spawn_columns=False,relative_width="95",src="''figures/Dogfood-Intro''"]
       \<open> Ouroboros I: This paper from inside \ldots \<close>  

text\<open> 
  @{docitem \<open>fig1\<close>} shows the corresponding view in the Isabelle/jedit of the start of an academic 
  paper. The text uses \isadof's own text-commands containing the meta-information provided by the 
  underlying ontology. We proceed by a definition of \inlineisar+introduction+'s, which we define 
  as the extension of \inlineisar+text_section+ which is intended to capture common infrastructure:

\begin{isar}
doc_class introduction = text_section +
   comment :: string
\end{isar}

  As a consequence of the definition as extension, the \inlineisar+introduction+ class
  inherits the attributes \inlineisar+main_author+ and \inlineisar+todo_list+ together with 
  the corresponding default values.

  We proceed more or less conventionally by the subsequent sections:

\begin{isar}
doc_class technical = text_section +
   definition_list :: "string list" <=  "[]"

doc_class example   = text_section +
   comment :: string

doc_class conclusion = text_section +
   main_author :: "author option"  <=  None
   
doc_class related_work = conclusion +
   main_author :: "author option"  <=  None

\end{isar}

Moreover, we model a document class for including figures (actually, this document class is already 
defined in the core ontology of \isadof):

\begin{isar}
datatype placement = h | t | b | ht | hb   
doc_class figure   = text_section +
   relative_width  :: "int" (* percent of textwidth *)    
   src             :: "string"
   placement       :: placement 
   spawn_columns   :: bool <= True 
\end{isar}
\<close>
figure*[fig_figures::figure,spawn_columns=False,relative_width="85",src="''figures/Dogfood-figures''"]
       \<open> Ouroboros II: figures \ldots \<close>

text\<open> 
  The document class \inlineisar+figure+ (supported by the \isadof command \inlineisar+figure*+) 
  makes it possible to express the pictures and diagrams such as @{docitem \<open>fig_figures\<close>}.

  Finally, we define a monitor class definition that enforces a textual ordering
  in the document core by a regular expression:

\begin{isar}
doc_class article = 
   style_id :: string                <= "''LNCS''"
   version  :: "(int \<times> int \<times> int)"  <= "(0,0,0)"
   where "(title       ~~ \<lbrakk>subtitle\<rbrakk>   ~~ \<lbrace>author\<rbrace>$^+$+  ~~  abstract    ~~
             introduction ~~  \<lbrace>technical || example\<rbrace>$^+$  ~~  conclusion ~~  
             bibliography)"
\end{isar}
\<close>

subsection*[scholar_pide::example]\<open>Editing Support for Academic Papers\<close>
side_by_side_figure*[exploring::side_by_side_figure,anchor="''fig-Dogfood-II-bgnd1''",
                      caption="''Exploring a reference of a text-element.''",relative_width="48",
                      src="''figures/Dogfood-II-bgnd1''",anchor2="''fig-bgnd-text_section''",
                      caption2="''Exploring the class of a text element.''",relative_width2="47",
                      src2="''figures/Dogfood-III-bgnd-text_section''"]\<open>Exploring text elements.\<close>


side_by_side_figure*["hyperlinks"::side_by_side_figure,anchor="''fig:Dogfood-IV-jumpInDocCLass''",
                      caption="''Hyperlink to class-definition.''",relative_width="48",
                      src="''figures/Dogfood-IV-jumpInDocCLass''",anchor2="''fig:Dogfood-V-attribute''",
                      caption2="''Exploring an attribute.''",relative_width2="47",
                      src2="''figures/Dogfood-III-bgnd-text_section''"]\<open> Hyperlinks.\<close>
text\<open> 
  From these class definitions, \isadof also automatically generated editing 
  support for Isabelle/jedit. In \autoref{fig-Dogfood-II-bgnd1} and 
  \autoref{fig-bgnd-text_section} we show how hovering over links permits to explore its 
  meta-information. Clicking on a document class identifier permits to hyperlink into the 
  corresponding class definition (\autoref{fig:Dogfood-IV-jumpInDocCLass}); hovering over an 
  attribute-definition (which is qualified in order to disambiguate; 
  \autoref{fig:Dogfood-V-attribute}).
\<close>
figure*[figDogfoodVIlinkappl::figure,relative_width="80",src="''figures/Dogfood-V-attribute''"]
       \<open> Exploring an attribute (hyperlinked to the class). \<close> 

text\<open> 
  An ontological reference application in @{docitem "figDogfoodVIlinkappl"}: the 
  ontology-dependant antiquotation \inlineisar|@ {example ...}| refers to the corresponding 
  text-elements. Hovering allows for inspection, clicking for jumping to the definition.  If the 
  link does not exist or  has a non-compatible type, the text is not validated.
\<close>

section*[cenelec_onto::example]\<open>Writing Certification Documents (CENELEC\_50128)\<close>
subsection\<open>The CENELEC 50128 Example\<close>
text\<open> 
  The ontology ``CENELEC\_50128''\index{ontology!CENELEC\_50128} is a small ontology modeling 
  documents for a certification following CENELEC 50128~@{cite "boulanger:cenelec-50128:2015"}.
  The \isadof distribution contains a small example  using the ontology ``CENELEC\_50128'' in 
  the directory \nolinkurl{examples/CENELEC_50128/mini_odo/}. You can inspect/edit the example 
  in Isabelle's IDE, by either 
  \<^item> starting Isabelle/jedit using your graphical user interface (\eg, by clicking on the 
    Isabelle-Icon provided by the Isabelle installation) and loading the file 
    \nolinkurl{examples/CENELEC_50128/mini_odo/mini_odo.thy}.
  \<^item> starting Isabelle/jedit from the command line by calling:

    \begin{bash}
ë\prompt{\isadofdirn}ë 
  isabelle jedit examples/CENELEC_50128/mini_odo/mini_odo.thy
\end{bash}
\<close> 
text\<open>  
  You can build the PDF-document by calling:

  \begin{bash}
ë\prompt{}ë isabelle build mini_odo
\end{bash}
\<close>
 
subsection\<open>Modeling CENELEC 50128\<close>
text\<open>
  Documents to be provided in formal certifications (such as CENELEC 
  50128~@{cite "boulanger:cenelec-50128:2015"} or Common Criteria~@{cite "cc:cc-part3:2006"}) can 
  much profit from the control of ontological consistency:  a lot of an evaluators work consists in 
  tracing down the links from requirements over assumptions down to elements of evidence, be it in 
  the models, the code, or the tests.  In a certification process, traceability becomes a major 
  concern; and providing mechanisms to ensure complete traceability already at the development of 
  the global document will clearly increase speed and reduce risk and cost of a certification 
  process. Making the link-structure machine-checkable, be it between requirements, assumptions, 
  their implementation and their discharge by evidence (be it tests, proofs, or authoritative 
  arguments), is therefore natural and has the potential to decrease the cost of developments 
  targeting certifications. Continuously checking the links between the formal and the semi-formal 
  parts of such documents is particularly valuable during the (usually collaborative) development 
  effort. 

  As in many other cases, formal certification documents come with an own terminology and pragmatics
  of what has to be demonstrated and where, and how the trace-ability of requirements through 
  design-models over code to system environment assumptions has to be assured.  

  In the sequel, we present a simplified version of an ontological model used in a 
  case-study~@{cite "bezzecchi.ea:making:2018"}. We start with an introduction of the concept of 
  requirement:

\begin{isar}
doc_class requirement = long_name :: "string option"

doc_class requirement_analysis = no :: "nat"
   where "requirement_item +"

doc_class hypothesis = requirement +
      hyp_type :: hyp_type <= physical  (* default *)
  
datatype ass_kind = informal | semiformal | formal
  
doc_class assumption = requirement +
     assumption_kind :: ass_kind <= informal 
\end{isar}

Such ontologies can be enriched by larger explanations and examples, which may help
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
\begin{isar}  
doc_class ec = assumption  +
     assumption_kind :: ass_kind <= (*default *) formal
                        
doc_class srac = ec  +
     assumption_kind :: ass_kind <= (*default *) formal
\end{isar}

We now can, \eg, write 

\begin{isar}
text*[ass123::SRAC]\<Open> 
  The overall sampling frequence of the odometer subsystem is therefore 
  14 khz, which includes sampling, computing a$$nd result communication 
  times \ldots
\<Close>
\end{isar}

This will be shown in the PDF as follows:
\<close>
text*[ass123::SRAC] \<open> The overall sampling frequence of the odometer
subsystem is therefore 14 khz, which includes sampling, computing and
result communication times \ldots \<close>

subsection*[ontopide::technical]\<open>Editing Support for CENELEC 50128\<close>  
figure*[figfig3::figure,relative_width="95",src="''figures/antiquotations-PIDE''"]
\<open> Standard antiquotations referring to theory elements.\<close>
text\<open> The corresponding view in @{docitem  \<open>figfig3\<close>} shows core part of a document 
conformimg to the CENELEC 50128 ontology. The first sample shows standard Isabelle antiquotations 
@{cite "wenzel:isabelle-isar:2020"} into formal entities of a theory. This way, the informal parts 
of a document get ``formal content'' and become more robust under change.\<close>

figure*[figfig5::figure, relative_width="95", src="''figures/srac-definition''"]
        \<open> Defining a SRAC reference \ldots \<close>
figure*[figfig7::figure, relative_width="95", src="''figures/srac-as-es-application''"]
        \<open> Using a SRAC as EC document reference. \<close>
text\<open> The subsequent sample in @{docitem \<open>figfig5\<close>} shows the definition of an
\<^emph>\<open>safety-related application condition\<close>, a side-condition of a theorem which 
has the consequence that a certain calculation must be executed sufficiently fast on an embedded 
device. This condition can not be established inside the formal theory but has to be 
checked by system integration tests. Now we reference in @{docitem  \<open>figfig7\<close>} this 
safety-related condition; however, this happens in a context where general \<^emph>\<open>exported constraints\<close> 
are listed. \isadof's checks establish that this is legal in the given ontology. 
\<close>    

section*[math_exam::example]\<open>Writing Exams (math\_exam)\<close> 
subsection\<open>The Math Exam Example\<close>
text\<open> 
  The ontology ``math\_exam''\index{ontology!math\_exam} is an experimental ontology modeling 
  the process of writing exams at higher education institution in the United Kingdom, where exams 
  undergo both an internal and external review process. The \isadof distribution contains a tiny 
  example  using the ontology ``math\_exam'' in the directory 
  \nolinkurl{examples/math_exam/MathExam/}. You can inspect/edit the example 
  in Isabelle's IDE, by either 
  \<^item> starting Isabelle/jedit using your graphical user interface (\eg, by clicking on the 
    Isabelle-Icon provided by the Isabelle installation) and loading the file 
    \nolinkurl{examples/math_exam/MathExam/MathExam.thy}.
  \<^item> starting Isabelle/jedit from the command line by calling:

    \begin{bash}
ë\prompt{\isadofdirn}ë 
  isabelle jedit examples/math_exam/MathExam/MathExam.thy
\end{bash}
\<close> 
text\<open>  
  You can build the PDF-document by calling:

  \begin{bash}
ë\prompt{}ë isabelle build MathExam
\end{bash}
\<close>
 
subsection\<open>Modeling Exams\<close>
text\<open>
  The math-exam scenario is an application with mixed formal and semi-formal content. It addresses 
  applications where the author of the exam is not present  during the exam and the preparation 
  requires a very rigorous process.

  We assume that the content has four different types of addressees, which have a different
  \<^emph>\<open>view\<close> on the integrated document: 
  \<^item> the \<^emph>\<open>setter\<close>, \ie, the author of the exam,
  \<^item> the \<^emph>\<open>checker\<close>, \ie, an internal person that checks 
   the exam for feasibility and non-ambiguity, 
  \<^item> the \<^emph>\<open>external\<close>, \ie, an external person that checks 
    the exam for feasibility and non-ambiguity, and 
  \<^item> the \<^emph>\<open>student\<close>, \ie, the addressee of the exam. 
\<close>
text\<open> 
  The latter quality assurance mechanism is used in many universities,
  where for organizational reasons the execution of an exam takes place in facilities
  where the author of the exam is not expected to be physically present.
  Furthermore, we assume a simple grade system (thus, some calculation is required). We 
  can model this as follows: 

\begin{isar}
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
doc_class Exam_item =  concerns :: "ContentClass set"  
doc_class Exam_item =  concerns :: "ContentClass set"  

type_synonym SubQuestion = string
\end{isar}

  The heart of this ontology is an alternation of questions and answers, where the answers can 
  consist of simple yes-no answers or lists of formulas. Since we do not assume familiarity of 
  the students with Isabelle (\inlineisar+term+ would assume that this is a parse-able and 
  type-checkable entity), we basically model a derivation as a sequence of strings:

\begin{isar}
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
\end{isar}

In many institutions, having a rigorous process of validation for exam subjects makes sense: is 
the initial question correct? Is a proof in the sense of the question possible? We model the 
possibility that the @{term examiner} validates a question by a sample proof validated by Isabelle:

\begin{isar}
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
\end{isar}

In our scenario this sample proofs are completely \<^emph>\<open>intern\<close>, \ie, not exposed to the 
students but just additional material for the internal review process of the exam.
\<close>


section\<open>Style Guide\<close>
text\<open>
  The document generation process of \isadof is based on Isabelle's document generation framework, 
  using \LaTeX{} as the underlying back-end. As Isabelle's document generation framework, it is 
  possible to embed (nearly) arbitrary \LaTeX-commands in text-commands, \eg:

\begin{isar}
text\<Open> This is \emph{emphasized} a$$nd this is a 
       citation~\cite{brucker.ea:isabelle-ontologies:2018}\<Close>
\end{isar}

  In general, we advise against this practice and, whenever positive, use the \isadof (respetively
  Isabelle) provided alternatives:

\begin{isar}
text\<Open> This is *\<Open>emphasized\<Close> a$$nd this is a 
        citation <@>{cite "brucker.ea:isabelle-ontologies:2018"}.\<Close>
\end{isar}

Clearly, this is not always possible and, in fact, often \isadof documents will contain 
\LaTeX-commands, this should be restricted to layout improvements that otherwise are (currently)
not possible. As far as possible, the use of \LaTeX-commands should be restricted to the definition 
of ontologies and document templates (see @{docitem (unchecked) \<open>isadof_ontologies\<close>}).

Restricting the use of \LaTeX has two advantages: first, \LaTeX commands can circumvent the 
consistency checks of \isadof and, hence, only if no \LaTeX commands are used, \isadof can 
ensure that a document that does not generate any error messages in Isabelle/jedit also generated
a PDF document. Second, future version of \isadof might support different targets for the 
document generation (\eg, HTML) which, naturally, are only available to documents not using 
native \LaTeX-commands. 

Similarly, (unchecked) forward references should, if possible, be avoided, as they also might
create dangeling references during the document generation that break the document generation.  

Finally, we recommend to use the @{command "check_doc_global"} command at the end of your 
document to check the global reference structure. 

\<close>

(*<*)
end
(*>*) 
  
