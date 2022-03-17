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
theory 
    "03_GuidedTour" 
  imports 
    "02_Background"
    "Isabelle_DOF.technical_report"
    "Isabelle_DOF.CENELEC_50128"
begin
(*>*)

chapter*[isadof_tour::text_section]\<open>\<^isadof>: A Guided Tour\<close>

text\<open>
  In this chapter, we will give an introduction into using \<^isadof> for users that want to create and 
  maintain documents following an existing document ontology.
\<close>

section*[getting_started::technical]\<open>Getting Started\<close>
text\<open>
As an alternative to installing \<^isadof>{} locally, the latest official release of \<^isadof> is also 
available on \href{https://cloud.docker.com/u/logicalhacking/}{Docker Hub}. Thus, if you have 
\href{https://www.docker.com}{Docker} installed and 
your installation of Docker supports X11 application, you can start \<^isadof> as follows:

@{boxed_bash [display] \<open>ë\prompt{}ë docker run -ti --rm -e DISPLAY=$DISPLAY \
   -v /tmp/.X11-unix:/tmp/.X11-unix \ 
   logicalhacking/isabelle_dof-ë\doflatestversionë_ë\MakeLowercase{\isabellelatestversion}ë \
   isabelle jedit\<close>}
\<close>

subsection*[installation::technical]\<open>Installation\<close>
text\<open>
  In this section, we will show how to install \<^isadof> and its pre-requisites: Isabelle and 
  \<^LaTeX>. We assume a basic familiarity with a Linux/Unix-like command line (i.e., a shell). 

  \<^isadof> requires Isabelle\<^bindex>\<open>Isabelle\<close> (\isabellefullversion) with a recent \<^LaTeX>-distribution
  (e.g., Tex Live 2021 or later).    
  \<^isadof> uses a two-part version system (e.g., 1.1.0/Isabelle2021),  where the first part is the version
  of \<^isadof> (using semantic versioning) and the second part is the supported version of Isabelle. 
  Thus, the same version of \<^isadof> might be available for different versions of Isabelle. 
\<close>

paragraph\<open>Installing Isabelle.\<close>
text\<open>
  Please download and install Isabelle (version: \isabelleversion) from the 
  \href{\isabelleurl}{Isabelle website} (\url{\isabelleurl}). After the 
  successful installation of Isabelle, you should be able to call the \<^boxed_bash>\<open>isabelle\<close> 
  tool on the command line:
@{boxed_bash [display]\<open>ë\prompt{}ë isabelle version
ë\isabellefullversionë\<close>}

Depending on your operating system and depending if you put Isabelle's  \<^boxed_bash>\<open>bin\<close> directory
in your  \<^boxed_bash>\<open>PATH\<close>, you will need to invoke  \<^boxed_bash>\<open>isabelle\<close> using its
full qualified path, \<^eg>:
@{boxed_bash [display]\<open>ë\prompt{}ë /usr/local/Isabelleë\isabelleversionë/bin/isabelle version
ë\isabellefullversionë\<close>}
\<close>

paragraph\<open>Installing \<^TeXLive>.\<close>
text\<open>
  Modern Linux distribution will allow you to install \<^TeXLive> using their respective package 
  managers. On a modern Debian system or a Debian derivative (\<^eg>, Ubuntu), the following command 
  should install all required \<^LaTeX> packages:
@{boxed_bash [display]\<open>ë\prompt{}ë sudo aptitude install texlive-latex-extra texlive-fonts-extra\<close>}
\<close>

subsubsection*[isadof::technical]\<open>Installing \<^isadof>\<close>
text\<open>
  In the following, we assume that you already downloaded the \<^isadof> distribution 
  (\href{\isadofarchiveurl}{\isadofarchiven}) from the \<^isadof> web site. The main steps for 
  installing are extracting the \<^isadof> distribution and calling its \<^boxed_bash>\<open>install\<close> script. 
  We start by extracting the \<^isadof> archive:
@{boxed_bash [display]\<open>ë\prompt{}ë tar xf ë\href{\isadofarchiveurl}{\isadofarchiven}ë\<close>}
This will create a directory \texttt{\isadofdirn} containing \<^isadof> distribution.
Next, we need to invoke the \<^boxed_bash>\<open>install\<close> script. If necessary, the installation 
automatically downloads additional dependencies from the AFP (\<^url>\<open>https://www.isa-afp.org\<close>), 
namely the AFP  entries ``Functional Automata''~@{cite "nipkow.ea:functional-Automata-afp:2004"} 
and ``Regular Sets and Expressions''~@{cite "kraus.ea:regular-sets-afp:2010"}. This might take a 
few minutes to complete. Moreover, the installation script applies a patch to the Isabelle system, 
which requires  \<^emph>\<open>write permissions for the Isabelle system directory\<close> and registers \<^isadof> as 
Isabelle component. 

If the \<^boxed_bash>\<open>isabelle\<close> tool is not in your  \<^boxed_bash>\<open>PATH\<close>, you need to call the 
 \<^boxed_bash>\<open>install\<close> script with the  \<^boxed_bash>\<open>--isabelle\<close> option, passing the full-qualified
path of the \<^boxed_bash>\<open>isabelle\<close> tool ( \<^boxed_bash>\<open>install --help\<close> gives 
you an overview of all available configuration options):

@{boxed_bash [display]\<open>ë\prompt{}ë cd ë\isadofdirnë
ë\prompt{\isadofdirn}ë ./install --isabelle /usr/local/Isabelleë\isabelleversion/bin/isabelleë

Isabelle/DOF Installer
======================
* Checking Isabelle version:
  Success: found supported Isabelle version ë(\isabellefullversion)ë
* Check availability of Isabelle/DOF patch:
  Warning: Isabelle/DOF patch is not available or outdated.
           Trying to patch system ....
       Applied patch successfully, Isabelle/HOL will be rebuilt during
       the next start of Isabelle.
* Checking availability of AFP entries:\<close>}

@{boxed_bash [display]
\<open>ëë     Warning: could not find AFP entry Regular-Sets.
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
  /usr/local/Isabelleë\isabelleversion/bin/isabelleë build -D . \<close>}

After the successful installation, you can explore the examples (in the sub-directory 
\<^boxed_bash>\<open>examples\<close>) or create your own project. On the first start, the session 
\<^boxed_bash>\<open>Isabelle_DOF\<close> will be built automatically. If you want to pre-build this 
session and all example documents, execute:
@{boxed_bash [display]\<open>ë\prompt{\isadofdirn}ë isabelle build -D . \<close>} 
\<close>

subsection*[first_project::technical]\<open>Creating an \<^isadof> Project\<close>
text\<open>
  \<^isadof> provides its own variant of Isabelle's 
  \<^boxed_bash>\<open>mkroot\<close> tool, called \<^boxed_bash>\<open>mkroot_DOF\<close>\index{mkroot\_DOF}:
@{boxed_bash [display]\<open>ë\prompt{}ë isabelle mkroot_DOF myproject

Preparing session "myproject" iëën "myproject"
  creating "myproject/ROOT"
  creating "myproject/document/root.tex"

Now use the following coëëmmand line to build the session:
  isabelle build -D myproject \<close>}
  The created project uses the default configuration (the ontology for writing academic papers 
  (scholarly\_paper) using a report layout based on the article class (\<^boxed_latex>\<open>scrartcl\<close>) of 
  the KOMA-Script bundle~@{cite "kohm:koma-script:2019"}). The directory \<^boxed_bash>\<open>myproject\<close> 
  contains the \<^isadof>-setup for your  new document. To check the document formally, including the 
  generation of the document in PDF, you only need to execute

@{boxed_bash [display]\<open>ë\prompt{myproject}ë  isabelle build -d . myproject \<close>}

The directory  \<^boxed_bash>\<open>myproject\<close> contains the following files and directories: 
\begin{center}
\begin{minipage}{.9\textwidth}
\dirtree{%
.1 .
.2 myproject.
.3 document.
.4 build\DTcomment{Build Script}.
.4 isadof.cfg\DTcomment{\<^isadof> configuration}.
.4 preamble.tex\DTcomment{Manual \<^LaTeX>-configuration}.
.3 ROOT\DTcomment{Isabelle build-configuration}.
}
\end{minipage}
\end{center}
The \<^isadof> configuration (\<^boxed_bash>\<open>isadof.cfg\<close>) specifies the required
ontologies and the document template using a YAML syntax.\<^footnote>\<open>Isabelle power users will recognize that 
\<^isadof>'s document setup does not make use of a file \<^boxed_bash>\<open>root.tex\<close>: this file is 
replaced by built-in document templates.\<close> The main two configuration files for 
users are:
\<^item> The file \<^boxed_bash>\<open>ROOT\<close>\<^index>\<open>ROOT\<close>, which defines the Isabelle session. New theory files as well as new 
  files required by the document generation (\<^eg>, images, bibliography database using \<^BibTeX>, local
  \<^LaTeX>-styles) need to be registered in this file. For details of Isabelle's build system, please 
  consult the Isabelle System Manual~@{cite "wenzel:system-manual:2020"}.
\<^item> The file \<^boxed_bash>\<open>preamble.tex\<close>\<^index>\<open>preamble.tex\<close>, which allows users to add additional 
  \<^LaTeX>-packages or to add/modify \<^LaTeX>-commands. 
\<close>

text\<open>
  Creating a new document setup requires two decisions:
  \<^item> which ontologies (\<^eg>, scholarly\_paper) are required, and 
  \<^item> which document template (layout)\index{document template} should be used 
    (\<^eg>, scrartcl\index{scrartcl}). Some templates require that the users manually 
    obtains and adds the necessary \<^LaTeX> class file. 
    This is due to licensing restrictions).\<close>
text\<open> 
  This can be configured by using the command-line options of \<^boxed_bash>\<open>mkroot_DOF\<close>. In 
  Particular, \<^boxed_bash>\<open>-o\<close> allows selecting the ontology and \<^boxed_bash>\<open>-t\<close> allows selecting 
  the document template. The built-in help (using  \<^boxed_bash>\<open>-h\<close>) shows all available options 
  as well as a complete list of the available document templates and ontologies: 

  @{boxed_bash [display]\<open>ë\prompt{}ë isabelle mkroot_DOF -h

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

  Prepare session root DIR (default: current directory). \<close>}

\<close>

section*[scholar_onto::example]\<open>Writing Academic Publications in \<^boxed_theory_text>\<open>scholarly_paper\<close>\<close>  
subsection\<open>Writing Academic Papers\<close>
text\<open> 
  The ontology \<^boxed_theory_text>\<open>scholarly_paper\<close>
  \<^index>\<open>ontology!scholarly\_paper\<close> is an ontology modeling 
  academic/scientific papers, with a slight bias towards texts in the domain of mathematics and engineering. 
  We explain first the principles of its underlying ontology, and then we present two ``real'' 
  examples from our own publication practice.
\<close>
text\<open>
  \<^enum> The iFM 2020 paper~@{cite "taha.ea:philosophers:2020"} is a typical mathematical text,
    heavy in definitions with complex  mathematical notation and a lot of non-trivial cross-referencing
    between statements, definitions and proofs which are ontologically tracked. However, wrt.
    the possible linking between the underlying formal theory and this mathematical presentation,
    it follows a pragmatic path without any ``deep'' linking to types, terms and theorems, 
    deliberately not exploiting \<^isadof> 's full potential with this regard.
  \<^enum> In the CICM 2018 paper~@{cite "brucker.ea:isabelle-ontologies:2018"}, we deliberately
    refrain from integrating references to formal content in order to demonstrate that \<^isadof> is not 
    a  framework from Isabelle users to Isabelle users only, but people just avoiding as much as
    possible \<^LaTeX> notation.

  The \<^isadof> distribution contains both examples using the ontology \<^verbatim>\<open>scholarly_paper\<close> in 
  the directory \nolinkurl{examples/scholarly_paper/2018-cicm-isabelle_dof-applications/} or
  \nolinkurl{examples/scholarly_paper/2020-iFM-CSP}.

  You can inspect/edit the example in Isabelle's IDE, by either 
  \<^item> starting Isabelle/jEdit using your graphical user interface (\<^eg>, by clicking on the 
    Isabelle-Icon provided by the Isabelle installation) and loading the file 
    \nolinkurl{examples/scholarly_paper/2018-cicm-isabelle_dof-applications/IsaDofApplications.thy},
  \<^item> starting Isabelle/jEdit from the command line by, \<^eg>, calling:

@{boxed_bash [display]\<open>ë\prompt{\isadofdirn}ë 
  isabelle jedit -d . examples/scholarly_paper/2020-iFM-CSP/paper.thy \<close>}
\<close> 


text\<open>    You can build the PDF-document at the command line by calling:
@{boxed_bash [display] \<open>ë\prompt{}ë isabelle build -d . 2020-iFM-csp \<close>}
\<close>

subsection*[sss::technical]\<open>A Bluffers Guide to the \<^verbatim>\<open>scholarly_paper\<close> Ontology\<close>
text\<open> In this section we give a minimal overview of the ontology formalized in
      \<^theory>\<open>Isabelle_DOF.scholarly_paper\<close>.\<close>

text\<open>  We start by modeling the usual text-elements of an academic paper: the title and author 
  information, abstract, and text section: 
@{boxed_theory_text [display]
\<open>doc_class title =
   short_title :: "string option"  <=  "None"
    
doc_class subtitle =
   abbrev ::      "string option"   <=  "None"
   
doc_class author =
   email       :: "string" <= "''''"
   http_site   :: "string" <= "''''"
   orcid       :: "string" <= "''''"
   affiliation :: "string"

doc_class abstract =
   keywordlist        :: "string list"   <= "[]" 
   principal_theorems :: "thm list"\<close>}
\<close>

text\<open>Note \<^const>\<open>short_title\<close> and \<^const>\<open>abbrev\<close> are optional and have the default\<^const>\<open>None\<close>
(no value). Note further, that \<^typ>\<open>abstract\<close>s may have a \<^const>\<open>principal_theorems\<close> list, where
the built-in \<^isadof> type \<^typ>\<open>thm list\<close> contains references to formally proven theorems that must
exist in the logical context of this document; this is a decisive feature of \<^isadof> that
conventional ontological languages lack.\<close>
find_consts name:"level"
text\<open>We continue by the introduction of a main class: the text-element \<^typ>\<open>text_section\<close>
(in contrast to \<^typ>\<open>figure\<close> or \<open>table\<close> or similar). Note that
the \<^const>\<open>main_author\<close> is typed with the class \<^typ>\<open>author\<close>, a HOL type that is automatically
derived from the document class definition \<^typ>\<open>author\<close> shown above. It is used to express which
author currently ``owns'' this \<^typ>\<open>text_section\<close>, an information that can give rise to
presentational or even access-control features in a suitably adapted front-end.
 
@{boxed_theory_text [display] \<open>
doc_class text_section = text_element +
   main_author :: "author option"  <=  None
   fixme_list  :: "string list"    <=  "[]" 
   level       :: "int  option"    <=  "None"
\<close>}

The \<^const>\<open>Isa_COL.text_element.level\<close>-attibute \<^index>\<open>level\<close> enables doc-notation support for
headers, chapters, sections, and subsections; we follow here the \<^LaTeX> terminology on levels to which \<^isadof> is currently targeting at.
The values are interpreted accordingly to the \<^LaTeX> standard. The correspondence between the levels
and the structural entities is summarized as follows:

   \<^item> part          \<^index>\<open>part\<close>          \<open>Some -1\<close> \vspace{-0.3cm}
   \<^item> chapter       \<^index>\<open>chapter\<close>       \<open>Some 0\<close>  \vspace{-0.3cm}
   \<^item> section       \<^index>\<open>section\<close>       \<open>Some 1\<close>  \vspace{-0.3cm}
   \<^item> subsection    \<^index>\<open>subsection\<close>    \<open>Some 2\<close>  \vspace{-0.3cm}
   \<^item> subsubsection \<^index>\<open>subsubsection\<close> \<open>Some 3\<close>  \vspace{-0.1cm}

Additional means assure that the following invariant is maintained in a document 
conforming to \<^verbatim>\<open>scholarly_paper\<close>:

\center {\<open>level > 0\<close>}
\<close>

text\<open> The rest of the ontology introduces concepts for \<^typ>\<open>introduction\<close>, \<^typ>\<open>conclusion\<close>,
\<^typ>\<open>related_work\<close>, \<^typ>\<open>bibliography\<close> etc. More details can be found in \<^verbatim>\<open>scholarly_paper\<close>
contained ion the theory \<^theory>\<open>Isabelle_DOF.scholarly_paper\<close>. \<close>

subsection\<open>Writing Academic Publications: A Freeform Mathematics Text \<close>
text*[csp_paper_synthesis::technical, main_author = "Some bu"]\<open>We present a typical mathematical
paper focussing on its form, not refering in any sense to its content which is out of scope here.
As mentioned before, we chose the paper~@{cite "taha.ea:philosophers:2020"} for this purpose,
which is written in the so-called free-form style: Formulas are superficially parsed and 
type-setted, but no deeper type-checking and checking with the underlying logical context
is undertaken. \<close>

figure*[fig0::figure,spawn_columns=False,relative_width="90",src="''figures/header_CSP_source.png''"]
       \<open> A mathematics paper as integrated document source ... \<close>  

figure*[fig0B::figure,spawn_columns=False,relative_width="90",src="''figures/header_CSP_pdf.png''"]
       \<open> ... and as corresponding \<^pdf>-output. \<close>  

text\<open>The integrated source of this paper-excerpt is shown in \<^figure>\<open>fig0\<close>, while the
document build process converts this to the corresponding \<^pdf>-output shown in \<^figure>\<open>fig0B\<close>.\<close>


text\<open>Recall that the standard syntax for a text-element in \<^isadof> is 
\<^theory_text>\<open>text*[<id>::<class_id>,<attrs>]\<open> ... text ...\<close>\<close>, but there are a few built-in abbreviations like
\<^theory_text>\<open>title*[<id>,<attrs>]\<open> ... text ...\<close>\<close> that provide special command-level syntax for text-elements. 
The other text-elements provide the authors and the abstract as specified by their class-id referring
to the \<^theory_text>\<open>doc_class\<close>es of \<^verbatim>\<open>scholarly_paper\<close>; we say that these text elements are \<^emph>\<open>instances\<close> 
\<^bindex>\<open>instance\<close> of the \<^theory_text>\<open>doc_class\<close>es \<^bindex>\<open>doc\_class\<close> of the underlying ontology. \<close>

text\<open>The paper proceeds by providing instances for introduction, technical sections, 
examples, \<^etc>. We would like to concentrate on one --- mathematical paper oriented --- detail in the 
ontology \<^verbatim>\<open>scholarly_paper\<close>: 

@{boxed_theory_text [display]
\<open>doc_class technical = text_section +  ...

type_synonym tc = technical (* technical content *)

datatype math_content_class = "defn" | "axm" | "thm"  | "lem" | "cor" | "prop" | ...
                           
doc_class math_content = tc +   ...

doc_class "definition"  = math_content +
   mcc           :: "math_content_class" <= "defn"  ...

doc_class "theorem"     = math_content +
   mcc           :: "math_content_class" <= "thm"   ... 
\<close>}\<close>


text\<open>The class \<^verbatim>\<open>technical\<close> regroups a number of text-elements that contain typical 
``technical content" in mathematical or engineering papers: code, definitions, theorems, 
lemmas, examples. From this class, the more stricter class of @{typ \<open>math_content\<close>} is derived,
which is grouped into @{typ "definition"}s and @{typ "theorem"}s (the details of these
class definitions are omitted here). Note, however, that class identifiers can be abbreviated by 
standard \<^theory_text>\<open>type_synonym\<close>s for convenience and enumeration types can be defined by the 
standard inductive \<^theory_text>\<open>datatype\<close> definition mechanism in Isabelle, since any HOL type is admitted
for attribute declarations. Vice-versa, document class definitions imply a corresponding HOL type 
definition. \<close>

figure*[fig01::figure,spawn_columns=False,relative_width="95",src="''figures/definition-use-CSP.png''"]
       \<open> A screenshot of the integrated source with definitions ...\<close>  
text\<open>An example for a sequence of (Isabelle-formula-)texts, their ontological declarations as 
\<^typ>\<open>definition\<close>s in terms of the \<^verbatim>\<open>scholarly_paper\<close>-ontology and their type-conform referencing 
later is shown in \<^figure>\<open>fig01\<close> in its presentation as the integrated source.

Note that the use in the ontology-generated antiquotation \<^theory_text>\<open>@{definition X4}\<close>
is type-checked; referencing \<^verbatim>\<open>X4\<close> as \<^theory_text>\<open>theorem\<close> would be a type-error and be reported directly
by \<^isadof> in Isabelle/jEdit. Note further, that if referenced correctly wrt. the sub-typing 
hierarchy makes \<^verbatim>\<open>X4\<close> \<^emph>\<open>navigable\<close> in Isabelle/jEdit; a click will cause the IDE to present the 
defining occurrence of this text-element in the integrated source.

% TODO:
% The definition \<^theory_text>\<open>@{definition X4}\<close> is not present in the screenshot,
% it might be better to use  \<^theory_text>\<open>@{definition X22}\<close>.

Note, further, how \<^isadof>-commands like \<^theory_text>\<open>text*\<close> interact with standard Isabelle document
antiquotations described in the Isabelle Isar Reference Manual in Chapter 4.2 in great detail. 
We refrain ourselves here to briefly describe three freeform antiquotations used in this text:

\<^item>  the freeform term antiquotation, also called \<^emph>\<open>cartouche\<close>, written by
   \<open>@{cartouche [style-parms] \<open>...\<close>}\<close> or just by \<open>\<open>...\<close>\<close> if the list of style parameters
   is empty,
\<^item>  the freeform antiquotation for theory fragments written \<open>@{theory_text [style-parms] \<open>...\<close>}\<close>
   or just \<^verbatim>\<open>\<^theory_text>\<close>\<open>\<open>...\<close>\<close> if the list of style parameters is empty,  
\<^item>  the freeform antiquotations for verbatim, emphasized, bold, or footnote text elements.
\<close>

figure*[fig02::figure,spawn_columns=False,relative_width="95",src="''figures/definition-use-CSP-pdf.png''"]
       \<open> ... and the corresponding pdf-oputput.\<close>  

text\<open>
\<^isadof> text-elements such as \<^theory_text>\<open>text*\<close> allow to have such standard term-antiquotations inside their
text, permitting to give the whole text entity a formal, referentiable status with typed
meta-information attached to it that may be used for presentation issues, search,
or other technical purposes.
The corresponding output of this snippet in the integrated source is shown in \<^figure>\<open>fig02\<close>. 
\<close>


subsection*[scholar_pide::example]\<open>More Freeform Elements, and Resulting Navigation\<close>
text\<open> In the following, we present some other text-elements provided by the Common Ontology Library
in @{theory "Isabelle_DOF.Isa_COL"}. It provides a document class for figures:

@{boxed_theory_text [display]\<open>
datatype placement = h | t | b | ht | hb   
doc_class figure   = text_section +
   relative_width  :: "int" (* percent of textwidth *)    
   src             :: "string"
   placement       :: placement 
   spawn_columns   :: bool <= True 
\<close>}
\<close>
figure*[fig_figures::figure,spawn_columns=False,relative_width="85",src="''figures/Dogfood-figures''"]
       \<open> Declaring figures in the integrated source.\<close>

text\<open> 
  The document class \<^typ>\<open>figure\<close> (supported by the \<^isadof> command abbreviation
  \<^boxed_theory_text>\<open>figure*\<close>) makes it possible to express the pictures and diagrams 
  as shown in \<^figure>\<open>fig_figures\<close>, which presents its own representation in the 
  integrated source as screenshot.\<close>

text\<open>
  Finally, we define a \<^emph>\<open>monitor class\<close> \<^index>\<open>monitor class\<close> that enforces a textual ordering
  in the document core by a regular expression:

  @{boxed_theory_text [display]\<open>
  doc_class article = 
     style_id :: string                <= "''LNCS''"
     version  :: "(int \<times> int \<times> int)"  <= "(0,0,0)"
     accepts "(title ~~ \<lbrakk>subtitle\<rbrakk> ~~ \<lbrace>author\<rbrace>\<^sup>+ ~~ abstract ~~ \<lbrace>introduction\<rbrace>\<^sup>+
                   ~~ \<lbrace>background\<rbrace>\<^sup>* ~~ \<lbrace>technical || example \<rbrace>\<^sup>+ ~~ \<lbrace>conclusion\<rbrace>\<^sup>+
                   ~~ bibliography ~~ \<lbrace>annex\<rbrace>\<^sup>* )"
  \<close>}\<close>

text\<open>
  In a integrated document source, the body of the content can be paranthesized into:

  @{boxed_theory_text [display]\<open>
  open_monitor* [this::article] 
  ...
  close_monitor*[this]
  \<close>} 

which signals to \<^isadof> begin and end of the part of the integrated source 
in which the text-elements instances are expected to appear in the textual ordering 
defined by \<^typ>\<open>article\<close>.
\<close>


side_by_side_figure*[exploring::side_by_side_figure,anchor="''fig-Dogfood-II-bgnd1''",
                      caption="''Exploring a reference of a text-element.''",relative_width="48",
                      src="''figures/Dogfood-II-bgnd1''",anchor2="''fig-bgnd-text_section''",
                      caption2="''Exploring the class of a text element.''",relative_width2="47",
                      src2="''figures/Dogfood-III-bgnd-text_section''"]\<open>Exploring text elements.\<close>


side_by_side_figure*["hyperlinks"::side_by_side_figure,anchor="''fig:Dogfood-IV-jumpInDocCLass''",
                      caption="''Hyperlink to class-definition.''",relative_width="48",
                      src="''figures/Dogfood-IV-jumpInDocCLass''",anchor2="''fig:Dogfood-V-attribute''",
                      caption2="''Exploring an attribute.''",relative_width2="47",
                      src2="''figures/Dogfood-V-attribute''"]\<open>Navigation via generated hyperlinks.\<close>
text\<open> 
  From these class definitions, \<^isadof> also automatically generated editing 
  support for Isabelle/jEdit. In \autoref{fig-Dogfood-II-bgnd1} and 
  \autoref{fig-bgnd-text_section} we show how hovering over links permits to explore its 
  meta-information. Clicking on a document class identifier permits to hyperlink into the 
  corresponding class definition (\autoref{fig:Dogfood-IV-jumpInDocCLass}); hovering over an 
  attribute-definition (which is qualified in order to disambiguate; 
  \autoref{fig:Dogfood-V-attribute}) shows its type.
\<close>

figure*[figDogfoodVIlinkappl::figure,relative_width="80",src="''figures/Dogfood-V-attribute''"]
       \<open> Exploring an attribute (hyperlinked to the class). \<close> 

text\<open> 
An ontological reference application in @{figure "figDogfoodVIlinkappl"}: the 
ontology-dependant antiquotation \<^boxed_theory_text>\<open>@{example ...}\<close> refers to the corresponding 
text-elements. Hovering allows for inspection, clicking for jumping to the definition.  If the 
link does not exist or  has a non-compatible type, the text is not validated,\<^ie>, Isabelle/jEdit
will respond with an error.\<close>

section*[cenelec_onto::example]\<open>Writing Certification Documents (CENELEC\_50128)\<close>
subsection\<open>The CENELEC 50128 Example\<close>
text\<open> 
  The ontology ``CENELEC\_50128''\index{ontology!CENELEC\_50128} is a small ontology modeling 
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
  \<^item>   can build the PDF-document by calling:
@{boxed_bash [display]\<open>ë\prompt{}ë isabelle build mini_odo \<close>}
\<close>
 
subsection\<open>Modeling CENELEC 50128\<close>
text\<open>
  Documents to be provided in formal certifications (such as CENELEC 
  50128~@{cite "boulanger:cenelec-50128:2015"} or Common Criteria~@{cite "cc:cc-part3:2006"}) can 
  much profit from the control of ontological consistency:  a substantial amount of the work
  of evaluators in formal certification processes consists in  tracing down the links from 
  requirements over assumptions down to elements of evidence, be it in form of semi-formal 
  documentation, models, code, or  tests.  In a certification process, traceability becomes a major 
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

doc_class requirement_analysis = no :: "nat"
   where "requirement_item +"
(*
% TODO:
% Update to the new implementation.
% where is deprecated and the new implementation uses accepts and rejects. 
*)
doc_class hypothesis = requirement +
      hyp_type :: hyp_type <= physical  (* default *)
  
datatype ass_kind = informal | semiformal | formal
  
doc_class assumption = requirement +
     assumption_kind :: ass_kind <= informal 
\<close>}

Such ontologies can be enriched by larger explanations and examples, which may help
the team of engineers substantially when developing the central document for a certification, 
like an explication of what is precisely the difference between an \<^emph>\<open>hypothesis\<close> and an 
\<^emph>\<open>assumption\<close> in the context of the evaluation standard. Since the PIDE makes for each 
document class its definition available by a simple mouse-click, this kind on meta-knowledge 
can be made far more accessible during the document evolution.

For example, the term of category \<^emph>\<open>assumption\<close> is used for domain-specific assumptions. 
It has formal, semi-formal and informal sub-categories. They have to be 
tracked and discharged by appropriate validation procedures within a 
certification process, be it by test or proof. It is different from a hypothesis, which is
globally assumed and accepted.

In the sequel, the category \<^emph>\<open>exported constraint\<close> (or \<^emph>\<open>ec\<close> for short)
is used for formal assumptions, that arise during the analysis,
design or implementation and have to be tracked till the final
evaluation target, and discharged by appropriate validation procedures 
within the certification process, be it by test or proof.  A particular class of interest 
is the category \<^emph>\<open>safety related application condition\<close> (or \<^emph>\<open>SRAC\<close> 
for short) which is used for \<^emph>\<open>ec\<close>'s that establish safety properties
of the evaluation target. Their traceability throughout the certification
is therefore particularly critical. This is naturally modeled as follows:
@{boxed_theory_text [display]\<open>  
doc_class ec = assumption  +
     assumption_kind :: ass_kind <= (*default *) formal
                        
doc_class SRAC = ec  +
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

This will be shown in the PDF as follows:
\<close>
text*[ass123::SRAC] \<open> The overall sampling frequence of the odometer
subsystem is therefore 14 khz, which includes sampling, computing and
result communication times \ldots \<close>

text\<open>Note that this pdf-output is the result of a specific setup for "SRAC"s.\<close>

subsection*[ontopide::technical]\<open>Editing Support for CENELEC 50128\<close>  
figure*[figfig3::figure,relative_width="95",src="''figures/antiquotations-PIDE''"]
\<open> Standard antiquotations referring to theory elements.\<close>
text\<open> The corresponding view in @{docitem  \<open>figfig3\<close>} shows core part of a document 
conforming to the CENELEC 50128 ontology. The first sample shows standard Isabelle antiquotations 
@{cite "wenzel:isabelle-isar:2020"} into formal entities of a theory. This way, the informal parts 
of a document get ``formal content'' and become more robust under change.\<close>

figure*[figfig5::figure, relative_width="95", src="''figures/srac-definition''"]
        \<open> Defining a "SRAC" in the integrated source \ldots \<close>
text\<open>
TODO:
The screenshot (figures/srac-definition) of the figure figfig5 should be updated
to have a SRAC type in uppercase.
\<close>

figure*[figfig7::figure, relative_width="95", src="''figures/srac-as-es-application''"]
        \<open> Using a "SRAC" as "EC" document element. \<close>
text\<open> The subsequent sample in @{figure \<open>figfig5\<close>} shows the definition of an
\<^emph>\<open>safety-related application condition\<close>, a side-condition of a theorem which 
has the consequence that a certain calculation must be executed sufficiently fast on an embedded 
device. This condition can not be established inside the formal theory but has to be 
checked by system integration tests. Now we reference in @{figure  \<open>figfig7\<close>} this 
safety-related condition; however, this happens in a context where general \<^emph>\<open>exported constraints\<close> 
are listed. \<^isadof>'s checks establish that this is legal in the given ontology. 
\<close>    


section*[tech_onto::example]\<open>Writing Technical Reports in \<^boxed_theory_text>\<open>technical_report\<close>\<close>  
text\<open>While it is perfectly possible to write documents in the
\<^boxed_theory_text>\<open>technical_report\<close> ontology in freeform-style (the present manual is mostly an
example for this category), we will briefly explain here the tight-checking-style in which
most Isabelle reference manuals themselves are written. 

The idea has already been put forward by Isabelle itself; besides the general infrastructure on 
which this work is also based, current Isabelle versions provide around 20 built-in 
document and code antiquotations described in the Reference Manual pp.75 ff. in great detail.

Most of them provide strict-checking, \<^ie> the argument strings where parsed and machine-checked in the
underlying logical context, which turns the arguments into \<^emph>\<open>formal content\<close> in the integrated
source, in contrast to the free-form antiquotations which basically influence the presentation.

We still mention a few of these document antiquotations here:
\<^item> \<^theory_text>\<open>@{thm \<open>refl\<close>}\<close> or \<^theory_text>\<open>@{thm [display] \<open>refl\<close>}\<close> check that \<^theory_text>\<open>refl\<close> is indeed a reference
  to a theorem; the additional "style" argument changes the presentation by printing the 
  formula into the output instead of the reference itself,
\<^item> \<^theory_text>\<open>@{lemma \<open>prop\<close> } by \<open>method\<close>\<close> allows to derive \<open>prop\<close> on the fly, thus garantee 
  that it is a corrollary of the current context,
\<^item> \<^theory_text>\<open>@{term \<open>term\<close> }\<close> parses and type-checks \<open>term\<close>,
\<^item> \<^theory_text>\<open>@{value \<open>term\<close> }\<close> performs the evaluation of \<open>term\<close>,
\<^item> \<^theory_text>\<open>@{ML \<open>ml-term\<close> }\<close> parses and type-checks \<open>ml-term\<close>,
\<^item> \<^theory_text>\<open>@{ML_file \<open>ml-file\<close> }\<close> parses the path for \<open>ml-file\<close> and
  verifies its existance in the (Isabelle-virtual) file-system.
\<close>
text\<open>There are options to display sub-parts of formulas etc., but it is a consequence
of tight-checking that the information must be given complete and exactly in the syntax of
Isabelle. This may be over-precise and a burden to readers not familiar with Isabelle, which may
motivate authors to choose the aforementioned freeform-style.
\<close>

subsection\<open>A Technical Report with Tight Checking\<close>
text\<open>An example of tight checking is a small programming manual developed by the
second author in order to document programming trick discoveries while implementing in Isabelle.
While not necessarily a meeting standards of a scientific text, it appears to us that this information
is often missing in the Isabelle community. 

So, if this text addresses only a very limited audience and will never be famous for its style,
it is nevertheless important to be \<^emph>\<open>exact\<close> in the sense that code-snippets and interface descriptions
should be accurate with the most recent version of Isabelle in which this document is generated.
So its value is that readers can just reuse some of these snippets and adapt them to their 
purposes.
\<close>

figure*[strict_SS::figure, relative_width="95", src="''figures/MyCommentedIsabelle.png''"] 
\<open>A table with a number of SML functions, together with their type.\<close>

text\<open>
\<open>TR_MyCommentedIsabelle\<close> is written according to the @{theory "Isabelle_DOF.technical_report"}
ontology. \<^figure>\<open>strict_SS\<close> shows a snippet from this integrated source and gives an idea why 
its tight-checking allows for keeping track of underlying Isabelle changes:
Any reference to an SML operation in some library module is type-checked, and the displayed
SML-type really corresponds to the type of the operations in the underlying SML environment.
In the pdf output, these text-fragments were displayed verbatim.
\<close>



section\<open>Style Guide\<close>
text\<open>
  The document generation of \<^isadof> is based on Isabelle's document generation framework, 
  using \<^LaTeX>{} as the underlying back-end. As Isabelle's document generation framework, it is 
  possible to embed (nearly) arbitrary \<^LaTeX>-commands in text-commands, \<^eg>:

@{boxed_theory_text [display]\<open>
text\<open> This is \emph{emphasized} and this is a 
       citation~\cite{brucker.ea:isabelle-ontologies:2018}\<close>
\<close>}

  In general, we advise against this practice and, whenever positive, use the \<^isadof> (respetively
  Isabelle) provided alternatives:

@{boxed_theory_text [display]\<open>
text\<open> This is *\<open>emphasized\<close> and this is a 
        citation @{cite "brucker.ea:isabelle-ontologies:2018"}.\<close>
\<close>}

Clearly, this is not always possible and, in fact, often \<^isadof> documents will contain 
\<^LaTeX>-commands, this should be restricted to layout improvements that otherwise are (currently)
not possible. As far as possible, the use of \<^LaTeX>-commands should be restricted to the definition 
of ontologies and document templates (see @{docitem (unchecked) \<open>isadof_ontologies\<close>}).

Restricting the use of \<^LaTeX> has two advantages: first, \<^LaTeX> commands can circumvent the 
consistency checks of \<^isadof> and, hence, only if no \<^LaTeX> commands are used, \<^isadof> can 
ensure that a document that does not generate any error messages in Isabelle/jEdit also generated
a PDF document. Second, future version of \<^isadof> might support different targets for the 
document generation (\<^eg>, HTML) which, naturally, are only available to documents not using 
too complex native \<^LaTeX>-commands. 

Similarly, (unchecked) forward references should, if possible, be avoided, as they also might
create dangling references during the document generation that break the document generation.  

Finally, we recommend to use the @{command "check_doc_global"} command at the end of your 
document to check the global reference structure. 

\<close>

(*<*)
end
(*>*) 
  
