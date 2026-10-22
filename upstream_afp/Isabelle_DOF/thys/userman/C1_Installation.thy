(*<*)
theory
  "C1_Installation"
imports
  "C0_Introduction"
begin

(*>*)
chapter*[install::text_section]\<open>Getting Started\<close>

section*[installation::technical]\<open>Installation\<close>

text\<open>
  \<^isadof> is installed in three steps on top of a standard Isabelle installation. This manual
  refers to the following versions:
\<^gridtbl>\<open>
+-----------------+----------------------------------+------------------------------------------+
| Component       | Version                          | Where                                    |
+=================+==================================+==========================================+
| Isabelle        | Isabelle2026                     | isabelle.in.tum.de                       |
+-----------------+----------------------------------+------------------------------------------+
| AFP             | AFP for Isabelle2026             | isa-afp.org (contains the core of        |
|                 |                                  | Isabelle/DOF 2026)                       |
+-----------------+----------------------------------+------------------------------------------+
| \<^LaTeX>           | TeX Live 2022 or newer           | tug.org/texlive, or your OS              |
|                 | (2026 recommended)               |                                          |
+-----------------+----------------------------------+------------------------------------------+
| Add-ons         | release matching your Isabelle   | zenodo.org, DOI 10.5281/zenodo.15274072  |
+-----------------+----------------------------------+------------------------------------------+
\<close>
  Older combinations of Isabelle and \<^isadof> are not supported, since both evolve together:
  always use the AFP and the add-ons that belong to your Isabelle release.
\<close>

paragraph\<open>Installing Isabelle\<close>
text\<open>
  Download and install Isabelle2026 from the Isabelle website (\<^url>\<open>https://isabelle.in.tum.de\<close>).
  After the installation, you should be able to call the \<^boxed_bash>\<open>isabelle\<close> tool on the command line:
  @{boxed_bash [display]\<open>ë\prompt{}ë isabelle version
Isabelle2026\<close>}
  Depending on your operating system and on whether Isabelle's \<^boxed_bash>\<open>bin\<close> directory is in your 
  \<^boxed_bash>\<open>PATH\<close>, you may have to invoke \<^boxed_bash>\<open>isabelle\<close> by its full path.
\<close>

paragraph\<open>Installing \<^TeXLive>\<close>
text\<open>
  \<^isadof> produces PDF documents via \<^LaTeX> (it uses \<^verbatim>\<open>lualatex\<close> and a number of packages), 
  so a recent \<^TeXLive> (2022 or newer; we use 2026) with all packages is required.
  On a Debian-based Linux system (\<^eg>, Ubuntu), the following command installs everything:
  @{boxed_bash [display]\<open>ë\prompt{}ë sudo apt-get install texlive-full\<close>}
  On other systems, use MacTeX, respectively the \<^TeXLive> installer, and update all packages.
  You can check the installation with:
  @{boxed_bash [display]\<open>ë\prompt{}ë lualatex --version\<close>}
\<close>

paragraph\<open>Installing \<^isadof>\<close>
text\<open>
  The core of \<^isadof> is part of the Archive of Formal Proofs (AFP). Download the AFP for 
  Isabelle2026 from the AFP website (\<^url>\<open>https://www.isa-afp.org/download/\<close>) and register it 
  with Isabelle. Once it has been extracted to \<^verbatim>\<open>/home/myself/afp\<close>, run:
  @{boxed_bash [display]\<open>ë\prompt{}ë isabelle components -u /home/myself/afp/thys\<close>}
  Check the installation by building the session \<^verbatim>\<open>Isabelle_DOF\<close> once; this takes a few minutes:
  @{boxed_bash [display]\<open>ë\prompt{}ë isabelle build -b Isabelle_DOF\<close>}
  From now on, a theory can use \<^isadof> by importing it, for example 
  \<^theory_text>\<open>imports Isabelle_DOF.technical_report\<close>, and be opened with 
  @{boxed_bash [display]\<open>ë\prompt{}ë isabelle jedit -l Isabelle_DOF MyDocument.thy\<close>}
\<close>

paragraph\<open>Installing the add-ons (optional)\<close>
text\<open>
  The AFP-version is complete for writing documents. In addition, a package of \<^emph>\<open>add-ons\<close> is 
  distributed via Zenodo (\<^cite>\<open>"zenodo:addon:2025"\<close>, record \<^url>\<open>https://zenodo.org/records/15274072\<close>): 
  further ontologies and document templates (the session \<^verbatim>\<open>Isabelle_DOF-Ontologies\<close>), more 
  example documents, and the tool \<^verbatim>\<open>dof_mkroot\<close>, which we use in the next section to start a 
  new document. Download the package that matches your Isabelle version.
\<close>


section*[newdoc::technical]\<open>Starting a new document\<close>

text\<open>
 After completing all necessary installations, the next step is to start a project of your own.
 A project is an Isabelle \<^emph>\<open>session\<close>: a directory with a \<^verbatim>\<open>ROOT\<close> file, some theory files 
 (the \<^verbatim>\<open>.thy\<close> files, which contain the text of your document) and, optionally, a \<^verbatim>\<open>document\<close> 
 directory with \<^LaTeX> material. There are three ways to set it up: with the tool \<^verbatim>\<open>dof_mkroot\<close> 
 of the add-ons (the most convenient one, next subsection), from a ready-made scaffold, or from scratch.
\<close>

subsection*[addon::technical]\<open>Creating A Basic Document Setup\<close>
text\<open>
 Unpack the add-ons, change into the extracted directory and register them (the same way as the AFP):
 @{boxed_bash [display]\<open>ë\prompt{}ë tar xf Isabelle_DOF-add_ons-2025.tgz
ë\prompt{}ë cd Isabelle_DOF-add_ons-2025
ë\prompt{}ë isabelle components -u .
ë\prompt{}ë isabelle build -b Isabelle_DOF-Ontologies\<close>}
 The last command compiles the additional ontologies once. Afterwards, the tool \<^verbatim>\<open>dof_mkroot\<close> 
 is available. It is the \<^isadof>-variant of Isabelle's \<^verbatim>\<open>mkroot\<close> and generates the beginning of a 
 new document directory. For example, the following command creates a scientific paper in a 
 directory \<^verbatim>\<open>MyPaper\<close>, using the ontology \<^verbatim>\<open>scholarly_paper\<close> and the KOMA-Script article class:
 @{boxed_bash [display]\<open>ë\prompt{}ë isabelle dof_mkroot -o scholarly_paper -t scrartcl MyPaper\<close>}
 Without options, you get a technical report (ontologies \<^verbatim>\<open>technical_report\<close> and 
 \<^verbatim>\<open>scholarly_paper\<close>, template \<^verbatim>\<open>scrreprt-modern\<close>). The options are:
\<^gridtbl>\<open>
+--------+--------------------------------------------+
| Option | Meaning                                    |
+========+============================================+
| -o     | ontologies, separated by blanks            |
+--------+--------------------------------------------+
| -t     | LaTeX template                             |
+--------+--------------------------------------------+
| -n     | session name (default: directory name)     |
+--------+--------------------------------------------+
| -q     | quiet mode                                 |
+--------+--------------------------------------------+
| -I     | initialise a Mercurial repository          |
+--------+--------------------------------------------+
\<close>
 The directory \<^verbatim>\<open>MyPaper\<close> now contains three files:
\<^latex>\<open>
\begin{center}
\begin{minipage}{.9\textwidth}\footnotesize
\dirtree{%
.1 MyPaper.
.2 ROOT\DTcomment{the session: parent, options, theories}.
.2 MyPaper.thy\DTcomment{the first theory: template and ontologies}.
.2 document.
.3 preamble.tex\DTcomment{your own \LaTeX{} packages and settings}.
}
\end{minipage}
\end{center}\<close>
 The theory \<^verbatim>\<open>MyPaper.thy\<close> is the place to start. It selects the \<^emph>\<open>template\<close>, which fixes the overall layout of the 
 PDF (page format, fonts, headings), and the \<^emph>\<open>ontologies\<close>, which provide the document 
 classes (\<^eg>, titles, authors, abstracts, definitions or theorems) that you can use in the text:
 @{boxed_theory_text [display]\<open>
theory
  "MyPaper"
imports
  "Isabelle_DOF-Ontologies.document_templates"
  Isabelle_DOF.scholarly_paper
begin

list_templates
use_template "scrartcl"
list_ontologies
use_ontology "scholarly_paper"

end\<close>}
 The commands \<^theory_text>\<open>list_templates\<close> and \<^theory_text>\<open>list_ontologies\<close> print the available choices in the output 
 panel of Isabelle/jEdit; they can be removed once your choice is made. You add your text after the 
 \<^theory_text>\<open>use_ontology\<close> command, for example a title and an author, as explained in the following chapters.
 To produce the PDF, build the session; the result is found in \<^verbatim>\<open>MyPaper/output\<close>:
 @{boxed_bash [display]\<open>ë\prompt{}ë isabelle build -D MyPaper\<close>}
 While you are writing, it is more convenient to work interactively; the parent of the generated 
 session is \<^verbatim>\<open>Isabelle_DOF-Ontologies\<close>, hence:
 @{boxed_bash [display]\<open>ë\prompt{}ë isabelle jedit -d MyPaper -l Isabelle_DOF-Ontologies MyPaper/MyPaper.thy\<close>}
 The directory \<^verbatim>\<open>output/document\<close> is a self-contained \<^LaTeX> project; if you adapt the preamble 
 or a template, you can re-run \<^LaTeX> directly there (\<^verbatim>\<open>lualatex root.tex\<close>) without the whole Isabelle 
 build. More details on the build and on documents templates can be found in the reference 
 manual \<^cite>\<open>"mwenzel:isaref:2025"\<close>, in particular on the technical infrastructure.
\<close>

subsection*[template::technical]\<open>Template folder\<close>
text\<open>
  A ready-made starting point is the scaffold in the Zenodo entry \<^cite>\<open>"zenodo:temp:2025"\<close>: download 
  the file \<^verbatim>\<open>Isabelle_DOF-Scaffold-2025.tgz\<close> and unpack it. It is an ordinary session with a 
  \<^verbatim>\<open>ROOT\<close> file, a first theory with a title and two authors for the ontology \<^verbatim>\<open>scholarly_paper\<close>, 
  and a \<^verbatim>\<open>document/preamble.tex\<close>, and it builds with \<^verbatim>\<open>isabelle build -D\<close>. It uses the version of 
  \<^isadof> of the AFP, so the add-ons are not needed for it. This is the quickest way to get a 
  document that you can adapt.
\<close>
  
subsection*[scratch::technical]\<open>From Scratch\<close>

text\<open>
 The second approach is to start from scratch, which requires additional time and patience. 
To begin with the basics, a PDF-generating project typically requires the following documents:
  \<^item> A "document" folder with a \<^LaTeX> file in it named \<^verbatim>\<open>preamble.tex\<close>
    , it does not need to have anything written in it. 
     @{boxed_latex [display] \<open>\<close>}
     This document allows you to specify certain requirements or include necessary
     packages in \<^LaTeX> for your document.  
     Overall, this folder is intended for adding personal \<^LaTeX> packages or
     storing images that need to be included in the document.\<close>

    (* The installation of isadof comes with such a folder*)
text\<open>
    This folder and it's documents are not necessary if you do not want \<^isadof> to generate a PDF.
\<close>
text\<open>
  \<^item> A \<^verbatim>\<open>ROOT\<close> file with the following structure:\<close>
text\<open>
\begin{config}{ROOT}
session Session_Name = Isabelle_DOF +
  options [document = pdf, document_output = "output", document_build = dof]
  theories [document = false]
    "A1"
    ...
    "AN"
  theories [document = true]
    "B1"
    ...
    "BM"
  document_files
    "preamble.tex"
\end{config}

 where the A files are '.thy' you don't want to include in your output document and the B files are
 those you do. These files are all machine checked during the build.\<close>
text\<open>
 If you were to organise you files into directories you would need to add a
   \<^verbatim>\<open>directories\<close> section and give their names, all files within those 
    directories would need to be addressed by its local path from the location of the 
   \<^verbatim>\<open>ROOT\<close> file.
\<close>
text\<open>
  \<^item> As many '.thy' files, each of which is called a theory, as you want.
    The first one should adhere to the following structure:
@{boxed_theory_text [display]
\<open>
theory
  "theory_name"
imports
  Isabelle_DOF.technical_report
begin
  use_template "scrreprt-modern"
  use_ontology "technical_report" and "scholarly_paper"
end
\<close>}
  The \<^verbatim>\<open>use_template\<close> defines the way the concepts in your paper are presented, their layouts while
  \<^verbatim>\<open>use_ontology\<close> decides what ontology to use within the theory's context. An ontology is the 
  definition of concepts, to decide it is used means that the concepts exists and can be used 
  within our new theory.
    

Every following theory may have the followings structure:
@{boxed_theory_text [display]
\<open>
theory
  "theory_name"
imports
  "previous_theory_name"
begin
end
\<close>}\<close>
text\<open>
 To gain a better understanding of how this would appear in a real paper, you can refer to the `.thy`
 files in the Reference Manual, located in the 'thys' folder of the \<^isadof> installation.

 The hierachy with which one needs to imports different theories is important in Isabelle. Chapter 5 
 of the reference manual has more details \<^cite>\<open>"mwenzel:isaref:2025"\<close>.
\<close>


(*<*)
end
(*>*)