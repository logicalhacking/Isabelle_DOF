(*<*)
theory
  "C1_Installation"
imports
  "C0_Introduction"
begin

(*>*)
chapter*[install::text_section]\<open>Getting Started\<close>

section*[installation::technical]\<open>Installation \<close>

paragraph\<open>Installing Isabelle\<close>
text\<open>
  Firstly you will need to download and install the latest official Isabelle release from the Isabelle Website 
  (\<^url>\<open>https://isabelle.in.tum.de\<close>). After the successful installation of Isabelle, you should be 
  able to call the \<^boxed_bash>\<open>isabelle\<close> tool on the command line:
@{boxed_bash [display]\<open>ë\prompt{}ë isabelle version\<close>}

Depending on your operating system and depending if you put Isabelle's  \<^boxed_bash>\<open>bin\<close> directory
in your  \<^boxed_bash>\<open>PATH\<close>, you will need to invoke  \<^boxed_bash>\<open>isabelle\<close> using its
full qualified path.
\<close>

paragraph\<open>Installing \<^TeXLive>.\<close>
text\<open>
  Next you will need to install all the required \<^LaTeX> packages.
  On a Debian-based Linux system (\<^eg>, Ubuntu), the following command will do so:
@{boxed_bash [display]\<open>ë\prompt{}ë sudo apt-get install texlive-full\<close>}
\<close>

paragraph\<open>Installing \<^isadof>\<close>
text\<open>
  Finally you will want to download \<^isadof> from the AFP website. To do so you will need to install 
the full AFP (\<^url>\<open>https://www.isa-afp.org/download/\<close>). Once it has been extracted to \<^verbatim>\<open>/home/myself/afp\<close>
 you will need to run the following command:
@{boxed_bash [display]\<open>ë\prompt{}ë isabelle components -u /home/myself/afp/thys\<close>}
\<close>


section*[newdoc::technical]\<open>Starting a new document \<close>

text\<open>
After completing all necessary installations, the next step is to become more familiar with the language and learn how to use it to write machine-checked papers.
 When starting a new project, there are two primary approaches to consider. 
\<close>
subsection*[template::technical]\<open>Template folder\<close>
text\<open>
  The easiest was to do this is to download the file named "Isabelle\_DOF-Scaffold-2025.tg1" in the 
Zenodo entry \<^cite>\<open>"zenodo:temp:2025"\<close> and unpack it. This gives you a basic setup and is very quick. 
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
 those you do. This files are all machine checked during the build.\<close>
text\<open>
If you were to organise you files into directories you would need to add a
 \<^verbatim>\<open>directories\<close> section and give their names, all files within those 
directories would need to be adressed by it's local path from the location of the 
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
\<^verbatim>\<open>use_ontology\<close> decides what ontology to use within the theory's context. An ontology is the definition
of concepts, to decide it is used means that the concepts exists and can be used within our new theory.
    

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

subsection*[addon::technical]\<open>Add-on command\<close>
text\<open>
 Optionally you may also download the \<^isadof> add-on, which can be found at \<^cite>\<open>"zenodo:addon:2025"\<close>
This package includes an Isabelle command called \<^verbatim>\<open>dof_mkroot\<close> which generates the beginning of a new
document directory. There are different options to make it as specific as you would like. You can read more
on the subject in the README provided at \<^url>\<open>https://zenodo.org/records/15274072\<close> \<close>

(*<*)
end
(*>*)