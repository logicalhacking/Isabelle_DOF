(*<*)
theory
  "C0_Introduction"
imports
  Isabelle_DOF.technical_report
  Isabelle_DOF.scholarly_paper
begin
          
use_template "scrreprt-modern"
use_ontology "technical_report" and "scholarly_paper"


(**
*this next section was taken from the reference manual 
*to allow to use the same shortcuts as well as the boxed example of code
**)

section\<open>Local Document Setup.\<close>
text\<open>Introducing document specific abbreviations and macros:\<close>

define_shortcut* dof     \<rightleftharpoons> \<open>\dof\<close>
                 isadof  \<rightleftharpoons> \<open>\isadof{}\<close>

define_shortcut* TeXLive \<rightleftharpoons> \<open>\TeXLive\<close>
                 BibTeX  \<rightleftharpoons> \<open>\BibTeX{}\<close> 
                 LaTeX   \<rightleftharpoons> \<open>\LaTeX{}\<close>
                 TeX     \<rightleftharpoons> \<open>\TeX{}\<close>
                 dofurl  \<rightleftharpoons> \<open>\dofurl\<close>
                 pdf     \<rightleftharpoons> \<open>PDF\<close>

text\<open>Note that these setups assume that the associated \<^LaTeX> macros 
     are defined, \<^eg>, in the document prelude. \<close>

define_macro* index     \<rightleftharpoons> \<open>\index{\<close> _ \<open>}\<close>
define_macro* bindex    \<rightleftharpoons> \<open>\bindex{\<close> _ \<open>}\<close>
define_macro* nolinkurl \<rightleftharpoons> \<open>\nolinkurl{\<close> _ \<open>}\<close>
define_macro* center    \<rightleftharpoons> \<open>\center{\<close> _ \<open>}\<close>
define_macro* ltxinline \<rightleftharpoons> \<open>\inlineltx|\<close> _ \<open>|\<close>

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

open_monitor*[this::report] 

(*A few of my own macros*)
define_macro* outmat \<rightleftharpoons> \<open>\begin{outmat}\<close> _ \<open>\end{outmat}\<close>
define_macro* isarbox \<rightleftharpoons> \<open>\begin{isarbox}\<close> _ \<open>\end{isarbox}\<close>
define_macro* isatext \<rightleftharpoons>  \<open>\begin{isabelle}\isakeywordONE{text}{\isacartoucheopen}\end{isabelle}\<close> _ \<open>\begin{isabelle}{\isacartoucheclose}\end{isabelle}\<close>
(*>*)

title*[title::title]         \<open>Isabelle/DOF\<close> 
subtitle*[subtitle::subtitle]\<open>User Manual\<close> 
author*[  mathi,
          email       ="\<open>mathilde.needham@universite-paris-saclay.fr\<close>",
          affiliation = "\<open>Université Paris-Saclay, Paris, France\<close>"]
\<open>Mathilde Needham\<close>

chapter*[intro::text_section]\<open>Introduction\<close>
text\<open>
\<^isadof> is a framework designed for writing structured documents that can seamlessly incorporate 
elements of Isabelle/HOL. It is suitable for authoring mathematical proofs, technical reports, and
 scientific papers.

This manual is intended for users of \<^isadof> who wish to use the framework for creating and editing
 such documents. If you are an ontology developer or working on \<^isadof> itself, we recommend consulting
 the Reference Manual(\<^cite>\<open>"brucker.ea:isabelledof:2025"\<close>), which provides a more detailed and technical
 overview of the system’s internal architecture and capabilities.
\<close>
paragraph\<open>Typographical Conventions\<close>
text\<open>In order to maintain a consistent and coherent style throughout the manuals for \<^isadof>, we
 will adopt the same typographical conventions used in the Reference Manual. Therefore we will use:
  \<^item> a light-blue background for input written in Isabelle’s Isar language, \<^eg>:
    @{boxed_theory_text[display]\<open>lemma refl: x=x by simp\<close>}
  \<^item> a green background for examples of generated document fragments (\<^ie>, PDF output):
    @{boxed_pdf[display]\<open>The axiom refl\<close>}
  \<^item> a yellow background for \<^LaTeX>-code:
    @{boxed_latex [display] \<open>\newcommand{\refl}{$x = x$}\<close>}
  \<^item> a grey background for shell scripts and interactive shell sessions:
    @{boxed_bash [display]\<open>ë\prompt{}ë ls
      CHANGELOG.md  CITATION  examples  install  LICENSE  README.md  ROOTS  src\<close>}
\<close>
(*<*)
end
(*>*)