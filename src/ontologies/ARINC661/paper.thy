(*<*)
theory "paper"
  imports "Isabelle_DOF.scholarly_paper"
begin

open_monitor*[this::article]

declare[[ strict_monitor_checking  = false]]
declare[[ Definition_default_class = "definition"]]
declare[[ Lemma_default_class      = "lemma"]]
declare[[ Theorem_default_class    = "theorem"]]

define_shortcut* isabelle \<rightleftharpoons> \<open>Isabelle/HOL\<close>

(*>*)

title*[tit::title]\<open>New Title\<close>
                                  
author*[idir,email="\<open>idir.aitsadoune@centralesupelec.fr\<close>",affiliation="\<open>LMF, CentraleSupelec, Université Paris-Saclay\<close>"]
\<open>Idir Ait-Sadoune\<close>
author*[nicolas,email="\<open>nicolas.meric@lri.fr\<close>",affiliation="\<open>LMF, Université Paris-Saclay\<close>"]
\<open>Nicolas Méric\<close>
author*[bu,email= "\<open>wolff@lri.fr\<close>",affiliation = "\<open>LMF, Université Paris-Saclay\<close>"]
\<open>Burkhart Wolff\<close>    


abstract*[abs, keywordlist="[\<open>w1\<close>,\<open>w2\<close>,\<open>w3\<close>,\<open>w4\<close>]"]
\<open>  
Abstract content
\<close>
text\<open>\<close>


section*[introheader::introduction,main_author="Some(@{docitem ''bu''}::author)"]
\<open> Introduction \<close>
text*[introtext::introduction]
\<open>
Our article should cover the following points:
- ISA_DOF framework and its features to annotate informal texts with formal concepts of ontologies.
- Check the conformance of object instances with an ontology model.
- Possibility of expressing invariants (the case of the propagation of the visible and enable properties between the root widget and the child widgets is to be treated)
- modelling of the UA Validation process.
\<close>


(*<*)

close_monitor*[this]

end
(*>*) 