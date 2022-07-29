(*<*)
theory "paper"
  imports "Isabelle_DOF.scholarly_paper"
begin

open_monitor*[this::article]

declare[[ strict_monitor_checking  = false]]
declare[[ Definition_default_class = "definition"]]
declare[[ Lemma_default_class      = "lemma"]]
declare[[ Theorem_default_class    = "theorem"]]

define_shortcut*  isabelle \<rightleftharpoons> \<open>Isabelle/HOL\<close>
                  isadof   \<rightleftharpoons> \<open>\isadof\<close>

(*>*)

(********************************************************)
(* TITLE ************************************************)
title*[tit::title]\<open>A UI-component Description and its conformance to the ARINC Standard\<close>

(**********************************************************)
(* AUTHORS ************************************************)
author*[idir,email="\<open>idir.aitsadoune@centralesupelec.fr\<close>",affiliation="\<open>LMF, CentraleSupelec, Université Paris-Saclay\<close>"]
\<open>Idir Ait-Sadoune\<close>
author*[nicolas,email="\<open>nicolas.meric@lri.fr\<close>",affiliation="\<open>LMF, Université Paris-Saclay\<close>"]
\<open>Nicolas Méric\<close>
author*[bu,email= "\<open>wolff@lri.fr\<close>",affiliation = "\<open>LMF, Université Paris-Saclay\<close>"]
\<open>Burkhart Wolff\<close>    

(***********************************************************)
(* ABSTRACT ************************************************)
abstract*[abs, keywordlist="[\<open>w1\<close>,\<open>w2\<close>,\<open>w3\<close>,\<open>w4\<close>]"]
\<open> We describe a new case-study in the domain of user-interfaces (UI) for safety-critical avionics systems.
  We use \<^isadof> designed to handle documents with both formal and informal in order
  to \<^emph>\<open>model\<close> the ontology of the relevant  ARINC 661 standard as well as the semi-formal 
  \<^emph>\<open>description\<close> for a concrete UI component. The purpose of the exercise is to demonstrate
  the conformance of the formal component model and its conformance to both the informal as
  well as semi-formal, ontologically modeled aspects of the standard.
  
  In particular, We show how ontological invariants can be linked to safety-properties 
  in the UI domain.
\<close>
text\<open>\<close>

(***************************************************************)
(* INTRODUCTION ************************************************)
section*[introheader::introduction,main_author="Some(@{docitem ''bu''}::author)"]
\<open> Introduction \<close>
text*[introtext::introduction]
\<open>
Our article should cover the following points:
- Isa_Dof framework and its features to annotate informal texts with formal concepts of ontologies.
- Checking the conformance of object instances with an ontology model in the context of ARINC 661 standard.
- Possibility of expressing invariants (the case of the propagation of the visible and enable properties 
between the root widget and the child widgets is to be treated)
- modelling of the UA Validation process.
\<close>

(***************************************************************)
(* BACKGROUND **************************************************)
section*[bgrnd::text_section,main_author="Some(@{docitem ''bu''}::author)"]
\<open> Background \<close>
text
\<open>
bla bla bla bla ...
\<close>

subsection*[isabelle::technical,main_author="Some(@{docitem ''bu''}::author)"]
\<open> The Isabelle System  \<close>
text
\<open>
bla bla bla bla ...
\<close>

subsection*[isadof::technical,main_author="Some(@{docitem ''bu''}::author)"]
\<open> The Isa_DOF Framework  \<close>
text
\<open>
bla bla bla bla ...
\<close>

(***************************************************************)
(* CASE STUDY **************************************************)
section*[arinc::example,main_author="Some(@{docitem ''bu''}::author)"]
\<open> Case study : ARINC 661 and Multi-Purpose Interactive Application (MPIA)\<close>
text
\<open>
bla bla bla bla ...
\<close>

subsection*[arincmod::text_section]
\<open> Modeling ARINC 661 in \<^isadof> \<close> 
text
\<open>
bla bla bla bla ...
\<close>

subsection*[mpiamod::text_section]
\<open> Checking MPIA conformance in \<^isadof> \<close> 
text
\<open>
bla bla bla bla ...
\<close>

subsection*[gendoc::text_section]
\<open> Document generation with \<^isadof> \<close> 
text
\<open>
bla bla bla bla ...
\<close>

(***************************************************************)
(* INVARIANTS **************************************************)
section*[inv::technical,main_author="Some(@{docitem ''bu''}::author)"]
\<open> Expressing Invariants in ISADOF\<close>
text
\<open>
bla bla bla bla ...
\<close>

(***************************************************************)
(* The UA Validation process. **********************************)
section*[validation::technical,main_author="Some(@{docitem ''bu''}::author)"]
\<open> The User Application (UA) Validation process \<close>
text
\<open>
bla bla bla bla ...
\<close>


(*************************************************************)
(* RELATED WORK ************************************************)
section*[related::conclusion,main_author="Some(@{docitem ''bu''}::author)"]
\<open>Related Work\<close>
text
\<open>
bla bla bla bla ...
\<close>

(*************************************************************)
(* CONCLUSION ************************************************)
section*[conclusion::conclusion,main_author="Some(@{docitem ''bu''}::author)"]
\<open>Conclusion\<close>
text
\<open>
Conclusion content
\<close>

(*<*)

close_monitor*[this]

end
(*>*) 