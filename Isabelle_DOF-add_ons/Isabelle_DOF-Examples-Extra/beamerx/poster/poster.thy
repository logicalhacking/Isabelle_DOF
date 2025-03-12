(*<*)
theory "poster"
  imports "Isabelle_DOF.scholarly_paper"
 "Isabelle_DOF-Ontologies.document_templates"
begin

use_template "beamerposter-UNSUPPORTED"
use_ontology "scholarly_paper"
(*>*)

title*[tit::title]\<open>Example Presentation\<close>
                                  
author*[safouan,email="\<open>example@example.org\<close>",affiliation="\<open>Example Org\<close>"]\<open>Eliza Example\<close>

text\<open>
    \vfill
    \begin{block}{\large Fontsizes}
      \centering
      {\tiny tiny}\par
      {\scriptsize scriptsize}\par
      {\footnotesize footnotesize}\par
      {\normalsize normalsize}\par
      {\large large}\par
      {\Large Large}\par
      {\LARGE LARGE}\par
      {\veryHuge veryHuge}\par
      {\VeryHuge VeryHuge}\par
      {\VERYHuge VERYHuge}\par
    \end{block}
    \vfill
\<close>

text\<open>
@{block (title = "\<open>Title\<^sub>t\<^sub>e\<^sub>s\<^sub>t\<close>") "\<open>Block content\<^sub>t\<^sub>e\<^sub>s\<^sub>t\<close>"}
\<close>

(*<*)
end 
(*>*)
