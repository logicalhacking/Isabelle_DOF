(*<*)
theory "presentation"
  imports "Isabelle_DOF.scholarly_paper"
 "Isabelle_DOF-Ontologies.document_templates"
begin

use_template "beamer-UNSUPPORTED"
use_ontology "scholarly_paper"

title*[tit::title]\<open>Example Presentation\<close>
                                  
author*[safouan,email="\<open>example@example.org\<close>",affiliation="\<open>Example Org\<close>"]\<open>Eliza Example\<close>
(*>*)

text\<open>
\begin{frame}
\frametitle{Example Slide}
\centering\huge This is an example!
\end{frame}
\<close>

(*<*)
end 
(*>*)
