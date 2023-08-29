(*<*)
theory "presentation"
  imports "Isabelle_DOF.scholarly_paper"
 "Isabelle_DOF-Ontologies.document_templates"
begin

use_template "beamer-UNSUPPORTED"
use_ontology "scholarly_paper"
(*>*)

title*[tit::title]\<open>Example Presentation\<close>
                                  
author*[safouan,email="\<open>example@example.org\<close>",affiliation="\<open>Example Org\<close>"]\<open>Eliza Example\<close>

text\<open>
\begin{frame}
\frametitle{Example Slide}
\centering\huge This is an example!
\end{frame}
\<close>

frame*[test_frame
    , frametitle = \<open>\<open>\<open>Example Slide\<^sub>t\<^sub>e\<^sub>s\<^sub>t\<close> @{thm "HOL.refl"}\<close>\<close>
    , framesubtitle = "''Subtitle''"]
\<open>This is an example!
 \<^item> The term \<^term>\<open>refl\<close> is...
 \<^item> and the term encoding the title of this frame is \<^term_>\<open>frametitle @{frame \<open>test_frame\<close>}\<close>\<close>

frame*[test_frame2
    , frametitle = "''Example Slide''"
    , framesubtitle = \<open>\<open>\<open>Subtitle\<^sub>t\<^sub>e\<^sub>s\<^sub>t:\<close> the value of \<^term>\<open>(3::int) + 3\<close> is @{value "(3::int) + 3"}\<close>\<close>]
\<open>Test frame env \<^term>\<open>refl\<close>\<close>

(*<*)
end 
(*>*)
