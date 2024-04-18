(*<*)
theory
  "template-beamer-UNSUPPORTED"
imports
  "Isabelle_DOF-Ontologies.document_templates"
   Isabelle_DOF.scholarly_paper
begin

list_templates
use_template "beamer-UNSUPPORTED"
list_ontologies
use_ontology "scholarly_paper"
(*>*)

title* [tit::title]\<open>Formal Verification of Security Protocols\<close>
author*[alice, email       = "\<open>alice@example.com\<close>",
               affiliation = "\<open>Wonderland University\<close>"]\<open>Alice\<close>  
(* 
author*[bob,   email       = "\<open>bob@example.com\<close>",
               affiliation = "\<open>Wonderland University\<close>"]\<open>Bob\<close>  
*)

text\<open>
\begin{frame}
\frametitle{Example Slide}
\centering\huge This is an example!
\end{frame}
\<close>


frame*[test_frame
    , frametitle = \<open>\<open>\<open>Example Slide\<^sub>t\<^sub>e\<^sub>s\<^sub>t\<close> with items @{thm "HOL.refl"}\<close>\<close>
    , framesubtitle = "''Subtitle''"]
\<open>This is an example!
 \<^item> The term \<^term>\<open>refl\<close> is...
 \<^item> and the term encoding the title of this frame is \<^term_>\<open>frametitle @{frame \<open>test_frame\<close>}\<close>\<close>

frame*[test_frame2
    , frametitle = "''Example Slide''"
    , framesubtitle = \<open>\<open>\<open>Subtitle\<^sub>t\<^sub>e\<^sub>s\<^sub>t:\<close> the value of \<^term>\<open>(3::int) + 3\<close> is @{value "(3::int) + 3"}\<close>\<close>]
\<open>Test frame env \<^term>\<open>refl\<close>\<close>

frame*[test_frame3
    , options = "''allowframebreaks''"
    , frametitle = "''Example Slide with frame break''"
    , framesubtitle = \<open>\<open>\<open>Subtitle\<^sub>t\<^sub>e\<^sub>s\<^sub>t:\<close> the value of \<^term>\<open>(3::int) + 3\<close> is @{value "(3::int) + 3"}\<close>\<close>]
\<open>
 \<^item> The term \<^term>\<open>refl\<close> is...
 \<^item> and the term encoding the title of this frame is \<^term_>\<open>frametitle @{frame \<open>test_frame3\<close>}\<close>
 \<^item> The term \<^term>\<open>refl\<close> is...
 \<^item> The term \<^term>\<open>refl\<close> is...
 \<^item> The term \<^term>\<open>refl\<close> is...
 \<^item> The term \<^term>\<open>refl\<close> is...
 \<^item> The term \<^term>\<open>refl\<close> is...
 \<^item> The term \<^term>\<open>refl\<close> is...
 \<^item> The term \<^term>\<open>refl\<close> is...
 \<^item> The term \<^term>\<open>refl\<close> is...
 \<^item> The term \<^term>\<open>refl\<close> is...
 \<^item> The term \<^term>\<open>refl\<close> is...
 \<^item> The term \<^term>\<open>refl\<close> is...
 \<^item> The term \<^term>\<open>refl\<close> is...
 \<^item> The term \<^term>\<open>refl\<close> is...
 \<^item> The term \<^term>\<open>refl\<close> is...
 \<^item> The term \<^term>\<open>refl\<close> is...
 \<^item> The term \<^term>\<open>refl\<close> is...
 \<^item> The term \<^term>\<open>refl\<close> is...
 \<^item> The term \<^term>\<open>refl\<close> is...
\<close>

(*<*)
end 
(*>*)
