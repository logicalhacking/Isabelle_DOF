theory 
  COL_Test
imports 
  "Isabelle_DOF_Unit_Tests_document"
begin


print_doc_items
print_doc_classes

section\<open>General Heading COL Elements\<close> 

chapter*[S1::"chapter"]\<open>Chapter\<close>
text*[S1'::"chapter"]\<open>Chapter\<close>

section*[S2::"section"]\<open>Section\<close>
text*[S2'::"section"]\<open>Section\<close>

subsection*[S3::"subsection"]\<open>Subsection\<close>
text*[S3'::"subsection"]\<open>Subsection\<close>

subsubsection*[S4::"subsubsection"]\<open>Subsubsection\<close>
text*[S4'::"subsubsection"]\<open>Subsubsection\<close>

paragraph*[S5::"paragraph"]\<open>PAragraph\<close>
text*[S5'::"paragraph"]\<open>Paragraph\<close>


section\<open>General Figure COL Elements\<close> 

figure*[fig1_test,relative_width="95",file_src="''figures/A.png''"]
       \<open> This is the label text  \<^term>\<open>\<sigma>\<^sub>i+2\<close> \<close>  

(*<*)
text*[fig2_test::figure, relative_width="95",file_src="''figures/A.png''"
]\<open> This is the label text\<close>
(*>*)
text\<open>check @{figure fig1_test} cmp to @{figure fig2_test}\<close>



(* And a side-chick ... *)

text*[inlinefig::float, 
      main_caption="\<open>The Caption.\<close>"]
     \<open>@{theory_text [display, margin = 5] \<open>lemma A :: "a \<longrightarrow> b"\<close>}\<close>

text*[dupl_graphics::float, 
      main_caption="\<open>The Caption.\<close>"]
\<open>
@{fig_content (width=40, height=35, caption="This is a left test") "figures/A.png"
}\<^hfill>@{fig_content (width=40, height=35, caption="This is a right \<^term>\<open>\<sigma>\<^sub>i + 1\<close> test") "figures/B.png"} 
\<close>



end
(*>*)

